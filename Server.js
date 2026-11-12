const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");

const PORT = process.env.PORT || 3000;
const SECRET = process.env.AUTH_SECRET || crypto.randomBytes(32).toString("hex");
const ORIGINS = String(process.env.ALLOWED_ORIGINS || "")
  .split(",")
  .map((s) => s.trim().replace(/\/+$/, ""))
  .filter(Boolean);
const GOOGLE_CLIENT_ID = process.env.GOOGLE_CLIENT_ID || "";
const RESEND_API_KEY = process.env.RESEND_API_KEY || "";
const MAIL_FROM = process.env.MAIL_FROM || "BrainGain <onboarding@resend.dev>";
const ALLOW_DEMO = process.env.ALLOW_DEMO_LOGIN === "1";
const DEV_SHOW_CODE = process.env.DEV_SHOW_CODE === "1";
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, "data");
const DB_FILE = path.join(DATA_DIR, "braingain.json");

const GOOGLE_JWKS = "https://www.googleapis.com/oauth2/v3/certs";
const GOOGLE_ISSUERS = ["https://accounts.google.com", "accounts.google.com"];

const SESSION_MS = 7 * 24 * 3600 * 1000;
const CODE_TTL = 10 * 60 * 1000;
const RESEND_GAP = 30 * 1000;
const MAX_TRIES = 5;
const CLASS_CHARS = "ABCDEFGHJKMNPQRSTUVWXYZ23456789";
const RESERVED = new Set(["admin", "administrator", "root", "support", "braingain", "teacher", "educator", "student", "moderator", "system", "help"]);

let db = { users: {}, byProvider: {}, usernames: {}, classes: {}, byCode: {}, reviews: {}, scores: {} };
let saveTimer = 0;

function loadDb() {
  try {
    db = Object.assign(db, JSON.parse(fs.readFileSync(DB_FILE, "utf8")));
  } catch (e) {}
}

function flushDb() {
  clearTimeout(saveTimer);
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    fs.writeFileSync(DB_FILE + ".tmp", JSON.stringify(db));
    fs.renameSync(DB_FILE + ".tmp", DB_FILE);
  } catch (e) {
    console.error("[db] could not save: " + e.message);
  }
}

function saveDb() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(flushDb, 800);
}

class HttpError extends Error {
  constructor(code, message) {
    super(message);
    this.code = code;
  }
}

function fail(code, message) {
  throw new HttpError(code, message);
}

const rand = (n) => crypto.randomBytes(n).toString("hex");
const b64url = (buf) => Buffer.from(buf).toString("base64url");

function sign(obj) {
  const body = b64url(JSON.stringify(obj));
  return body + "." + crypto.createHmac("sha256", SECRET).update(body).digest("base64url");
}

function unsign(token) {
  if (typeof token !== "string" || token.length > 600) return null;
  const parts = token.split(".");
  if (parts.length !== 2) return null;
  const a = Buffer.from(parts[1]);
  const b = Buffer.from(crypto.createHmac("sha256", SECRET).update(parts[0]).digest("base64url"));
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  try {
    return JSON.parse(Buffer.from(parts[0], "base64url").toString());
  } catch (e) {
    return null;
  }
}

function sameText(a, b) {
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
}

const hashCode = (uid, code) => crypto.createHmac("sha256", SECRET).update(uid + ":" + code).digest("hex");

const buckets = new Map();

function limited(key, max, windowMs) {
  const now = Date.now();
  let b = buckets.get(key);
  if (!b) {
    b = [];
    buckets.set(key, b);
  }
  while (b.length && now - b[0] > windowMs) b.shift();
  if (b.length >= max) return true;
  b.push(now);
  return false;
}

setInterval(() => {
  const now = Date.now();
  for (const [k, e] of emailLogins) if (now > e.exp) emailLogins.delete(k);
  for (const [k, b] of buckets) if (!b.length || now - b[b.length - 1] > 3600000) buckets.delete(k);
}, 60000).unref();

function clientIp(req) {
  const h = req.headers;
  let ip = h["cf-connecting-ip"] || h["true-client-ip"];
  if (!ip && h["x-forwarded-for"]) {
    const parts = String(h["x-forwarded-for"])
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);
    ip = parts.length >= 2 ? parts[parts.length - 2] : parts[0];
  }
  if (!ip) ip = req.socket.remoteAddress || "unknown";
  return String(ip).replace(/^::ffff:/, "").slice(0, 64);
}

function cleanName(raw, max) {
  return String(raw || "")
    .replace(/<[^>]*>/g, "")
    .replace(/[\u0000-\u001f\u007f<>]/g, "")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, max);
}

function cleanText(raw, max) {
  return String(raw || "")
    .replace(/[\u0000-\u001f\u007f]/g, " ")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, max);
}

const normAnswer = (s) =>
  String(s || "")
    .toLowerCase()
    .replace(/[^\p{L}\p{N}\s.\-]/gu, "")
    .replace(/\s+/g, " ")
    .trim();

function shortName(full) {
  const t = cleanName(full, 60).split(" ").filter(Boolean);
  if (!t.length) return "Student";
  if (t.length === 1) return t[0];
  return t[0] + " " + t[t.length - 1][0].toUpperCase() + ".";
}

function maskEmail(email) {
  const m = /^([^@]+)@(.+)$/.exec(String(email || ""));
  if (!m) return "";
  return m[1][0] + "***@" + m[2];
}

function publicUser(u) {
  return {
    id: u.id,
    name: u.name,
    email: maskEmail(u.email),
    needsEmail: !u.email,
    provider: u.provider,
    role: u.role,
    educator: u.educator ? { username: u.educator.username, displayName: u.educator.displayName, verified: true } : null,
    pending: u.pending ? { username: u.pending.username, displayName: u.pending.displayName, sentTo: maskEmail(u.pending.email), sentAt: u.pending.sentAt } : null
  };
}

const educatorLabel = (u) => (u.educator ? u.educator.displayName || u.educator.username : "Educator");

const jwksCache = new Map();

async function getKeys(url, force) {
  const hit = jwksCache.get(url);
  if (hit && !force && Date.now() - hit.at < 3600000) return hit.keys;
  const r = await fetch(url);
  if (!r.ok) throw new Error("keys");
  const j = await r.json();
  const keys = Array.isArray(j.keys) ? j.keys : [];
  jwksCache.set(url, { at: Date.now(), keys: keys });
  return keys;
}

async function verifyIdToken(token, opts) {
  const parts = token.split(".");
  if (parts.length !== 3 || token.length > 5000) throw new Error("format");
  const header = JSON.parse(Buffer.from(parts[0], "base64url").toString());
  const payload = JSON.parse(Buffer.from(parts[1], "base64url").toString());
  if (header.alg !== "RS256" || typeof header.kid !== "string") throw new Error("alg");
  let keys = await getKeys(opts.jwks, false);
  let jwk = keys.find((k) => k.kid === header.kid && k.kty === "RSA");
  if (!jwk) {
    keys = await getKeys(opts.jwks, true);
    jwk = keys.find((k) => k.kid === header.kid && k.kty === "RSA");
  }
  if (!jwk) throw new Error("kid");
  const key = crypto.createPublicKey({ key: jwk, format: "jwk" });
  const ok = crypto.verify("RSA-SHA256", Buffer.from(parts[0] + "." + parts[1]), key, Buffer.from(parts[2], "base64url"));
  if (!ok) throw new Error("signature");
  if (opts.issuers.indexOf(payload.iss) === -1) throw new Error("issuer");
  const aud = Array.isArray(payload.aud) ? payload.aud : [payload.aud];
  if (aud.indexOf(opts.audience) === -1) throw new Error("audience");
  const now = Date.now();
  if (!(payload.exp * 1000 > now - 60000)) throw new Error("expired");
  if (payload.iat && payload.iat * 1000 > now + 300000) throw new Error("future");
  if (typeof payload.sub !== "string" || !payload.sub) throw new Error("sub");
  return payload;
}

function prettyName(email) {
  const words = String(email).split("@")[0].replace(/[._+\-]+/g, " ").replace(/[0-9]+$/, "").trim().split(" ").filter(Boolean);
  const out = words.map((w) => w[0].toUpperCase() + w.slice(1)).join(" ").slice(0, 30);
  return out || "Student";
}

function signIn(provider, sub, name, email) {
  const key = provider + ":" + sub;
  let u = db.users[db.byProvider[key]];
  if (!u && email && provider !== "demo") {
    u = Object.values(db.users).find((x) => x.provider !== "demo" && x.email === email);
    if (u) db.byProvider[key] = u.id;
  }
  if (!u) {
    u = { id: rand(12), provider: provider, sub: sub, name: name || "Student", email: email || "", role: null, tv: 0, created: Date.now(), educator: null, pending: null };
    db.users[u.id] = u;
    db.byProvider[key] = u.id;
  } else {
    if (name && provider !== "email") u.name = name;
    if (email) u.email = email;
  }
  saveDb();
  return { token: sign({ uid: u.id, tv: u.tv, exp: Date.now() + SESSION_MS }), user: publicUser(u) };
}

async function authGoogle(c) {
  if (!GOOGLE_CLIENT_ID) fail(503, "Google sign-in isn't set up on the server yet.");
  let p;
  try {
    p = await verifyIdToken(String(c.body.credential || ""), { jwks: GOOGLE_JWKS, issuers: GOOGLE_ISSUERS, audience: GOOGLE_CLIENT_ID });
  } catch (e) {
    fail(401, "Google sign-in couldn't be verified. Please try again.");
  }
  const verified = p.email_verified === true || p.email_verified === "true";
  const email = verified ? String(p.email || "").toLowerCase().slice(0, 120) : "";
  const name = cleanName(p.name || p.given_name || (email && email.split("@")[0]), 60);
  return signIn("google", p.sub, name, email);
}

function authDemo(c) {
  if (!ALLOW_DEMO) fail(403, "Demo sign-in is turned off.");
  const name = cleanName(c.body.name, 40) || "Demo User";
  const slug = name.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "").slice(0, 30) || "demo";
  return signIn("demo", slug, name, slug + "@demo.test");
}

function setRole(c) {
  const role = c.body.role;
  const u = c.user;
  if (role !== "student" && role !== "educator") fail(400, "Pick Educator or Student.");
  if (u.educator && role !== "educator") fail(409, "This account is already an educator account.");
  u.role = role;
  if (role === "student") u.pending = null;
  saveDb();
  return { user: publicUser(u) };
}

const emailLogins = new Map();

function normEmail(raw) {
  const e = String(raw || "").trim().toLowerCase();
  return e.length > 120 || !/^[^\s@]{1,64}@[^\s@]{1,200}\.[^\s@]{2,}$/.test(e) ? "" : e;
}

async function sendMail(to, code, purpose) {
  const signin = purpose === "signin";
  const subject = signin ? "Your BrainGain sign-in code" : "Your BrainGain verification code";
  const intro = signin ? "Use this code to sign in to BrainGain:" : "Use this code to finish creating your educator account:";
  if (!RESEND_API_KEY) {
    if (DEV_SHOW_CODE) {
      console.log("[mail] testing mode: " + subject + " " + code + " for " + to);
      return;
    }
    throw new Error("mail-off");
  }
  const html =
    '<div style="font-family:Arial,sans-serif;max-width:420px;margin:auto;padding:24px;border:3px solid #1d2b53;border-radius:16px">' +
    '<h2 style="margin:0 0 8px;color:#1d2b53">BrainGain</h2>' +
    "<p>" + intro + "</p>" +
    '<p style="font-size:36px;letter-spacing:8px;font-weight:bold;margin:16px 0;color:#1d2b53">' +
    code +
    "</p>" +
    "<p>It works for 10 minutes. If you didn't ask for it, you can ignore this email.</p></div>";
  const r = await fetch("https://api.resend.com/emails", {
    method: "POST",
    headers: { Authorization: "Bearer " + RESEND_API_KEY, "Content-Type": "application/json" },
    body: JSON.stringify({ from: MAIL_FROM, to: [to], subject: subject, text: subject + " is " + code + ". It works for 10 minutes.", html: html })
  });
  if (!r.ok) throw new Error("mail-failed");
}

async function emailStart(c) {
  if (!RESEND_API_KEY && !DEV_SHOW_CODE) fail(503, "Email sign-in isn't set up on the server yet.");
  const email = normEmail(c.body.email);
  if (!email) fail(400, "Enter a real email address.");
  const now = Date.now();
  const prev = emailLogins.get(email);
  if (prev && now - prev.sentAt < RESEND_GAP) fail(429, "Wait a few seconds before asking for another code.");
  if (limited("emailsend:" + c.ip, 10, 3600000)) fail(429, "Too many codes asked for. Try again in an hour.");
  if (limited("emailaddr:" + email, 5, 3600000)) fail(429, "That's a lot of codes for one email. Try again in an hour.");
  const code = String(crypto.randomInt(100000, 1000000));
  const entry = { hash: hashCode("login:" + email, code), exp: now + CODE_TTL, tries: 0, sentAt: now, name: cleanName(c.body.name, 40) };
  try {
    await sendMail(email, code, "signin");
  } catch (e) {
    if (e.message === "mail-off") fail(503, "Email sign-in isn't set up on the server yet.");
    fail(502, "The email couldn't be sent. Please try again.");
  }
  emailLogins.set(email, entry);
  const out = { ok: true, sentTo: maskEmail(email) };
  if (DEV_SHOW_CODE) out.devCode = code;
  return out;
}

function emailVerify(c) {
  const email = normEmail(c.body.email);
  const entry = email ? emailLogins.get(email) : null;
  if (!entry) fail(400, "Ask for a sign-in code first.");
  if (Date.now() > entry.exp) {
    emailLogins.delete(email);
    fail(410, "That code expired. Ask for a new one.");
  }
  const code = String(c.body.code || "").replace(/\s/g, "");
  if (!/^[0-9]{6}$/.test(code)) fail(400, "The code is 6 numbers.");
  entry.tries++;
  if (!sameText(hashCode("login:" + email, code), entry.hash)) {
    if (entry.tries >= MAX_TRIES) {
      emailLogins.delete(email);
      fail(429, "Too many wrong codes. Please ask for a new one.");
    }
    fail(400, "That code isn't right. " + (MAX_TRIES - entry.tries) + " tries left.");
  }
  emailLogins.delete(email);
  return signIn("email", email, entry.name || prettyName(email), email);
}

async function issueCode(u, info) {
  const now = Date.now();
  if (u.pending && now - u.pending.sentAt < RESEND_GAP) fail(429, "Wait a few seconds before asking for another code.");
  if (limited("mail:" + u.id, 5, 3600000)) fail(429, "That's a lot of codes. Try again in an hour.");
  const code = String(crypto.randomInt(100000, 1000000));
  const prev = u.pending;
  u.pending = { username: info.username, displayName: info.displayName, email: info.email, hash: hashCode(u.id, code), exp: now + CODE_TTL, tries: 0, sentAt: now };
  try {
    await sendMail(info.email, code);
  } catch (e) {
    u.pending = prev || null;
    if (e.message === "mail-off") fail(503, "Email isn't set up on the server yet.");
    fail(502, "The email couldn't be sent. Please try again.");
  }
  saveDb();
  const out = { ok: true, sentTo: maskEmail(info.email), user: publicUser(u) };
  if (DEV_SHOW_CODE) out.devCode = code;
  return out;
}

async function educatorStart(c) {
  const u = c.user;
  if (u.role !== "educator") fail(400, "Choose Educator first.");
  if (u.educator) fail(409, "Your educator account is already set up.");
  const username = String(c.body.username || "").trim();
  if (!/^[A-Za-z0-9_]{3,20}$/.test(username)) fail(400, "Usernames are 3 to 20 letters, numbers or underscores.");
  const key = username.toLowerCase();
  if (RESERVED.has(key)) fail(400, "That username isn't available.");
  if (db.usernames[key] && db.usernames[key] !== u.id) fail(409, "That username is taken. Try another.");
  const displayName = cleanName(c.body.displayName, 30) || null;
  let email = u.email;
  if (!email) {
    email = String(c.body.email || "").trim().toLowerCase();
    if (email.length > 120 || !/^[^\s@]{1,64}@[^\s@]{1,200}\.[^\s@]{2,}$/.test(email)) fail(400, "Enter a real email address.");
  }
  return issueCode(u, { username: username, displayName: displayName, email: email });
}

async function educatorResend(c) {
  const u = c.user;
  if (!u.pending) fail(400, "Start the account setup first.");
  return issueCode(u, { username: u.pending.username, displayName: u.pending.displayName, email: u.pending.email });
}

function educatorVerify(c) {
  const u = c.user;
  const p = u.pending;
  if (!p) fail(400, "Ask for a verification code first.");
  if (Date.now() > p.exp) {
    u.pending = null;
    saveDb();
    fail(410, "That code expired. Ask for a new one.");
  }
  const code = String(c.body.code || "").replace(/\s/g, "");
  if (!/^[0-9]{6}$/.test(code)) fail(400, "The code is 6 numbers.");
  p.tries++;
  if (!sameText(hashCode(u.id, code), p.hash)) {
    if (p.tries >= MAX_TRIES) {
      u.pending = null;
      saveDb();
      fail(429, "Too many wrong codes. Please start again.");
    }
    saveDb();
    fail(400, "That code isn't right. " + (MAX_TRIES - p.tries) + " tries left.");
  }
  const key = p.username.toLowerCase();
  if (db.usernames[key] && db.usernames[key] !== u.id) {
    u.pending = null;
    saveDb();
    fail(409, "That username was just taken. Pick another.");
  }
  db.usernames[key] = u.id;
  u.educator = { username: p.username, displayName: p.displayName, email: p.email, verified: true, at: Date.now() };
  u.pending = null;
  u.role = "educator";
  saveDb();
  return { user: publicUser(u) };
}

function cleanQuestions(raw) {
  if (!Array.isArray(raw) || raw.length < 1) fail(400, "Add at least one question.");
  if (raw.length > 50) fail(400, "A review can have up to 50 questions.");
  return raw.map((q, i) => {
    const n = i + 1;
    if (!q || typeof q !== "object") fail(400, "Question " + n + " couldn't be read.");
    const text = cleanText(q.q, 200);
    if (text.length < 2) fail(400, "Question " + n + " needs some text.");
    if (q.t === "mc") {
      const options = Array.isArray(q.options) ? q.options.map((o) => cleanText(o, 100)) : [];
      if (options.length < 2 || options.length > 6) fail(400, "Question " + n + " needs 2 to 6 answer choices.");
      if (options.some((o) => !o)) fail(400, "Fill in every answer choice for question " + n + ".");
      const a = Number(q.a);
      if (!Number.isInteger(a) || a < 0 || a >= options.length) fail(400, "Pick the right answer for question " + n + ".");
      return { t: "mc", q: text, options: options, a: a };
    }
    if (q.t === "short") {
      const a = cleanText(q.a, 100);
      if (!normAnswer(a.split("|")[0])) fail(400, "Type the right answer for question " + n + ".");
      return { t: "short", q: text, a: a };
    }
    fail(400, "Question " + n + " has an unknown type.");
  });
}

function requireCreator(u) {
  if (u.role === "student" || (u.role === "educator" && u.educator)) return;
  fail(403, "Finish setting up your account first.");
}

function reviewBody(c) {
  const title = cleanText(c.body.title, 60);
  if (title.length < 2) fail(400, "Give the review a title.");
  return { title: title, subject: cleanText(c.body.subject, 40), questions: cleanQuestions(c.body.questions) };
}

const reviewMeta = (r) => ({ id: r.id, title: r.title, subject: r.subject, count: r.questions.length, updated: r.updated });

function ownReviewById(u, id) {
  const r = db.reviews[String(id || "")];
  if (!r || r.ownerId !== u.id) fail(404, "Review not found.");
  return r;
}

function dropScores(reviewId) {
  for (const k of Object.keys(db.scores)) if (k.indexOf(reviewId + ":") === 0) delete db.scores[k];
}

function createReview(c) {
  requireCreator(c.user);
  if (Object.values(db.reviews).filter((r) => r.ownerId === c.user.id).length >= 50) fail(400, "That's the most reviews you can keep (50).");
  const b = reviewBody(c);
  const r = { id: rand(8), ownerId: c.user.id, title: b.title, subject: b.subject, questions: b.questions, classIds: [], created: Date.now(), updated: Date.now() };
  db.reviews[r.id] = r;
  saveDb();
  return { review: reviewMeta(r) };
}

function getReview(c) {
  const r = ownReviewById(c.user, c.body.id);
  return { review: { id: r.id, title: r.title, subject: r.subject, questions: r.questions } };
}

function updateReview(c) {
  const r = ownReviewById(c.user, c.body.id);
  Object.assign(r, reviewBody(c), { updated: Date.now() });
  dropScores(r.id);
  saveDb();
  return { review: reviewMeta(r) };
}

function deleteReview(c) {
  const r = ownReviewById(c.user, c.body.id);
  delete db.reviews[r.id];
  dropScores(r.id);
  saveDb();
  return { ok: true };
}

function inClass(u, classId) {
  const k = db.classes[classId];
  return !!k && k.students.indexOf(u.id) !== -1;
}

function reachable(u, r) {
  return r.ownerId === u.id || (u.role === "student" && r.classIds.some((cid) => inClass(u, cid)));
}

function listReviews(c) {
  const u = c.user;
  requireCreator(u);
  const mine = Object.values(db.reviews)
    .filter((r) => r.ownerId === u.id)
    .sort((a, b) => b.updated - a.updated)
    .map((r) => {
      const sc = db.scores[r.id + ":" + u.id];
      const m = Object.assign(reviewMeta(r), { best: sc ? sc.best : null });
      if (u.role === "educator") m.classIds = r.classIds.slice();
      return m;
    });
  const assigned = [];
  if (u.role === "student") {
    for (const r of Object.values(db.reviews)) {
      const cid = r.ownerId !== u.id ? r.classIds.find((id) => inClass(u, id)) : null;
      if (!cid) continue;
      const sc = db.scores[r.id + ":" + u.id];
      assigned.push(Object.assign(reviewMeta(r), { className: db.classes[cid].name, educator: educatorLabel(db.users[r.ownerId] || {}), best: sc ? sc.best : null }));
    }
  }
  return { mine: mine, assigned: assigned };
}

function takeReview(c) {
  const r = db.reviews[String(c.body.id || "")];
  if (!r || !reachable(c.user, r)) fail(404, "Review not found.");
  return { review: { id: r.id, title: r.title, subject: r.subject, questions: r.questions.map((q) => (q.t === "mc" ? { t: "mc", q: q.q, options: q.options } : { t: "short", q: q.q })) } };
}

function submitReview(c) {
  const r = db.reviews[String(c.body.id || "")];
  if (!r || !reachable(c.user, r)) fail(404, "Review not found.");
  const answers = Array.isArray(c.body.answers) ? c.body.answers : [];
  let score = 0;
  const results = r.questions.map((q, i) => {
    const given = answers[i];
    let ok = false;
    if (q.t === "mc") ok = Number.isInteger(given) && given === q.a;
    else ok = typeof given === "string" && q.a.split("|").map(normAnswer).filter(Boolean).indexOf(normAnswer(given.slice(0, 200))) !== -1;
    if (ok) score++;
    return {
      correct: ok,
      yours: q.t === "mc" ? (Number.isInteger(given) ? given : null) : typeof given === "string" ? cleanText(given, 100) : "",
      answer: q.t === "mc" ? q.a : q.a.split("|")[0].trim()
    };
  });
  const key = r.id + ":" + c.user.id;
  const sc = db.scores[key] || { best: 0, count: 0 };
  sc.count = Math.min(sc.count + 1, 999);
  sc.best = Math.max(sc.best, score);
  sc.total = r.questions.length;
  sc.at = Date.now();
  db.scores[key] = sc;
  saveDb();
  return { score: score, total: r.questions.length, results: results };
}

function assignReview(c) {
  if (c.user.role !== "educator") fail(403, "Only educators can give reviews to classes.");
  const r = ownReviewById(c.user, c.body.reviewId);
  const k = db.classes[String(c.body.classId || "")];
  if (!k || k.ownerId !== c.user.id) fail(404, "Class not found.");
  const has = r.classIds.indexOf(k.id) !== -1;
  if (c.body.on === true && !has) r.classIds.push(k.id);
  else if (c.body.on === false && has) r.classIds = r.classIds.filter((id) => id !== k.id);
  saveDb();
  return { classIds: r.classIds.slice() };
}

function reviewResults(c) {
  const r = ownReviewById(c.user, c.body.id);
  const classes = r.classIds
    .map((cid) => db.classes[cid])
    .filter(Boolean)
    .map((k) => ({
      id: k.id,
      name: k.name,
      students: k.students.map((sid) => {
        const s = db.users[sid];
        const sc = db.scores[r.id + ":" + sid];
        return { name: shortName(s ? s.name : ""), best: sc ? sc.best : null, total: r.questions.length, attempts: sc ? sc.count : 0 };
      })
    }));
  return { title: r.title, classes: classes };
}

function listClasses(c) {
  const u = c.user;
  const all = Object.values(db.classes);
  if (u.role === "educator") {
    if (!u.educator) fail(403, "Finish creating your educator account first.");
    return {
      classes: all
        .filter((k) => k.ownerId === u.id)
        .map((k) => ({
          id: k.id,
          code: k.code,
          name: k.name,
          students: k.students.map((id) => db.users[id]).filter(Boolean).map((s) => ({ name: shortName(s.name) })),
          reviews: Object.values(db.reviews).filter((r) => r.classIds.indexOf(k.id) !== -1).map((r) => ({ id: r.id, title: r.title }))
        }))
    };
  }
  if (u.role === "student") {
    return { classes: all.filter((k) => k.students.indexOf(u.id) !== -1).map((k) => ({ id: k.id, name: k.name, educator: educatorLabel(db.users[k.ownerId] || {}) })) };
  }
  fail(403, "Pick a role first.");
}

function createClass(c) {
  const u = c.user;
  if (u.role !== "educator" || !u.educator) fail(403, "Only educators can create classes.");
  const name = cleanName(c.body.name, 40);
  if (name.length < 2) fail(400, "Give the class a name (at least 2 letters).");
  if (Object.values(db.classes).filter((k) => k.ownerId === u.id).length >= 30) fail(400, "That's the most classes one educator can have (30).");
  let code;
  do {
    code = "";
    for (let i = 0; i < 6; i++) code += CLASS_CHARS[crypto.randomInt(CLASS_CHARS.length)];
  } while (db.byCode[code]);
  const k = { id: rand(8), code: code, name: name, ownerId: u.id, created: Date.now(), students: [] };
  db.classes[k.id] = k;
  db.byCode[code] = k.id;
  saveDb();
  return { class: { id: k.id, code: k.code, name: k.name, students: [] } };
}

function joinClass(c) {
  const u = c.user;
  if (u.role !== "student") fail(403, "Only students can join classes.");
  if (limited("join:" + u.id, 20, 600000)) fail(429, "Too many tries. Wait a few minutes.");
  const code = String(c.body.code || "").toUpperCase().replace(/[^A-Z0-9]/g, "");
  const k = db.classes[db.byCode[code]];
  if (code.length !== 6 || !k) fail(404, "No class has that code. Check it with your educator.");
  if (k.students.indexOf(u.id) !== -1) return { joined: false, class: { id: k.id, name: k.name }, message: "You're already in this class." };
  if (k.students.length >= 200) fail(400, "That class is full.");
  if (Object.values(db.classes).filter((x) => x.students.indexOf(u.id) !== -1).length >= 20) fail(400, "You can be in up to 20 classes.");
  k.students.push(u.id);
  saveDb();
  return { joined: true, class: { id: k.id, name: k.name, educator: educatorLabel(db.users[k.ownerId] || {}) } };
}

function leaveClass(c) {
  const k = db.classes[String(c.body.id || "")];
  if (!k || k.students.indexOf(c.user.id) === -1) fail(404, "You're not in that class.");
  k.students = k.students.filter((id) => id !== c.user.id);
  saveDb();
  return { ok: true };
}

function deleteClass(c) {
  const k = db.classes[String(c.body.id || "")];
  if (!k || k.ownerId !== c.user.id) fail(404, "Class not found.");
  delete db.classes[k.id];
  delete db.byCode[k.code];
  for (const r of Object.values(db.reviews)) r.classIds = r.classIds.filter((id) => id !== k.id);
  saveDb();
  return { ok: true };
}

function logout(c) {
  c.user.tv++;
  saveDb();
  return { ok: true };
}

const ROUTES = {
  "GET /config": { fn: () => ({ google: GOOGLE_CLIENT_ID ? { clientId: GOOGLE_CLIENT_ID } : null, email: !!(RESEND_API_KEY || DEV_SHOW_CODE), demo: ALLOW_DEMO }) },
  "POST /auth/google": { limit: 30, fn: authGoogle },
  "POST /auth/email/start": { limit: 30, fn: emailStart },
  "POST /auth/email/verify": { limit: 30, fn: emailVerify },
  "POST /auth/demo": { limit: 30, fn: authDemo },
  "GET /me": { auth: true, fn: (c) => ({ user: publicUser(c.user) }) },
  "POST /role": { auth: true, fn: setRole },
  "POST /educator/start": { auth: true, fn: educatorStart },
  "POST /educator/resend": { auth: true, fn: educatorResend },
  "POST /educator/verify": { auth: true, fn: educatorVerify },
  "GET /classes": { auth: true, fn: listClasses },
  "POST /classes": { auth: true, fn: createClass },
  "POST /classes/join": { auth: true, fn: joinClass },
  "POST /classes/leave": { auth: true, fn: leaveClass },
  "POST /classes/delete": { auth: true, fn: deleteClass },
  "GET /reviews": { auth: true, fn: listReviews },
  "POST /reviews": { auth: true, max: 60000, fn: createReview },
  "POST /reviews/get": { auth: true, fn: getReview },
  "POST /reviews/update": { auth: true, max: 60000, fn: updateReview },
  "POST /reviews/delete": { auth: true, fn: deleteReview },
  "POST /reviews/take": { auth: true, fn: takeReview },
  "POST /reviews/submit": { auth: true, fn: submitReview },
  "POST /reviews/assign": { auth: true, fn: assignReview },
  "POST /reviews/results": { auth: true, fn: reviewResults },
  "POST /logout": { auth: true, fn: logout }
};

function readJson(req, max) {
  return new Promise((resolve, reject) => {
    if (req.method === "GET") {
      resolve({});
      return;
    }
    if (Number(req.headers["content-length"]) > max) {
      reject(new HttpError(413, "That request is too big."));
      return;
    }
    let size = 0;
    const chunks = [];
    req.on("data", (d) => {
      size += d.length;
      if (size > max) {
        reject(new HttpError(413, "That request is too big."));
        return;
      }
      chunks.push(d);
    });
    req.on("end", () => {
      try {
        const text = Buffer.concat(chunks).toString() || "{}";
        const j = JSON.parse(text);
        resolve(j && typeof j === "object" && !Array.isArray(j) ? j : {});
      } catch (e) {
        reject(new HttpError(400, "That request couldn't be read."));
      }
    });
    req.on("error", () => reject(new HttpError(400, "That request couldn't be read.")));
  });
}

function userFromRequest(req) {
  const h = String(req.headers.authorization || "");
  if (h.indexOf("Bearer ") !== 0) return null;
  const t = unsign(h.slice(7));
  if (!t || typeof t.uid !== "string" || !(t.exp > Date.now())) return null;
  const u = db.users[t.uid];
  return u && u.tv === t.tv ? u : null;
}

const server = http.createServer(async (req, res) => {
  const origin = String(req.headers.origin || "");
  const open = ORIGINS.length === 0;
  const allowed = open || ORIGINS.indexOf(origin) !== -1;
  const headers = {
    "Access-Control-Allow-Origin": open ? "*" : allowed ? origin : "null",
    "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
    "Access-Control-Allow-Headers": "Content-Type, Authorization",
    "Access-Control-Max-Age": "600",
    Vary: "Origin",
    "Cache-Control": "no-store"
  };
  const reply = (code, obj) => {
    const extra = req.complete ? null : { Connection: "close" };
    res.writeHead(code, Object.assign({ "Content-Type": "application/json" }, headers, extra));
    res.end(JSON.stringify(obj));
  };
  res.on("finish", () => {
    if (!req.complete) req.destroy();
  });
  try {
    const url = String(req.url || "/").split("?")[0].replace(/\/+$/, "") || "/";
    if (req.method === "OPTIONS") {
      res.writeHead(204, headers);
      res.end();
      return;
    }
    if (url === "/") {
      res.writeHead(200, Object.assign({ "Content-Type": "text/plain" }, headers));
      res.end("BrainGain server is running");
      return;
    }
    if (!allowed) fail(403, "This website isn't allowed to use this server.");
    const route = ROUTES[req.method + " " + url];
    if (!route) fail(404, "Not found.");
    const ip = clientIp(req);
    if (route.limit && limited("auth:" + ip, route.limit, 600000)) fail(429, "Too many sign-in tries. Please wait a few minutes.");
    const user = route.auth ? userFromRequest(req) : null;
    if (route.auth && !user) fail(401, "Please sign in again.");
    if (route.auth && limited("api:" + user.id, 240, 60000)) fail(429, "Slow down a little.");
    const body = await readJson(req, route.max || 10000);
    const out = await route.fn({ req: req, ip: ip, body: body, user: user });
    reply(200, out);
  } catch (e) {
    if (e instanceof HttpError) reply(e.code, { error: e.message });
    else {
      console.error("[error] " + (e && e.stack));
      reply(500, { error: "Something went wrong on the server." });
    }
  }
});

function shutdown() {
  flushDb();
  process.exit(0);
}

process.on("SIGTERM", shutdown);
process.on("SIGINT", shutdown);

loadDb();

if (require.main === module) {
  if (!ORIGINS.length) console.log("[security] ALLOWED_ORIGINS is not set, so any website can call this server");
  if (!process.env.AUTH_SECRET) console.log("[security] AUTH_SECRET is not set. Logins will reset every time the server restarts");
  console.log("[login] Google: " + (GOOGLE_CLIENT_ID ? "on" : "off") + ", email: " + (RESEND_API_KEY || DEV_SHOW_CODE ? "on" : "off") + ", demo: " + (ALLOW_DEMO ? "ON (testing only)" : "off"));
  console.log("[mail] " + (RESEND_API_KEY ? "Resend is set up" : DEV_SHOW_CODE ? "testing mode: codes are shown on screen" : "NOT set up: educators can't verify yet"));
  server.listen(PORT, () => console.log("BrainGain server listening on port " + PORT));
}

module.exports = { server: server };

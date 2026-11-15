'use strict';

/**
 * RK X RAJA - ELITE CYBER MATRIX PRO CONSOLE
 * 24/7 WhatsApp Bulk Sender Bot
 *
 * IMPORTANT:
 * - No proxy logic is used anywhere.
 * - Sessions are stored in ./sessions_data/<session-name>.
 * - Pairing code is strictly generated only once per pairing request and is
 *   persisted in meta.json so network drops do not rotate it.
 */

const express = require('express');
const multer = require('multer');
const path = require('path');
const fs = require('fs');
const fsp = fs.promises;
const crypto = require('crypto');
const Boom = require('@hapi/boom');
const pino = require('pino');
const qrcodeTerminal = require('qrcode-terminal');

const baileys = require('@whiskeysockets/baileys');
const makeWASocket = baileys.default || baileys.makeWASocket;
const {
  useMultiFileAuthState,
  makeCacheableSignalKeyStore,
  fetchLatestWaWebVersion,
  DisconnectReason,
  Browsers,
} = baileys;

const app = express();
const PORT = process.env.PORT || 3000;
const SESSIONS_ROOT = path.join(__dirname, 'sessions_data');
const MAX_LOG_LINES = 300;
const MAX_TXT_BYTES = 5 * 1024 * 1024;

const logger = pino({ level: process.env.LOG_LEVEL || 'silent' });

app.use(express.json({ limit: '2mb' }));
app.use(express.urlencoded({ extended: true, limit: '2mb' }));

const sessions = new Map();
let activeSessionName = null;
let bulkTask = null;
let cachedWaVersion = null;
let waVersionFailedAt = 0;
let globalLogSeq = 0;
let systemLogs = [];
let shuttingDown = false;
let watchdogTimer = null;

/* -------------------------------------------------------------------------- */
/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function asyncHandler(fn) {
  return (req, res, next) => Promise.resolve(fn(req, res, next)).catch(next);
}

function withTimeout(promise, ms, label) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      reject(new Error(label + ' timed out after ' + ms + 'ms'));
    }, ms);
    promise.then(
      (value) => {
        clearTimeout(timer);
        resolve(value);
      },
      (err) => {
        clearTimeout(timer);
        reject(err);
      }
    );
  });
}

function sanitizeSessionName(raw) {
  const name = String(raw || '')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9_-]/g, '_')
    .replace(/^_+|_+$/g, '')
    .slice(0, 40);

  if (!name || name === '.' || name === '..') {
    throw Boom.badRequest('Invalid session name. Use letters, numbers, dash or underscore (max 40 chars).');
  }
  return name;
}

function normalizePhone(raw) {
  const digits = String(raw || '').replace(/\D/g, '');
  if (!/^\d{7,15}$/.test(digits)) {
    throw Boom.badRequest('Phone number must contain 7 to 15 digits including country code. Example: 919876543210');
  }
  return digits;
}

function nowTimeLabel(date) {
  return new Date(date || Date.now()).toLocaleTimeString('en-US', {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: true,
  });
}

function makeLogEntry(text) {
  return {
    seq: ++globalLogSeq,
    text: '[' + nowTimeLabel() + '] ' + String(text),
  };
}

function pushSystemLog(text) {
  const entry = makeLogEntry(text);
  systemLogs.push(entry);
  if (systemLogs.length > MAX_LOG_LINES) {
    systemLogs.splice(0, systemLogs.length - MAX_LOG_LINES);
  }
  console.log(entry.text);
  return entry;
}

function bulkLog(task, text) {
  if (!task) {
    pushSystemLog(text);
    return;
  }
  const entry = makeLogEntry(text);
  task.logs.push(entry);
  if (task.logs.length > MAX_LOG_LINES) {
    task.logs.splice(0, task.logs.length - MAX_LOG_LINES);
  }
  console.log(entry.text);
}

function getMergedLogs() {
  const taskLogs = bulkTask && Array.isArray(bulkTask.logs) ? bulkTask.logs : [];
  return systemLogs
    .concat(taskLogs)
    .sort((a, b) => a.seq - b.seq)
    .slice(-MAX_LOG_LINES);
}

function defaultMeta() {
  return {
    createdAt: new Date().toISOString(),
    passwordSalt: null,
    passwordHash: null,
    phoneNumber: null,
    pairingRequested: false,
    pairingCode: null,
    pairingCodeGeneratedAt: null,
    paired: false,
    lastPairedAt: null,
  };
}

function makePasswordFields(password) {
  if (password === undefined || password === null || String(password).length === 0) {
    return { passwordSalt: null, passwordHash: null };
  }
  const salt = crypto.randomBytes(16).toString('hex');
  const hash = crypto.scryptSync(String(password), salt, 64).toString('hex');
  return { passwordSalt: salt, passwordHash: hash };
}

function checkSessionPassword(session, provided) {
  if (!session || !session.meta || !session.meta.passwordHash) return true;
  if (provided === undefined || provided === null || String(provided).length === 0) return false;

  try {
    const derived = crypto.scryptSync(String(provided), session.meta.passwordSalt, 64).toString('hex');
    const a = Buffer.from(derived, 'hex');
    const b = Buffer.from(session.meta.passwordHash, 'hex');
    return a.length === b.length && crypto.timingSafeEqual(a, b);
  } catch {
    return false;
  }
}

function authorizeSession(session, req) {
  const password =
    (req.body && req.body.password) ||
    (req.query && req.query.password) ||
    req.headers['x-session-password'];

  if (!checkSessionPassword(session, password)) {
    throw Boom.unauthorized('Invalid session password.');
  }
}

/* -------------------------------------------------------------------------- */
/* Session persistence                                                        */
/* -------------------------------------------------------------------------- */

async function readMeta(dir) {
  try {
    const raw = await fsp.readFile(path.join(dir, 'meta.json'), 'utf8');
    const parsed = JSON.parse(raw);
    return Object.assign(defaultMeta(), parsed || {});
  } catch {
    return defaultMeta();
  }
}

async function writeMeta(session) {
  const tmp = path.join(
    session.dir,
    'meta.' + process.pid + '.' + Date.now() + '.' + Math.random().toString(16).slice(2) + '.tmp'
  );
  const target = path.join(session.dir, 'meta.json');
  await fsp.writeFile(tmp, JSON.stringify(session.meta, null, 2), 'utf8');
  await fsp.rename(tmp, target);
}

async function getSession(name) {
  const safe = sanitizeSessionName(name);
  if (sessions.has(safe)) return sessions.get(safe);

  const dir = path.join(SESSIONS_ROOT, safe);
  await fsp.mkdir(dir, { recursive: true });
  const meta = await readMeta(dir);

  const session = {
    name: safe,
    dir,
    meta,
    sock: null,
    authState: null,
    saveCreds: null,
    connected: false,
    connecting: false,
    connectPromise: null,
    reconnectTimer: null,
    intentionalClose: false,
    autoReconnect: true,
    pairingPromise: null,
    pendingPairingPhone: null,
    qrReceivedAt: 0,
    qrWaiters: [],
    lastError: null,
    lastCloseAt: 0,
    lastHeartbeat: Date.now(),
    createdAt: Date.now(),
    connectingSince: 0,
  };

  sessions.set(safe, session);
  return session;
}

async function listSessionNames() {
  await fsp.mkdir(SESSIONS_ROOT, { recursive: true });
  const entries = await fsp.readdir(SESSIONS_ROOT, { withFileTypes: true });
  return entries
    .filter((entry) => entry.isDirectory() && /^[a-z0-9_-]{1,40}$/i.test(entry.name) && !entry.name.startsWith('.'))
    .map((entry) => entry.name)
    .sort();
}

async function isSessionPairedFromDisk(name) {
  try {
    const raw = await fsp.readFile(path.join(SESSIONS_ROOT, name, 'creds.json'), 'utf8');
    const creds = JSON.parse(raw);
    return creds.registered === true;
  } catch {
    return false;
  }
}

async function resetSessionDirectory(session) {
  const preserved = {
    passwordSalt: session.meta.passwordSalt,
    passwordHash: session.meta.passwordHash,
  };

  if (session.reconnectTimer) {
    clearTimeout(session.reconnectTimer);
    session.reconnectTimer = null;
  }

  await fsp.rm(session.dir, { recursive: true, force: true });
  await fsp.mkdir(session.dir, { recursive: true });

  session.meta = Object.assign(defaultMeta(), preserved, {
    createdAt: new Date().toISOString(),
  });
  await writeMeta(session);

  session.authState = null;
  session.saveCreds = null;
  session.pendingPairingPhone = null;
  session.pairingPromise = null;
  session.qrReceivedAt = 0;
  session.qrWaiters = [];
  session.connected = false;
  session.connecting = false;
  session.lastError = null;
}

async function syncPairedMeta(session) {
  try {
    if (session.authState && session.authState.creds && session.authState.creds.registered) {
      if (!session.meta.paired) {
        session.meta.paired = true;
        session.meta.lastPairedAt = new Date().toISOString();
        session.meta.pairingCode = null;
        session.meta.pairingRequested = true;
        await writeMeta(session);
        pushSystemLog('Session ' + session.name + ' is now PAIRED.');
      }
    }
  } catch (err) {
    pushSystemLog('Failed to sync paired meta for ' + session.name + ': ' + err.message);
  }
}

/* -------------------------------------------------------------------------- */
/* WhatsApp version                                                           */
/* -------------------------------------------------------------------------- */

async function getWaVersion() {
  if (cachedWaVersion) return cachedWaVersion;

  if (waVersionFailedAt && Date.now() - waVersionFailedAt < 5 * 60 * 1000) {
    return undefined;
  }

  try {
    const result = await withTimeout(fetchLatestWaWebVersion(), 10000, 'WA Web version fetch');
    if (result && Array.isArray(result.version)) {
      cachedWaVersion = result.version;
      pushSystemLog('WhatsApp Web version resolved: ' + cachedWaVersion.join('.'));
      return cachedWaVersion;
    }
  } catch (err) {
    waVersionFailedAt = Date.now();
    pushSystemLog('WA Web version fetch failed, using Baileys default: ' + err.message);
  }

  return undefined;
}

/* -------------------------------------------------------------------------- */
/* Connection lifecycle                                                       */
/* -------------------------------------------------------------------------- */

function resolveQrWaiters(session) {
  const waiters = session.qrWaiters.splice(0);
  for (const waiter of waiters) {
    try {
      waiter();
    } catch {
      // Ignore waiter errors.
    }
  }
}

function waitForQr(session, timeoutMs) {
  if (session.qrReceivedAt && Date.now() - session.qrReceivedAt < 60000) {
    return Promise.resolve();
  }

  return new Promise((resolve, reject) => {
    let done = false;

    const timer = setTimeout(() => {
      if (done) return;
      done = true;
      const index = session.qrWaiters.indexOf(waiter);
      if (index >= 0) session.qrWaiters.splice(index, 1);
      reject(new Error('Timed out waiting for WhatsApp QR stream. Please try pairing again.'));
    }, timeoutMs);

    const waiter = () => {
      if (done) return;
      done = true;
      clearTimeout(timer);
      resolve();
    };

    session.qrWaiters.push(waiter);
  });
}

function scheduleReconnect(session, delayMs) {
  if (session.reconnectTimer || session.intentionalClose || !session.autoReconnect) return;
  if (activeSessionName !== session.name) return;

  session.reconnectTimer = setTimeout(async () => {
    session.reconnectTimer = null;
    if (session.intentionalClose || !session.autoReconnect) return;
    if (activeSessionName !== session.name) return;

    try {
      pushSystemLog('Reconnecting ' + session.name + ' after 3s...');
      await connectSession(session.name);
    } catch (err) {
      pushSystemLog('Reconnect failed for ' + session.name + ': ' + err.message);
      scheduleReconnect(session, Math.min(30000, Math.max(3000, delayMs * 2)));
    }
  }, Math.max(1000, delayMs));

  if (session.reconnectTimer.unref) session.reconnectTimer.unref();
}

async function handleConnectionUpdate(session, update) {
  session.lastHeartbeat = Date.now();

  const connection = update.connection;
  const lastDisconnect = update.lastDisconnect;
  const qr = update.qr;

  if (qr) {
    session.qrReceivedAt = Date.now();
    resolveQrWaiters(session);
    pushSystemLog('QR stream ready for ' + session.name + '.');

    if (process.env.SHOW_QR === 'true') {
      try {
        qrcodeTerminal.generate(qr, { small: true });
      } catch {
        // QR terminal rendering is optional.
      }
    }

    if (session.pendingPairingPhone && !session.meta.pairingRequested && !session.pairingPromise) {
      generatePairingCode(session, session.pendingPairingPhone).catch((err) => {
        pushSystemLog('Auto pairing-code generation failed for ' + session.name + ': ' + err.message);
      });
    }
  }

  if (connection === 'open') {
    session.connected = true;
    session.connecting = false;
    session.qrReceivedAt = 0;
    session.lastError = null;
    session.autoReconnect = true;
    pushSystemLog('WhatsApp uplink ONLINE for ' + session.name + '.');
    await syncPairedMeta(session);
    return;
  }

  if (connection === 'close') {
    session.connected = false;
    session.connecting = false;
    session.lastCloseAt = Date.now();

    if (session.intentionalClose) {
      return;
    }

    const statusCode =
      (lastDisconnect && lastDisconnect.error && lastDisconnect.error.output && lastDisconnect.error.output.statusCode) ||
      (lastDisconnect && lastDisconnect.error && lastDisconnect.error.statusCode) ||
      null;

    const message =
      (lastDisconnect && lastDisconnect.error && lastDisconnect.error.message) ||
      'connection closed';

    session.lastError = 'Code ' + statusCode + ': ' + message;
    pushSystemLog('Uplink closed for ' + session.name + ' (' + session.lastError + ').');

    const loggedOut = statusCode === 401 || statusCode === DisconnectReason.loggedOut;
    const forbidden = statusCode === 403 || statusCode === DisconnectReason.forbidden;
    const multiDeviceMismatch = statusCode === 411 || statusCode === DisconnectReason.multideviceMismatch;
    const connectionReplaced = statusCode === 440 || statusCode === DisconnectReason.connectionReplaced;

    if (loggedOut) {
      session.autoReconnect = false;
      session.intentionalClose = true;
      session.sock = null;
      try {
        await resetSessionDirectory(session);
      } catch (err) {
        pushSystemLog('Failed to reset logged-out session ' + session.name + ': ' + err.message);
      }
      session.intentionalClose = false;
      session.autoReconnect = false;
      pushSystemLog('Session ' + session.name + ' was logged out. Pair again from the dashboard.');
      return;
    }

    if (forbidden || multiDeviceMismatch || connectionReplaced) {
      session.autoReconnect = false;
      pushSystemLog('Fatal disconnect for ' + session.name + '. Auto-reconnect disabled.');
      return;
    }

    // 515 restartRequired, 428, 408, 503, 500 and normal drops are retried.
    if (session.autoReconnect && activeSessionName === session.name) {
      scheduleReconnect(session, 3000);
    }
  }
}

async function connectSession(name) {
  const session = await getSession(name);

  if (session.connected && session.sock) return session;
  if (session.connectPromise) return session.connectPromise;

  session.connectPromise = (async () => {
    if (session.sock) {
      const state = session.sock.ws && session.sock.ws.readyState;
      if (state === 0 || state === 1) return session;
      try {
        session.sock.end(undefined);
      } catch {
        // Ignore stale socket close errors.
      }
      session.sock = null;
    }

    session.intentionalClose = false;
    session.connecting = true;
    session.connectingSince = Date.now();
    session.lastError = null;

    const version = await getWaVersion();
    const { state, saveCreds } = await useMultiFileAuthState(session.dir);

    session.authState = state;
    session.saveCreds = saveCreds;

    const sock = makeWASocket(
      Object.assign(
        {},
        version ? { version } : {},
        {
          auth: {
            creds: state.creds,
            keys: makeCacheableSignalKeyStore(state.keys, logger),
          },
          browser: Browsers.ubuntu('Chrome'),
          logger,
          printQRInTerminal: false,
          markOnlineOnConnect: false,
          syncFullHistory: false,
          connectTimeoutMs: 60000,
          defaultQueryTimeoutMs: 60000,
          keepAliveIntervalMs: 25000,
          retryRequestDelayMs: 2000,
          generateHighQualityLinkPreview: false,
          getMessage: async () => undefined,
        }
      )
    );

    session.sock = sock;

    sock.ev.on('creds.update', async () => {
      try {
        await saveCreds();
      } catch (err) {
        pushSystemLog('creds.save failed for ' + session.name + ': ' + err.message);
      }
      await syncPairedMeta(session);
    });

    sock.ev.on('connection.update', (update) => {
      if (session.sock !== sock) return;
      handleConnectionUpdate(session, update).catch((err) => {
        pushSystemLog('connection.update handler error for ' + session.name + ': ' + err.message);
      });
    });

    sock.ev.on('messages.upsert', () => {
      session.lastHeartbeat = Date.now();
    });

    session.connecting = false;
    return session;
  })()
    .catch(async (err) => {
      session.connecting = false;
      session.lastError = err.message;
      pushSystemLog('Connection start failed for ' + session.name + ': ' + err.message);
      throw err;
    })
    .finally(() => {
      session.connectPromise = null;
    });

  return session.connectPromise;
}

async function stopSocket(session) {
  session.intentionalClose = true;

  if (session.reconnectTimer) {
    clearTimeout(session.reconnectTimer);
    session.reconnectTimer = null;
  }

  if (session.sock) {
    try {
      session.sock.end(undefined);
    } catch {
      // Ignore end errors.
    }
  }

  session.sock = null;
  session.connected = false;
  session.connecting = false;
}

async function generatePairingCode(session, phone) {
  const cleanPhone = normalizePhone(phone);

  if (session.pairingPromise) return session.pairingPromise;

  session.pairingPromise = (async () => {
    if (session.authState && session.authState.creds && session.authState.creds.registered) {
      return null;
    }

    if (session.meta.pairingRequested && session.meta.pairingCode) {
      return session.meta.pairingCode;
    }

    if (session.meta.pairingRequested && !session.meta.pairingCode) {
      throw Boom.conflict('Pairing lock is active for this session. Use Logout to reset the session.');
    }

    if (!session.sock) {
      throw new Error('WhatsApp socket is not ready. Please try again.');
    }

    // STRICT LOCK: set and persist before the request so reconnects cannot rotate it.
    session.meta.pairingRequested = true;
    session.meta.phoneNumber = cleanPhone;
    session.meta.pairingCodeGeneratedAt = Date.now();
    await writeMeta(session);

    try {
      const code = await session.sock.requestPairingCode(cleanPhone);
      session.meta.pairingCode = code;
      await writeMeta(session);
      pushSystemLog('Pairing code generated ONCE for ' + session.name + ' (' + cleanPhone + ').');
      return code;
    } catch (err) {
      session.meta.pairingRequested = false;
      session.meta.pairingCode = null;
      session.meta.pairingCodeGeneratedAt = null;
      await writeMeta(session);
      throw err;
    }
  })();

  try {
    return await session.pairingPromise;
  } finally {
    session.pairingPromise = null;
    session.pendingPairingPhone = null;
  }
}

async function switchActiveSession(name) {
  const target = await getSession(name);

  if (activeSessionName === target.name) return target;

  if (bulkTask && bulkTask.running) {
    throw Boom.conflict('Stop the bulk loop before switching sessions.');
  }

  const previous = activeSessionName ? sessions.get(activeSessionName) : null;
  if (previous) {
    await stopSocket(previous);
  }

  activeSessionName = target.name;
  target.intentionalClose = false;
  target.autoReconnect = true;

  await connectSession(target.name);
  pushSystemLog('Active session switched to ' + target.name + '.');
  return target;
}

async function forceReconnect(session, reason) {
  pushSystemLog('Watchdog restarting ' + session.name + ': ' + reason);
  await stopSocket(session);
  session.intentionalClose = false;
  session.autoReconnect = true;

  if (activeSessionName === session.name) {
    try {
      await connectSession(session.name);
    } catch (err) {
      pushSystemLog('Watchdog reconnect failed for ' + session.name + ': ' + err.message);
      scheduleReconnect(session, 3000);
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Bulk sender helpers                                                        */
/* -------------------------------------------------------------------------- */

function composeMessage(task, rawMessage) {
  let text = String(rawMessage);
  if (task.prefix) text = task.prefix + ' ' + text;
  if (task.suffix) text = text + ' ' + task.suffix;
  return text;
}

function parseMessageFile(buffer) {
  const text = buffer
    .toString('utf8')
    .replace(/^\uFEFF/, '')
    .replace(/\r/g, '');

  const lines = text
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean);

  return Array.from(new Set(lines));
}

function parseGroupTargets(raw) {
  const text = String(raw || '').trim();
  if (!text) return [];

  let arr;
  try {
    arr = JSON.parse(text);
  } catch {
    arr = text.split(',');
  }

  if (!Array.isArray(arr)) return [];

  const targets = [];
  for (const item of arr) {
    const jid = String(item || '').trim();
    if (jid.endsWith('@g.us')) targets.push(jid);
  }

  return Array.from(new Set(targets));
}

function parseNumberTargets(raw) {
  const parts = String(raw || '')
    .split(/[\n,;]+/)
    .map((part) => part.trim())
    .filter(Boolean);

  const targets = [];

  for (const part of parts) {
    const digits = part.replace(/\D/g, '');
    if (!/^\d{7,15}$/.test(digits)) {
      throw Boom.badRequest('Invalid phone number: ' + part + '. Use country code, digits only, 7-15 digits.');
    }
    targets.push(digits + '@s.whatsapp.net');
  }

  return Array.from(new Set(targets));
}

async function waitForSocketOpen(sessionName, timeoutMs, task) {
  const session = sessions.get(sessionName);
  const startedAt = Date.now();

  while (Date.now() - startedAt < timeoutMs) {
    if (task && (!task.running || task.stopRequested)) {
      throw new Error('__STOPPED__');
    }

    if (session && session.connected && session.sock) {
      return session.sock;
    }

    await sleep(500);
  }

  throw new Error('Session ' + sessionName + ' is not connected.');
}

async function interruptibleDelay(task, ms) {
  const endAt = Date.now() + Math.max(0, ms);

  while (Date.now() < endAt) {
    if (!task.running || task.stopRequested) return false;
    await sleep(Math.min(500, Math.max(10, endAt - Date.now())));
  }

  return task.running && !task.stopRequested;
}

function stopBulkTask(reason) {
  if (!bulkTask) return;
  bulkTask.stopRequested = true;
  bulkTask.running = false;
  bulkLog(bulkTask, 'STOP requested (' + (reason || 'manual') + ').');
}

async function runBulkLoop(task) {
  bulkLog(
    task,
    'Cycle ' + task.cycle + ' | START | ' + task.messages.length + ' messages x ' + task.targets.length + ' targets'
  );

  try {
    while (task.running && !task.stopRequested) {
      task.cycle += 1;

      bulkLog(
        task,
        'Cycle ' + task.cycle + ' | START | ' + task.messages.length + ' msgs x ' + task.targets.length + ' targets'
      );

      for (let messageIndex = 0; messageIndex < task.messages.length; messageIndex += 1) {
        if (!task.running || task.stopRequested) break;

        const composedMessage = composeMessage(task, task.messages[messageIndex]);

        for (let targetIndex = 0; targetIndex < task.targets.length; targetIndex += 1) {
          if (!task.running || task.stopRequested) break;

          const target = task.targets[targetIndex];

          task.currentIndex = messageIndex * task.targets.length + targetIndex + 1;
          task.totalSends = task.messages.length * task.targets.length;
          task.remaining = Math.max(0, task.totalSends - task.currentIndex);
          task.progress = task.totalSends
            ? Math.min(100, Math.round((task.currentIndex / task.totalSends) * 100))
            : 0;
          task.currentMessage = composedMessage;
          task.currentTarget = target;

          try {
            const sock = await waitForSocketOpen(task.sessionName, 60000, task);
            await sock.sendMessage(target, { text: composedMessage });

            task.sent += 1;
            bulkLog(
              task,
              'Cycle ' + task.cycle + ' | Msg ' + task.currentIndex + '/' + task.totalSends + ' → ' + target
            );
          } catch (err) {
            if (task.stopRequested || !task.running || err.message === '__STOPPED__') {
              break;
            }

            task.failed += 1;
            bulkLog(
              task,
              'Cycle ' + task.cycle + ' | FAILED Msg ' + task.currentIndex + '/' + task.totalSends + ' → ' + target + ' | ' + err.message
            );
          }

          if (!task.running || task.stopRequested) break;

          await interruptibleDelay(task, task.delayMs);
        }
      }

      if (!task.running || task.stopRequested) break;

      bulkLog(task, 'Cycle ' + task.cycle + ' | COMPLETE | Restarting 24/7 loop...');
      await interruptibleDelay(task, 1000);
    }
  } catch (err) {
    bulkLog(task, 'FATAL | ' + err.message);
  } finally {
    task.running = false;
    task.stopRequested = true;
    task.endedAt = Date.now();
    bulkLog(
      task,
      'Bulk loop STOPPED | Cycle ' + task.cycle + ' | Sent ' + task.sent + ' | Failed ' + task.failed
    );
  }
}

function buildBulkStatus() {
  const task = bulkTask;
  const running = !!(task && task.running);

  return {
    running,
    stopped: !running,
    session: task ? task.sessionName : activeSessionName,
    targetMode: task ? task.mode : null,
    sent: task ? task.sent : 0,
    failed: task ? task.failed : 0,
    cycle: task ? task.cycle : 0,
    messages: task ? task.messages.length : 0,
    remaining: task ? task.remaining : 0,
    progress: task ? task.progress : 0,
    currentMessage: task ? task.currentMessage : '—',
    currentTarget: task ? task.currentTarget : '—',
    totalSends: task ? task.totalSends : 0,
    currentIndex: task ? task.currentIndex : 0,
    targetCount: task ? task.targets.length : 0,
    delaySeconds: task ? Math.round(task.delayMs / 1000) : 3,
    uptimeSeconds:
      task && task.startedAt
        ? Math.floor(((task.endedAt || Date.now()) - task.startedAt) / 1000)
        : 0,
    logs: getMergedLogs(),
    logSeq: globalLogSeq,
  };
}

/* -------------------------------------------------------------------------- */
/* Multer                                                                     */
/* -------------------------------------------------------------------------- */

const upload = multer({
  storage: multer.memoryStorage(),
  limits: {
    fileSize: MAX_TXT_BYTES,
    files: 1,
  },
  fileFilter: (req, file, cb) => {
    if (!/\.txt$/i.test(file.originalname || '')) {
      return cb(Boom.badRequest('Only .txt files are allowed.'));
    }
    cb(null, true);
  },
});

/* -------------------------------------------------------------------------- */
/* API routes                                                                 */
/* -------------------------------------------------------------------------- */

app.get(
  '/api/status',
  asyncHandler(async (req, res) => {
    const names = await listSessionNames();
    const active = activeSessionName ? await getSession(activeSessionName) : null;

    const sessionList = [];
    for (const name of names) {
      const pairedFromDisk = await isSessionPairedFromDisk(name);
      const inMemory = sessions.get(name);
      let paired = pairedFromDisk;
      if (inMemory && inMemory.authState && inMemory.authState.creds) {
        paired = inMemory.authState.creds.registered === true || pairedFromDisk;
      }

      sessionList.push({
        name,
        active: name === activeSessionName,
        paired,
      });
    }

    const activePaired = active
      ? Boolean(
          (active.authState && active.authState.creds && active.authState.creds.registered) ||
            active.meta.paired ||
            (await isSessionPairedFromDisk(active.name))
        )
      : false;

    res.json({
      ok: true,
      activeSession: activeSessionName,
      sessions: sessionList,
      session: active
        ? {
            name: active.name,
            connected: active.connected,
            paired: activePaired,
            pairingRequested: Boolean(active.meta.pairingRequested),
            pairingCode: active.meta.pairingCode || null,
            pairingCodeGeneratedAt: active.meta.pairingCodeGeneratedAt || null,
            phoneNumber: active.meta.phoneNumber || null,
            qrAvailable: Boolean(active.qrReceivedAt && Date.now() - active.qrReceivedAt < 60000),
            lastError: active.lastError || null,
          }
        : null,
      uptimeSeconds: Math.floor(process.uptime()),
      bulkRunning: Boolean(bulkTask && bulkTask.running),
    });
  })
);

app.post(
  '/api/sessions/create',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.name || req.body.session);
    const existing = await listSessionNames();

    if (existing.includes(name)) {
      throw Boom.conflict('Session "' + name + '" already exists.');
    }

    const dir = path.join(SESSIONS_ROOT, name);
    await fsp.mkdir(dir, { recursive: true });

    const session = await getSession(name);
    const passwordFields = makePasswordFields(req.body.password);

    session.meta = Object.assign(defaultMeta(), passwordFields, {
      createdAt: new Date().toISOString(),
    });
    await writeMeta(session);

    pushSystemLog('Session created: ' + name);
    res.json({ ok: true, session: name });
  })
);

app.post(
  '/api/sessions/switch',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.name || req.body.session);
    const target = await getSession(name);

    authorizeSession(target, req);

    if (activeSessionName === target.name) {
      return res.json({ ok: true, activeSession: activeSessionName, switched: false });
    }

    if (bulkTask && bulkTask.running) {
      throw Boom.conflict('Stop the bulk loop before switching sessions.');
    }

    await switchActiveSession(target.name);
    res.json({ ok: true, activeSession: activeSessionName, switched: true });
  })
);

app.post(
  '/api/pair',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.session || req.body.name || activeSessionName);
    const session = await getSession(name);

    authorizeSession(session, req);

    const phone = normalizePhone(req.body.phone || req.body.phoneNumber);

    if (activeSessionName !== session.name) {
      if (bulkTask && bulkTask.running) {
        throw Boom.conflict('Stop the bulk loop before switching sessions.');
      }
      await switchActiveSession(session.name);
    }

    await connectSession(session.name);

    if (session.authState && session.authState.creds && session.authState.creds.registered) {
      return res.json({
        ok: true,
        alreadyPaired: true,
        code: null,
        generatedAt: null,
        locked: Boolean(session.meta.pairingRequested),
        session: session.name,
      });
    }

    if (session.meta.pairingRequested && session.meta.pairingCode) {
      return res.json({
        ok: true,
        code: session.meta.pairingCode,
        generatedAt: session.meta.pairingCodeGeneratedAt,
        locked: true,
        session: session.name,
      });
    }

    if (session.meta.pairingRequested && !session.meta.pairingCode) {
      throw Boom.conflict('Pairing lock is active for this session. Use Logout to reset the session.');
    }

    session.pendingPairingPhone = phone;

    if (!session.qrReceivedAt || Date.now() - session.qrReceivedAt > 60000) {
      await waitForQr(session, 45000);
    }

    const code = await generatePairingCode(session, phone);

    if (!code) {
      throw Boom.conflict('This session is already registered. No pairing code was generated.');
    }

    res.json({
      ok: true,
      code,
      generatedAt: session.meta.pairingCodeGeneratedAt,
      locked: true,
      session: session.name,
    });
  })
);

app.post(
  '/api/logout',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.session || req.body.name || activeSessionName);
    const session = await getSession(name);

    authorizeSession(session, req);

    if (bulkTask && bulkTask.running && bulkTask.sessionName === session.name) {
      stopBulkTask('logout');
    }

    session.intentionalClose = true;
    session.autoReconnect = false;

    if (session.sock) {
      try {
        await session.sock.logout();
      } catch (err) {
        pushSystemLog('Logout request failed for ' + session.name + ' (continuing reset): ' + err.message);
      }
    }

    await stopSocket(session);
    await resetSessionDirectory(session);
    session.intentionalClose = false;
    session.autoReconnect = true;

    if (activeSessionName === session.name) {
      await connectSession(session.name);
    }

    pushSystemLog('Session logged out and reset: ' + session.name);
    res.json({ ok: true, session: session.name });
  })
);

app.get(
  '/api/groups',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.query.session || activeSessionName);
    const session = await getSession(name);

    if (!session.connected || !session.sock) {
      throw Boom.conflict('Session is not connected. Pair and connect the session first.');
    }

    const raw = await session.sock.groupFetchAllParticipating();
    const groups = Object.values(raw || {})
      .map((group) => ({
        jid: group.id || group.jid || '',
        subject: group.subject || 'Unnamed Group',
        size: Array.isArray(group.participants) ? group.participants.length : 0,
      }))
      .filter((group) => group.jid && group.jid.endsWith('@g.us'))
      .sort((a, b) => String(a.subject).localeCompare(String(b.subject)));

    res.json({ ok: true, session: session.name, groups });
  })
);

app.post(
  '/api/bulk/start',
  upload.single('file'),
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.session || activeSessionName);

    if (name !== activeSessionName) {
      throw Boom.conflict('Switch to session "' + name + '" before starting the bulk loop.');
    }

    const session = await getSession(name);
    authorizeSession(session, req);

    if (bulkTask && bulkTask.running) {
      throw Boom.conflict('A bulk loop is already running. Stop it first.');
    }

    if (!req.file) {
      throw Boom.badRequest('A .txt message file is required.');
    }

    const messages = parseMessageFile(req.file.buffer);
    if (!messages.length) {
      throw Boom.badRequest('The uploaded .txt file contains no non-empty message lines.');
    }

    const mode = String(req.body.targetMode || 'groups').toLowerCase() === 'numbers' ? 'numbers' : 'groups';
    let targets;

    if (mode === 'groups') {
      targets = parseGroupTargets(req.body.groups);
      if (!targets.length) {
        throw Boom.badRequest('Select at least one WhatsApp group.');
      }
    } else {
      targets = parseNumberTargets(req.body.numbers);
      if (!targets.length) {
        throw Boom.badRequest('Enter at least one valid phone number.');
      }
    }

    const parsedDelay = Number(req.body.delay);
    const delaySeconds = Math.max(3, Math.min(3600, Number.isFinite(parsedDelay) ? parsedDelay : 3));

    const task = {
      running: true,
      stopRequested: false,
      sessionName: name,
      mode,
      messages,
      targets,
      prefix: String(req.body.prefix || '').trim().slice(0, 200),
      suffix: String(req.body.suffix || '').trim().slice(0, 200),
      delayMs: Math.round(delaySeconds * 1000),
      sent: 0,
      failed: 0,
      cycle: 0,
      currentIndex: 0,
      totalSends: messages.length * targets.length,
      remaining: messages.length * targets.length,
      progress: 0,
      currentMessage: '',
      currentTarget: '',
      startedAt: Date.now(),
      endedAt: null,
      logs: [],
    };

    bulkTask = task;

    pushSystemLog(
      'Bulk loop ARMED | session=' + name + ' | messages=' + messages.length + ' | targets=' + targets.length + ' | delay=' + delaySeconds + 's'
    );

    runBulkLoop(task).catch((err) => {
      task.running = false;
      task.stopRequested = true;
      bulkLog(task, 'FATAL | ' + err.message);
    });

    res.json({ ok: true, status: buildBulkStatus() });
  })
);

app.post(
  '/api/bulk/stop',
  asyncHandler(async (req, res) => {
    const name = sanitizeSessionName(req.body.session || activeSessionName);
    const session = await getSession(name);
    authorizeSession(session, req);

    if (!bulkTask) {
      return res.json({ ok: true, stopped: false, status: buildBulkStatus() });
    }

    stopBulkTask('api');
    res.json({ ok: true, stopped: true, status: buildBulkStatus() });
  })
);

app.get(
  '/api/bulk/status',
  asyncHandler(async (req, res) => {
    res.json(Object.assign({ ok: true }, buildBulkStatus()));
  })
);

app.post(
  '/api/bulk/clear-logs',
  asyncHandler(async (req, res) => {
    systemLogs = [];
    if (bulkTask) bulkTask.logs = [];
    res.json({ ok: true, logSeq: globalLogSeq });
  })
);

/* -------------------------------------------------------------------------- */
/* Dashboard                                                                  */
/* -------------------------------------------------------------------------- */

const DASHBOARD_HTML = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0" />
<title>RK X RAJA | ELITE CYBER MATRIX PRO CONSOLE</title>
<link rel="preconnect" href="https://fonts.googleapis.com" />
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
<link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700;900&family=Rajdhani:wght@400;500;600;700&display=swap" rel="stylesheet" />
<style>
  :root {
    --bg: #05050a;
    --panel: #080d12;
    --panel-2: #0a1118;
    --neon: #10b981;
    --neon-bright: #34d399;
    --neon-dim: #065f46;
    --danger: #ef4444;
    --danger-dim: #7f1d1d;
    --text: #d1fae5;
    --muted: #6b7280;
    --line: rgba(16, 185, 129, 0.25);
    --line-strong: rgba(16, 185, 129, 0.55);
    --amber: #f59e0b;
  }

  * {
    box-sizing: border-box;
  }

  html, body {
    margin: 0;
    padding: 0;
    min-height: 100%;
  }

  body {
    background:
      radial-gradient(circle at 20% 0%, rgba(16, 185, 129, 0.09), transparent 35%),
      radial-gradient(circle at 85% 20%, rgba(52, 211, 153, 0.06), transparent 30%),
      linear-gradient(rgba(16, 185, 129, 0.025) 1px, transparent 1px),
      linear-gradient(90deg, rgba(16, 185, 129, 0.025) 1px, transparent 1px),
      var(--bg);
    background-size: auto, auto, 32px 32px, 32px 32px, auto;
    color: var(--text);
    font-family: 'Rajdhani', 'Segoe UI', sans-serif;
    overflow-x: hidden;
  }

  #matrixRain {
    position: fixed;
    inset: 0;
    z-index: 0;
    opacity: 0.28;
    pointer-events: none;
  }

  .scanlines {
    position: fixed;
    inset: 0;
    z-index: 1;
    pointer-events: none;
    background: repeating-linear-gradient(
      0deg,
      rgba(0, 0, 0, 0) 0px,
      rgba(0, 0, 0, 0) 2px,
      rgba(0, 0, 0, 0.12) 3px,
      rgba(0, 0, 0, 0) 4px
    );
    mix-blend-mode: multiply;
  }

  .shell {
    position: relative;
    z-index: 2;
    width: min(1480px, calc(100% - 28px));
    margin: 0 auto;
    padding: 22px 0 40px;
  }

  .top-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 18px;
    border: 1px solid var(--line);
    background: linear-gradient(135deg, rgba(8, 13, 18, 0.96), rgba(5, 10, 14, 0.9));
    padding: 18px 22px;
    clip-path: polygon(0 0, calc(100% - 22px) 0, 100% 22px, 100% 100%, 22px 100%, 0 calc(100% - 22px));
    box-shadow: 0 0 28px rgba(16, 185, 129, 0.08), inset 0 0 40px rgba(16, 185, 129, 0.02);
  }

  .brand-row {
    display: flex;
    align-items: center;
    gap: 16px;
  }

  .logo-mark {
    width: 54px;
    height: 54px;
    border: 1px solid var(--neon);
    display: grid;
    place-items: center;
    font-family: 'Orbitron', sans-serif;
    font-size: 17px;
    font-weight: 900;
    color: var(--neon-bright);
    text-shadow: 0 0 14px rgba(16, 185, 129, 0.9);
    background: rgba(16, 185, 129, 0.06);
    box-shadow: 0 0 20px rgba(16, 185, 129, 0.16), inset 0 0 18px rgba(16, 185, 129, 0.06);
  }

  .brand-title {
    font-family: 'Orbitron', sans-serif;
    font-size: clamp(1.2rem, 2.2vw, 1.8rem);
    font-weight: 900;
    letter-spacing: 0.1em;
    color: #ecfdf5;
    text-shadow: 0 0 18px rgba(16, 185, 129, 0.55);
    line-height: 1.05;
  }

  .brand-title .x {
    color: var(--neon-bright);
    text-shadow: 0 0 24px rgba(52, 211, 153, 0.95);
  }

  .brand-sub {
    margin: 5px 0 0;
    font-size: 0.78rem;
    letter-spacing: 0.3em;
    color: var(--muted);
    text-transform: uppercase;
  }

  .header-status {
    display: inline-flex;
    align-items: center;
    gap: 9px;
    font-family: 'Orbitron', sans-serif;
    font-size: 0.7rem;
    letter-spacing: 0.14em;
    color: var(--muted);
    border: 1px solid var(--line);
    padding: 9px 13px;
    background: rgba(0, 0, 0, 0.35);
  }

  .dot {
    width: 8px;
    height: 8px;
    border-radius: 50%;
    background: var(--muted);
    box-shadow: 0 0 10px var(--muted);
  }

  .dot.online {
    background: var(--neon-bright);
    box-shadow: 0 0 12px var(--neon-bright);
    animation: pulse 1.4s infinite;
  }

  .dot.danger {
    background: var(--danger);
    box-shadow: 0 0 12px var(--danger);
  }

  @keyframes pulse {
    0%, 100% { opacity: 1; transform: scale(1); }
    50% { opacity: 0.45; transform: scale(0.82); }
  }

  .tabs {
    display: flex;
    gap: 8px;
    margin: 16px 0 20px;
    flex-wrap: wrap;
  }

  .tab-btn {
    border: 1px solid var(--line);
    background: rgba(8, 13, 18, 0.8);
    color: var(--muted);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.68rem;
    letter-spacing: 0.16em;
    padding: 12px 18px;
    cursor: pointer;
    transition: 160ms ease;
    clip-path: polygon(0 0, calc(100% - 10px) 0, 100% 10px, 100% 100%, 10px 100%, 0 calc(100% - 10px));
  }

  .tab-btn:hover {
    color: var(--neon-bright);
    border-color: var(--line-strong);
  }

  .tab-btn.active {
    color: #02110c;
    background: linear-gradient(135deg, var(--neon-bright), var(--neon));
    border-color: var(--neon-bright);
    box-shadow: 0 0 22px rgba(16, 185, 129, 0.25);
    font-weight: 700;
  }

  .tab-panel {
    display: none;
  }

  .tab-panel.active {
    display: block;
    animation: fadeIn 180ms ease;
  }

  @keyframes fadeIn {
    from { opacity: 0; transform: translateY(4px); }
    to { opacity: 1; transform: translateY(0); }
  }

  .card {
    border: 1px solid var(--line);
    background: linear-gradient(160deg, rgba(8, 13, 18, 0.96), rgba(4, 8, 12, 0.94));
    padding: 18px;
    position: relative;
    clip-path: polygon(0 0, calc(100% - 16px) 0, 100% 16px, 100% 100%, 16px 100%, 0 calc(100% - 16px));
    box-shadow: 0 0 28px rgba(0, 0, 0, 0.35), inset 0 0 40px rgba(16, 185, 129, 0.018);
  }

  .card::before {
    content: '';
    position: absolute;
    left: 0;
    top: 0;
    width: 60px;
    height: 2px;
    background: var(--neon);
    box-shadow: 0 0 12px var(--neon);
  }

  .card-title {
    margin: 0 0 16px;
    font-family: 'Orbitron', sans-serif;
    font-size: 0.78rem;
    letter-spacing: 0.18em;
    color: var(--neon-bright);
    text-transform: uppercase;
  }

  .grid-2 {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 16px;
  }

  .grid-3 {
    display: grid;
    grid-template-columns: repeat(3, minmax(0, 1fr));
    gap: 14px;
  }

  .field {
    margin-bottom: 14px;
  }

  .field:last-child {
    margin-bottom: 0;
  }

  label {
    display: block;
    margin-bottom: 7px;
    font-family: 'Orbitron', sans-serif;
    font-size: 0.6rem;
    letter-spacing: 0.14em;
    color: var(--muted);
    text-transform: uppercase;
  }

  input[type="text"],
  input[type="password"],
  input[type="number"],
  select,
  textarea {
    width: 100%;
    border: 1px solid rgba(16, 185, 129, 0.2);
    background: rgba(2, 8, 7, 0.86);
    color: var(--text);
    padding: 11px 12px;
    font-family: 'Rajdhani', sans-serif;
    font-size: 0.98rem;
    outline: none;
    transition: 150ms ease;
    border-radius: 0;
  }

  input:focus,
  select:focus,
  textarea:focus {
    border-color: var(--neon-bright);
    box-shadow: 0 0 0 1px rgba(16, 185, 129, 0.25), 0 0 18px rgba(16, 185, 129, 0.12);
  }

  textarea {
    min-height: 132px;
    resize: vertical;
    line-height: 1.45;
  }

  select {
    cursor: pointer;
  }

  input[type="file"] {
    width: 100%;
    border: 1px dashed rgba(16, 185, 129, 0.35);
    background: rgba(2, 8, 7, 0.55);
    color: var(--muted);
    padding: 14px;
    font-family: 'Rajdhani', sans-serif;
    cursor: pointer;
  }

  input[type="file"]::file-selector-button {
    border: 1px solid var(--line-strong);
    background: rgba(16, 185, 129, 0.08);
    color: var(--neon-bright);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.6rem;
    letter-spacing: 0.08em;
    padding: 8px 11px;
    cursor: pointer;
    margin-right: 12px;
  }

  .btn-row {
    display: flex;
    gap: 9px;
    flex-wrap: wrap;
  }

  .btn {
    border: 1px solid var(--line-strong);
    background: rgba(16, 185, 129, 0.07);
    color: var(--neon-bright);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.62rem;
    letter-spacing: 0.1em;
    padding: 11px 15px;
    cursor: pointer;
    transition: 150ms ease;
    text-transform: uppercase;
    clip-path: polygon(0 0, calc(100% - 8px) 0, 100% 8px, 100% 100%, 8px 100%, 0 calc(100% - 8px));
  }

  .btn:hover:not(:disabled) {
    background: var(--neon);
    color: #02110c;
    box-shadow: 0 0 20px rgba(16, 185, 129, 0.35);
  }

  .btn:disabled {
    opacity: 0.35;
    cursor: not-allowed;
  }

  .btn-primary {
    background: linear-gradient(135deg, var(--neon-bright), #059669);
    color: #02110c;
    border-color: var(--neon-bright);
    font-weight: 700;
  }

  .btn-primary:hover:not(:disabled) {
    background: var(--neon-bright);
    box-shadow: 0 0 28px rgba(52, 211, 153, 0.5);
  }

  .btn-danger {
    background: rgba(239, 68, 68, 0.1);
    color: #fecaca;
    border-color: rgba(239, 68, 68, 0.55);
  }

  .btn-danger:hover:not(:disabled) {
    background: var(--danger);
    color: #fff;
    box-shadow: 0 0 24px rgba(239, 68, 68, 0.4);
  }

  .btn-wide {
    width: 100%;
    padding: 14px;
    font-size: 0.72rem;
  }

  .small-note {
    margin-top: 12px;
    color: var(--muted);
    font-size: 0.78rem;
    line-height: 1.4;
  }

  .pair-code {
    min-height: 120px;
    display: grid;
    place-items: center;
    border: 1px solid var(--line);
    background: radial-gradient(circle at center, rgba(16, 185, 129, 0.09), rgba(0, 0, 0, 0.2));
    margin: 6px 0 10px;
    position: relative;
    overflow: hidden;
  }

  .pair-code::after {
    content: '';
    position: absolute;
    inset: 0;
    background: repeating-linear-gradient(0deg, transparent 0 3px, rgba(16, 185, 129, 0.025) 4px);
    pointer-events: none;
  }

  #pairingCode {
    font-family: 'Orbitron', sans-serif;
    font-size: clamp(1.5rem, 4vw, 2.8rem);
    letter-spacing: 0.24em;
    color: var(--neon-bright);
    text-shadow: 0 0 24px rgba(16, 185, 129, 0.85);
    z-index: 1;
    text-align: center;
    word-break: break-all;
    padding: 12px;
  }

  #pairingMeta {
    color: var(--muted);
    font-size: 0.8rem;
    min-height: 20px;
  }

  .session-chips {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    margin-top: 14px;
  }

  .chip {
    border: 1px solid var(--line);
    background: rgba(16, 185, 129, 0.04);
    color: var(--muted);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.58rem;
    letter-spacing: 0.08em;
    padding: 7px 10px;
    cursor: pointer;
  }

  .chip.active {
    color: var(--neon-bright);
    border-color: var(--neon-bright);
    background: rgba(16, 185, 129, 0.1);
  }

  .preview-box {
    border: 1px solid rgba(16, 185, 129, 0.15);
    background: rgba(2, 8, 7, 0.6);
    padding: 11px;
    min-height: 84px;
    max-height: 150px;
    overflow: auto;
    font-size: 0.82rem;
    color: var(--muted);
    line-height: 1.45;
    white-space: pre-wrap;
    word-break: break-word;
  }

  .preview-box strong {
    color: var(--neon-bright);
  }

  .dim {
    color: #4b5563;
  }

  .target-tabs {
    display: flex;
    gap: 8px;
    margin-bottom: 14px;
    flex-wrap: wrap;
  }

  .target-tab {
    border: 1px solid var(--line);
    background: rgba(8, 13, 18, 0.8);
    color: var(--muted);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.6rem;
    letter-spacing: 0.1em;
    padding: 10px 13px;
    cursor: pointer;
  }

  .target-tab.active {
    color: #02110c;
    background: var(--neon);
    border-color: var(--neon-bright);
    font-weight: 700;
  }

  .hidden {
    display: none !important;
  }

  .group-list {
    max-height: 292px;
    overflow: auto;
    border: 1px solid rgba(16, 185, 129, 0.15);
    background: rgba(2, 8, 7, 0.55);
    padding: 6px;
  }

  .group-row {
    display: flex;
    align-items: center;
    gap: 10px;
    padding: 9px 8px;
    border-bottom: 1px solid rgba(16, 185, 129, 0.08);
    cursor: pointer;
    font-size: 0.9rem;
  }

  .group-row:last-child {
    border-bottom: none;
  }

  .group-row:hover {
    background: rgba(16, 185, 129, 0.06);
  }

  .group-row input {
    accent-color: var(--neon);
    width: 15px;
    height: 15px;
    flex: 0 0 auto;
  }

  .group-name {
    flex: 1;
    min-width: 0;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }

  .group-meta {
    color: var(--muted);
    font-size: 0.72rem;
    white-space: nowrap;
  }

  .empty {
    padding: 20px;
    text-align: center;
    color: var(--muted);
    font-size: 0.82rem;
  }

  .validation {
    margin-top: 8px;
    font-size: 0.8rem;
    color: var(--muted);
    min-height: 20px;
  }

  .validation.bad {
    color: #fca5a5;
  }

  .validation.good {
    color: var(--neon-bright);
  }

  .stats-panel {
    border: 1px solid var(--line-strong);
    background: linear-gradient(160deg, rgba(4, 10, 9, 0.98), rgba(2, 6, 5, 0.96));
    padding: 14px;
    box-shadow: 0 0 30px rgba(16, 185, 129, 0.08), inset 0 0 40px rgba(16, 185, 129, 0.02);
  }

  .stats-row {
    display: grid;
    gap: 8px;
    margin-bottom: 8px;
  }

  .stats-row-3 {
    grid-template-columns: repeat(3, minmax(0, 1fr));
  }

  .stats-row-2 {
    grid-template-columns: repeat(2, minmax(0, 1fr));
  }

  .stat-cell {
    border: 1px solid rgba(16, 185, 129, 0.14);
    background: rgba(0, 0, 0, 0.35);
    padding: 11px 12px;
    min-height: 66px;
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    position: relative;
    overflow: hidden;
  }

  .stat-cell::before {
    content: '';
    position: absolute;
    left: 0;
    top: 0;
    bottom: 0;
    width: 2px;
    background: rgba(16, 185, 129, 0.5);
  }

  .stat-label {
    font-family: 'Orbitron', sans-serif;
    font-size: 0.52rem;
    letter-spacing: 0.14em;
    color: var(--muted);
    text-transform: uppercase;
  }

  .stat-value {
    font-family: 'Orbitron', sans-serif;
    font-size: clamp(0.95rem, 1.6vw, 1.24rem);
    font-weight: 700;
    color: var(--neon-bright);
    text-shadow: 0 0 12px rgba(16, 185, 129, 0.25);
    word-break: break-word;
    line-height: 1.2;
  }

  .stat-value.green {
    color: var(--neon-bright);
  }

  .stat-value.amber {
    color: var(--amber);
  }

  .stat-value.red {
    color: #f87171;
  }

  .stat-value.muted {
    color: var(--muted);
  }

  .stat-value-small {
    font-family: 'Rajdhani', sans-serif;
    font-size: 0.92rem;
    color: var(--text);
    line-height: 1.28;
    max-height: 46px;
    overflow: hidden;
    word-break: break-word;
  }

  .stat-cell.wide {
    min-height: 74px;
  }

  .progress-track {
    height: 9px;
    border: 1px solid rgba(16, 185, 129, 0.28);
    background: rgba(0, 0, 0, 0.55);
    margin-top: 6px;
    overflow: hidden;
  }

  #progressFill {
    height: 100%;
    width: 0%;
    background: linear-gradient(90deg, #047857, var(--neon-bright));
    box-shadow: 0 0 16px rgba(52, 211, 153, 0.8);
    transition: width 280ms ease;
  }

  .log-head {
    display: flex;
    justify-content: space-between;
    align-items: center;
    gap: 12px;
    flex-wrap: wrap;
    margin-bottom: 10px;
  }

  .log-head h2 {
    margin: 0;
    font-family: 'Orbitron', sans-serif;
    font-size: 0.72rem;
    letter-spacing: 0.16em;
    color: var(--neon-bright);
  }

  .log-box {
    height: 280px;
    overflow: auto;
    border: 1px solid rgba(16, 185, 129, 0.18);
    background:
      linear-gradient(rgba(16, 185, 129, 0.018) 1px, transparent 1px),
      rgba(0, 0, 0, 0.62);
    background-size: 100% 22px;
    padding: 10px 12px;
    font-family: 'Courier New', monospace;
    font-size: 0.76rem;
    line-height: 1.55;
    color: #86efac;
  }

  .log-line {
    padding: 1px 0;
    border-bottom: 1px solid rgba(16, 185, 129, 0.035);
    white-space: pre-wrap;
    word-break: break-word;
  }

  .log-line.send {
    color: #6ee7b7;
  }

  .log-line.error {
    color: #fca5a5;
  }

  .log-line.system {
    color: #9ca3af;
  }

  .toast {
    position: fixed;
    top: 18px;
    left: 50%;
    transform: translate(-50%, -120%);
    z-index: 9999;
    border: 1px solid var(--neon-bright);
    background: rgba(2, 15, 10, 0.96);
    color: var(--neon-bright);
    font-family: 'Orbitron', sans-serif;
    font-size: 0.68rem;
    letter-spacing: 0.12em;
    padding: 13px 22px;
    box-shadow: 0 0 30px rgba(16, 185, 129, 0.3), inset 0 0 20px rgba(16, 185, 129, 0.05);
    transition: transform 220ms ease, opacity 220ms ease;
    opacity: 0;
    pointer-events: none;
    text-align: center;
    max-width: calc(100vw - 30px);
  }

  .toast.show {
    transform: translate(-50%, 0);
    opacity: 1;
  }

  .big-actions {
    display: flex;
    gap: 10px;
    flex-wrap: wrap;
    margin-top: 14px;
  }

  .big-actions .btn {
    flex: 1 1 220px;
    padding: 15px;
    font-size: 0.72rem;
  }

  .footer {
    margin-top: 18px;
    padding: 12px 4px;
    display: flex;
    justify-content: space-between;
    gap: 12px;
    flex-wrap: wrap;
    color: #374151;
    font-size: 0.7rem;
    letter-spacing: 0.08em;
    font-family: 'Orbitron', sans-serif;
  }

  @media (max-width: 980px) {
    .grid-2,
    .grid-3 {
      grid-template-columns: 1fr;
    }

    .stats-row-3 {
      grid-template-columns: repeat(3, minmax(0, 1fr));
    }
  }

  @media (max-width: 640px) {
    .shell {
      width: calc(100% - 16px);
      padding-top: 12px;
    }

    .top-header {
      align-items: flex-start;
      flex-direction: column;
      padding: 14px;
    }

    .stats-row-3,
    .stats-row-2 {
      grid-template-columns: 1fr;
    }

    .brand-sub {
      letter-spacing: 0.16em;
    }

    .stat-value {
      font-size: 1rem;
    }

    .log-box {
      height: 230px;
    }
  }
</style>
</head>
<body>
<canvas id="matrixRain"></canvas>
<div class="scanlines"></div>
<div id="toast" class="toast"></div>

<div class="shell">
  <header class="top-header">
    <div class="brand-row">
      <div class="logo-mark">RK</div>
      <div>
        <div class="brand-title">RK <span class="x">X</span> RAJA</div>
        <p class="brand-sub">Elite Cyber Matrix Pro Console</p>
      </div>
    </div>
    <div class="header-status">
      <span id="globalDot" class="dot"></span>
      <span id="globalStatus">STANDBY</span>
    </div>
  </header>

  <nav class="tabs">
    <button id="tabBtnDashboard" class="tab-btn active" data-tab="tab-dashboard">01 &nbsp; DASHBOARD &amp; PAIRING</button>
    <button id="tabBtnBulk" class="tab-btn" data-tab="tab-bulk">02 &nbsp; BULK SENDER HUB</button>
  </nav>

  <main>
    <section id="tab-dashboard" class="tab-panel active">
      <div class="grid-2">
        <div class="card">
          <h2 class="card-title">Session Control</h2>

          <div class="field">
            <label for="sessionName">Session Name</label>
            <input id="sessionName" type="text" placeholder="session1" value="session1" autocomplete="off" />
          </div>

          <div class="field">
            <label for="pairPassword">Password (Optional)</label>
            <input id="pairPassword" type="password" placeholder="Session password" autocomplete="current-password" />
          </div>

          <div class="field">
            <label for="phoneNumber">Phone Number With Country Code</label>
            <input id="phoneNumber" type="text" placeholder="919876543210" autocomplete="off" inputmode="numeric" />
          </div>

          <div class="btn-row">
            <button id="pairBtn" class="btn btn-primary">Get Pairing Code</button>
            <button id="createSessionBtn" class="btn">Create / Save Session</button>
            <button id="logoutBtn" class="btn btn-danger">Logout</button>
          </div>

          <div class="small-note">
            Pairing codes are generated ONLY once per session. Network drops and reconnects will NOT rotate your code.
          </div>

          <div id="sessionChips" class="session-chips"></div>
        </div>

        <div class="card">
          <h2 class="card-title">Pairing Uplink</h2>
          <div class="pair-code">
            <div id="pairingCode">------</div>
          </div>
          <div id="pairingMeta">No active pairing code.</div>

          <div class="btn-row" style="margin-top:14px;">
            <button id="copyCodeBtn" class="btn">Copy Code</button>
            <button id="refreshStatusBtn" class="btn">Refresh Status</button>
          </div>

          <div class="small-note" id="connectionDetail">
            Waiting for session telemetry...
          </div>
        </div>
      </div>
    </section>

    <section id="tab-bulk" class="tab-panel">
      <div class="card" style="margin-bottom:16px;">
        <h2 class="card-title">Bulk Sender Configuration</h2>

        <div class="grid-3">
          <div class="field">
            <label for="bulkSessionSelect">Active Session</label>
            <select id="bulkSessionSelect"></select>
          </div>

          <div class="field">
            <label for="messageFile">Message File (.txt)</label>
            <input id="messageFile" type="file" accept=".txt" />
            <div id="filePreview" class="preview-box" style="margin-top:8px;">No file selected.</div>
          </div>

          <div class="field">
            <label for="prefixInput">Hater Name (Optional Prefix)</label>
            <input id="prefixInput" type="text" placeholder="Optional prefix" autocomplete="off" />
            <label for="delayInput" style="margin-top:12px;">Delay (Seconds) - Minimum 3s</label>
            <input id="delayInput" type="number" min="3" max="3600" step="1" value="3" />
            <label for="suffixInput" style="margin-top:12px;">Last Hater Name (Optional Suffix)</label>
            <input id="suffixInput" type="text" placeholder="Optional suffix" autocomplete="off" />
          </div>
        </div>
      </div>

      <div class="card" style="margin-bottom:16px;">
        <h2 class="card-title">Target Selector</h2>

        <div class="target-tabs">
          <button id="targetGroupsBtn" class="target-tab active" data-target="groups">Send to Groups</button>
          <button id="targetNumbersBtn" class="target-tab" data-target="numbers">Send to Numbers</button>
        </div>

        <div id="groupsView">
          <div class="btn-row" style="margin-bottom:10px;">
            <button id="fetchGroupsBtn" class="btn">Fetch Groups</button>
            <button id="selectAllGroupsBtn" class="btn">All</button>
            <button id="clearGroupsBtn" class="btn">Clear</button>
          </div>
          <div id="groupList" class="group-list">
            <div class="empty">No groups loaded. Pair a session, then click FETCH GROUPS.</div>
          </div>
          <div class="validation" id="groupValidation">0 selected</div>
        </div>

        <div id="numbersView" class="hidden">
          <div class="field">
            <label for="numbersInput">Phone Numbers (comma or newline separated)</label>
            <textarea id="numbersInput" placeholder="919876543210&#10;918765432109, 447700900123"></textarea>
          </div>
          <div class="validation" id="numbersValidation">Enter at least one valid number.</div>
        </div>
      </div>

      <div class="card" style="margin-bottom:16px;">
        <h2 class="card-title">Live Matrix Stats</h2>

        <div class="stats-panel">
          <div class="stats-row stats-row-3">
            <div class="stat-cell">
              <span class="stat-label">Status</span>
              <span id="statStatus" class="stat-value muted">STANDBY</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Paired</span>
              <span id="statPaired" class="stat-value muted">NO</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Uptime</span>
              <span id="statUptime" class="stat-value">00:00:00</span>
            </div>
          </div>

          <div class="stats-row stats-row-3">
            <div class="stat-cell">
              <span class="stat-label">Sent</span>
              <span id="statSent" class="stat-value green">0</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Failed</span>
              <span id="statFailed" class="stat-value red">0</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Cycle</span>
              <span id="statCycle" class="stat-value">0</span>
            </div>
          </div>

          <div class="stats-row stats-row-3">
            <div class="stat-cell">
              <span class="stat-label">Messages</span>
              <span id="statMessages" class="stat-value">0</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Remaining</span>
              <span id="statRemaining" class="stat-value amber">0</span>
            </div>
            <div class="stat-cell">
              <span class="stat-label">Progress</span>
              <span id="statProgress" class="stat-value green">0%</span>
            </div>
          </div>

          <div class="stats-row stats-row-2">
            <div class="stat-cell wide">
              <span class="stat-label">Current Message</span>
              <span id="statCurrentMessage" class="stat-value-small muted">—</span>
            </div>
            <div class="stat-cell wide">
              <span class="stat-label">Current Target</span>
              <span id="statCurrentTarget" class="stat-value-small muted">—</span>
            </div>
          </div>

          <div class="progress-track">
            <div id="progressFill"></div>
          </div>
        </div>

        <div class="big-actions">
          <button id="startBulkBtn" class="btn btn-primary">Start 24/7 Loop</button>
          <button id="stopBulkBtn" class="btn btn-danger">Emergency Stop</button>
        </div>
      </div>

      <div class="card">
        <div class="log-head">
          <h2>Live Matrix Cyber Log</h2>
          <div class="btn-row">
            <button id="clearLogBtn" class="btn">Clear Log</button>
            <button id="stopTaskBtn" class="btn btn-danger">Stop Task</button>
          </div>
        </div>
        <div id="logBox" class="log-box"></div>
      </div>
    </section>
  </main>

  <footer class="footer">
    <span>RK X RAJA // MATRIX NODE</span>
    <span>DIRECT CONNECTION // NO PROXY</span>
  </footer>
</div>

<script>
(function () {
  'use strict';

  var state = {
    activeSession: '',
    sessions: [],
    groups: [],
    targetMode: 'groups',
    selectedGroups: new Set(),
    file: null,
    fileMessages: [],
    lastLogSeq: 0,
    lastStatus: null,
    polling: false
  };

  function el(id) {
    return document.getElementById(id);
  }

  function esc(value) {
    return String(value === undefined || value === null ? '' : value).replace(/[&<>"']/g, function (ch) {
      return {
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        '"': '&quot;',
        "'": '&#39;'
      }[ch];
    });
  }

  function showToast(message, duration) {
    var toast = el('toast');
    toast.textContent = message;
    toast.classList.add('show');
    window.clearTimeout(showToast._timer);
    showToast._timer = window.setTimeout(function () {
      toast.classList.remove('show');
    }, duration || 1000);
  }

  function formatHMS(seconds) {
    var total = Math.max(0, Math.floor(Number(seconds) || 0));
    var h = Math.floor(total / 3600);
    var m = Math.floor((total % 3600) / 60);
    var s = total % 60;
    return String(h).padStart(2, '0') + ':' + String(m).padStart(2, '0') + ':' + String(s).padStart(2, '0');
  }

  async function api(path, options) {
    var opts = options || {};
    var response = await fetch(path, opts);
    var data = await response.json().catch(function () {
      return {};
    });
    if (!response.ok) {
      throw new Error(data.error || ('HTTP ' + response.status));
    }
    return data;
  }

  function getPassword() {
    return el('pairPassword').value;
  }

  function setGlobalStatus(online, text) {
    var dot = el('globalDot');
    dot.className = 'dot ' + (online ? 'online' : 'danger');
    el('globalStatus').textContent = text;
  }

  function switchTab(tabId) {
    document.querySelectorAll('.tab-btn').forEach(function (btn) {
      btn.classList.toggle('active', btn.getAttribute('data-tab') === tabId);
    });
    document.querySelectorAll('.tab-panel').forEach(function (panel) {
      panel.classList.toggle('active', panel.id === tabId);
    });
  }

  function renderSessions(sessions) {
    var select = el('bulkSessionSelect');
    var previous = select.value || state.activeSession;

    select.innerHTML = '';
    sessions.forEach(function (session) {
      var option = document.createElement('option');
      option.value = session.name;
      option.textContent = session.name + (session.paired ? ' [PAIRED]' : ' [UNPAIRED]');
      select.appendChild(option);
    });

    if (previous) select.value = previous;
    if (state.activeSession) select.value = state.activeSession;

    var chips = el('sessionChips');
    chips.innerHTML = '';
    sessions.forEach(function (session) {
      var button = document.createElement('button');
      button.type = 'button';
      button.className = 'chip' + (session.active ? ' active' : '');
      button.textContent = session.name + (session.paired ? ' // LINKED' : ' // OPEN');
      button.addEventListener('click', function () {
        el('sessionName').value = session.name;
        if (!session.active) {
          switchSession(session.name);
        }
      });
      chips.appendChild(button);
    });
  }

  function updatePairingUI(data) {
    var session = data.session;
    if (!session) return;

    el('statPaired').textContent = session.paired ? 'YES' : 'NO';
    el('statPaired').className = 'stat-value ' + (session.paired ? 'green' : 'red');

    if (session.pairingCode) {
      el('pairingCode').textContent = session.pairingCode;
      el('pairingMeta').textContent =
        'Generated ' +
        (session.pairingCodeGeneratedAt ? new Date(session.pairingCodeGeneratedAt).toLocaleString() : 'just now') +
        ' | LOCKED: code will not rotate on reconnect.';
    } else if (session.paired) {
      el('pairingCode').textContent = 'LINKED';
      el('pairingMeta').textContent = 'This session is paired and ready.';
    } else {
      el('pairingCode').textContent = '------';
      el('pairingMeta').textContent = 'No active pairing code.';
    }

    var details = [];
    details.push('SESSION: ' + session.name.toUpperCase());
    details.push('CONNECTION: ' + (session.connected ? 'ONLINE' : 'OFFLINE'));
    details.push('PAIRED: ' + (session.paired ? 'YES' : 'NO'));
    details.push('QR STREAM: ' + (session.qrAvailable ? 'READY' : 'WAITING'));
    if (session.phoneNumber) details.push('PHONE: ' + session.phoneNumber);
    if (session.lastError) details.push('LAST ERROR: ' + session.lastError);
    el('connectionDetail').textContent = details.join('  //  ');
  }

  async function loadStatus() {
    var data = await api('/api/status');

    state.lastStatus = data;
    state.activeSession = data.activeSession;
    state.sessions = data.sessions || [];

    if (!el('sessionName').value) {
      el('sessionName').value = data.activeSession || '';
    }

    renderSessions(state.sessions);
    updatePairingUI(data);

    el('statUptime').textContent = formatHMS(data.uptimeSeconds);
    setGlobalStatus(true, data.session && data.session.connected ? 'UPLINK ONLINE' : 'CONSOLE ONLINE');

    if (data.session && data.session.paired) {
      el('statPaired').textContent = 'YES';
      el('statPaired').className = 'stat-value green';
    }

    return data;
  }

  function updateBulkUI(data) {
    var running = !!data.running;

    el('statStatus').textContent = running ? 'RUNNING 24/7' : 'STANDBY';
    el('statStatus').className = 'stat-value ' + (running ? 'green' : 'muted');

    el('statSent').textContent = data.sent || 0;
    el('statFailed').textContent = data.failed || 0;
    el('statCycle').textContent = data.cycle || 0;
    el('statMessages').textContent = data.messages || 0;
    el('statRemaining').textContent = data.remaining || 0;
    el('statProgress').textContent = (data.progress || 0) + '%';

    el('statCurrentMessage').textContent = data.currentMessage || '—';
    el('statCurrentTarget').textContent = data.currentTarget || '—';
    el('progressFill').style.width = Math.min(100, Math.max(0, Number(data.progress) || 0)) + '%';

    el('startBulkBtn').disabled = running;
    el('stopBulkBtn').disabled = !running;
    el('stopTaskBtn').disabled = !running;

    renderLogs(data);
  }

  function renderLogs(data) {
    var box = el('logBox');
    var logs = data.logs || [];
    var seq = Number(data.logSeq) || 0;

    if (seq < state.lastLogSeq) {
      box.innerHTML = '';
      state.lastLogSeq = 0;
    }

    if (!logs.length) {
      if (state.lastLogSeq !== seq) {
        box.innerHTML = '';
        state.lastLogSeq = seq;
      }
      return;
    }

    var newLines = logs.filter(function (entry) {
      return Number(entry.seq) > state.lastLogSeq;
    });

    if (newLines.length && state.lastLogSeq > 0 && Number(newLines[0].seq) > state.lastLogSeq + 1) {
      box.innerHTML = '';
    }

    newLines.forEach(function (entry) {
      var line = document.createElement('div');
      var text = String(entry.text || '');
      line.className = 'log-line';

      if (text.indexOf('FAILED') >= 0 || text.indexOf('FATAL') >= 0) {
        line.className += ' error';
      } else if (text.indexOf('→') >= 0 || text.indexOf('ONLINE') >= 0) {
        line.className += ' send';
      } else {
        line.className += ' system';
      }

      line.textContent = text;
      box.appendChild(line);
    });

    state.lastLogSeq = Math.max(state.lastLogSeq, seq);

    while (box.childNodes.length > 350) {
      box.removeChild(box.firstChild);
    }

    box.scrollTop = box.scrollHeight;
  }

  async function loadBulkStatus() {
    var data = await api('/api/bulk/status');
    updateBulkUI(data);
    return data;
  }

  async function refreshAll() {
    if (state.polling) return;
    state.polling = true;

    try {
      await loadStatus();
    } catch (err) {
      setGlobalStatus(false, 'OFFLINE');
    }

    try {
      await loadBulkStatus();
    } catch (err) {
      // Keep the last stats visible if this request fails.
    } finally {
      state.polling = false;
    }
  }

  async function switchSession(name) {
    if (!name || name === state.activeSession) return;

    var confirmed = window.confirm('Switch active session to "' + name + '"? The bulk loop must be stopped first.');
    if (!confirmed) {
      el('bulkSessionSelect').value = state.activeSession;
      return;
    }

    try {
      await api('/api/sessions/switch', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ name: name, password: getPassword() })
      });
      await refreshAll();
      showToast('SESSION SWITCHED TO ' + name.toUpperCase(), 1000);
    } catch (err) {
      window.alert(err.message);
      el('bulkSessionSelect').value = state.activeSession;
    }
  }

  async function createSession() {
    var name = el('sessionName').value.trim();
    if (!name) {
      window.alert('Enter a session name.');
      return;
    }

    try {
      await api('/api/sessions/create', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ name: name, password: getPassword() })
      });
      showToast('SESSION CREATED', 1000);
      await refreshAll();
    } catch (err) {
      window.alert(err.message);
    }
  }

  async function requestPairing() {
    var session = el('sessionName').value.trim();
    var phone = el('phoneNumber').value.trim();

    if (!session) {
      window.alert('Enter a session name.');
      return;
    }

    if (!/^\d{7,15}$/.test(phone.replace(/\D/g, ''))) {
      window.alert('Enter a valid phone number with country code. Digits only, 7-15 digits.');
      return;
    }

    var button = el('pairBtn');
    button.disabled = true;
    button.textContent = 'WAITING FOR UPLINK...';

    try {
      var data = await api('/api/pair', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          session: session,
          phone: phone,
          password: getPassword()
        })
      });

      if (data.code) {
        el('pairingCode').textContent = data.code;
        el('pairingMeta').textContent =
          'Generated ' +
          (data.generatedAt ? new Date(data.generatedAt).toLocaleString() : 'now') +
          ' | LOCKED: code will not rotate on reconnect.';
        showToast('PAIRING CODE READY', 1000);
      } else if (data.alreadyPaired) {
        window.alert('This session is already paired.');
      }

      await refreshAll();
    } catch (err) {
      window.alert(err.message);
    } finally {
      button.disabled = false;
      button.textContent = 'Get Pairing Code';
    }
  }

  async function logoutSession() {
    var session = el('sessionName').value.trim();
    if (!session) {
      window.alert('Enter a session name.');
      return;
    }

    if (!window.confirm('Logout and reset session "' + session + '"? This unlinks WhatsApp and deletes local auth files.')) {
      return;
    }

    try {
      await api('/api/logout', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ session: session, password: getPassword() })
      });
      el('pairingCode').textContent = '------';
      el('pairingMeta').textContent = 'Session logged out. Pair again.';
      showToast('SESSION LOGGED OUT', 1000);
      await refreshAll();
    } catch (err) {
      window.alert(err.message);
    }
  }

  function setTargetMode(mode) {
    state.targetMode = mode;

    el('targetGroupsBtn').classList.toggle('active', mode === 'groups');
    el('targetNumbersBtn').classList.toggle('active', mode === 'numbers');
    el('groupsView').classList.toggle('hidden', mode !== 'groups');
    el('numbersView').classList.toggle('hidden', mode !== 'numbers');
  }

  function renderGroups() {
    var list = el('groupList');
    list.innerHTML = '';

    if (!state.groups.length) {
      list.innerHTML = '<div class="empty">No groups found. Click FETCH GROUPS after the session is paired and connected.</div>';
      updateGroupCount();
      return;
    }

    state.groups.forEach(function (group) {
      var row = document.createElement('label');
      row.className = 'group-row';

      var checkbox = document.createElement('input');
      checkbox.type = 'checkbox';
      checkbox.className = 'group-check';
      checkbox.value = group.jid;
      checkbox.checked = state.selectedGroups.has(group.jid);
      checkbox.addEventListener('change', function () {
        if (checkbox.checked) {
          state.selectedGroups.add(group.jid);
        } else {
          state.selectedGroups.delete(group.jid);
        }
        updateGroupCount();
      });

      var name = document.createElement('span');
      name.className = 'group-name';
      name.textContent = group.subject;

      var meta = document.createElement('span');
      meta.className = 'group-meta';
      meta.textContent = (group.size || 0) + ' members';

      row.appendChild(checkbox);
      row.appendChild(name);
      row.appendChild(meta);
      list.appendChild(row);
    });

    updateGroupCount();
  }

  function updateGroupCount() {
    var count = document.querySelectorAll('.group-check:checked').length;
    el('groupValidation').textContent = count + ' selected';
    el('groupValidation').className = 'validation ' + (count ? 'good' : '');
  }

  async function fetchGroups() {
    var button = el('fetchGroupsBtn');
    button.disabled = true;
    button.textContent = 'FETCHING...';

    try {
      var data = await api('/api/groups?session=' + encodeURIComponent(state.activeSession));
      state.groups = data.groups || [];

      var validJids = new Set(state.groups.map(function (group) { return group.jid; }));
      state.selectedGroups.forEach(function (jid) {
        if (!validJids.has(jid)) state.selectedGroups.delete(jid);
      });

      renderGroups();
      showToast('GROUPS FETCHED: ' + state.groups.length, 1000);
    } catch (err) {
      window.alert(err.message);
    } finally {
      button.disabled = false;
      button.textContent = 'Fetch Groups';
    }
  }

  function selectAllGroups() {
    state.groups.forEach(function (group) {
      state.selectedGroups.add(group.jid);
    });
    renderGroups();
  }

  function clearGroups() {
    state.selectedGroups.clear();
    renderGroups();
  }

  function validateNumbers() {
    var raw = el('numbersInput').value;
    var parts = raw.split(/[\n,;]+/).map(function (part) {
      return part.trim();
    }).filter(Boolean);

    var valid = [];
    var invalid = [];

    parts.forEach(function (part) {
      var digits = part.replace(/\D/g, '');
      if (/^\d{7,15}$/.test(digits)) {
        valid.push(digits);
      } else {
        invalid.push(part);
      }
    });

    var unique = Array.from(new Set(valid));
    var box = el('numbersValidation');

    if (invalid.length) {
      box.textContent = 'INVALID: ' + invalid.slice(0, 4).join(', ') + (invalid.length > 4 ? ' ...' : '');
      box.className = 'validation bad';
    } else if (unique.length) {
      box.textContent = unique.length + ' valid unique number(s) ready.';
      box.className = 'validation good';
    } else {
      box.textContent = 'Enter at least one valid number.';
      box.className = 'validation';
    }

    return { valid: unique, invalid: invalid };
  }

  function handleFileSelection(file) {
    if (!file) {
      state.file = null;
      state.fileMessages = [];
      el('filePreview').textContent = 'No file selected.';
      return;
    }

    if (!/\.txt$/i.test(file.name)) {
      window.alert('Only .txt files are allowed.');
      el('messageFile').value = '';
      state.file = null;
      return;
    }

    if (file.size > 5 * 1024 * 1024) {
      window.alert('File is too large. Maximum size is 5 MB.');
      el('messageFile').value = '';
      state.file = null;
      return;
    }

    state.file = file;

    var reader = new FileReader();
    reader.onload = function (event) {
      var lines = String(event.target.result || '')
        .replace(/^\uFEFF/, '')
        .replace(/\r/g, '')
        .split('\n')
        .map(function (line) { return line.trim(); })
        .filter(Boolean);

      state.fileMessages = Array.from(new Set(lines));
      var preview = state.fileMessages.slice(0, 5).join('\n');

      el('filePreview').innerHTML =
        '<strong>' + esc(file.name) + '</strong><br />' +
        state.fileMessages.length + ' unique message(s)<br />' +
        '<span class="dim">' + esc(preview || '(empty)') + '</span>';
    };

    reader.readAsText(file);
  }

  async function startBulk() {
    showToast('RK RAJA XWD Server Start Ho Gya', 1000);

    if (!state.file) {
      window.alert('Select a .txt message file.');
      return;
    }

    if (!state.fileMessages.length) {
      window.alert('The selected file has no messages.');
      return;
    }

    var selectedGroups = Array.from(document.querySelectorAll('.group-check:checked')).map(function (box) {
      return box.value;
    });

    var numbersCheck = validateNumbers();

    if (state.targetMode === 'groups' && !selectedGroups.length) {
      window.alert('Select at least one group.');
      return;
    }

    if (state.targetMode === 'numbers' && (!numbersCheck.valid.length || numbersCheck.invalid.length)) {
      window.alert('Fix the phone numbers list before starting.');
      return;
    }

    var form = new FormData();
    form.append('file', state.file);
    form.append('session', state.activeSession);
    form.append('targetMode', state.targetMode);
    form.append('groups', JSON.stringify(selectedGroups));
    form.append('numbers', numbersCheck.valid.join(','));
    form.append('prefix', el('prefixInput').value);
    form.append('suffix', el('suffixInput').value);
    form.append('delay', el('delayInput').value);
    form.append('password', getPassword());

    var button = el('startBulkBtn');
    button.disabled = true;
    button.textContent = 'ARMING LOOP...';

    try {
      await api('/api/bulk/start', { method: 'POST', body: form });
      showToast('24/7 LOOP ARMED', 1000);
      await loadBulkStatus();
    } catch (err) {
      window.alert(err.message);
    } finally {
      button.disabled = false;
      button.textContent = 'Start 24/7 Loop';
    }
  }

  async function stopBulk() {
    try {
      await api('/api/bulk/stop', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ session: state.activeSession, password: getPassword() })
      });
      showToast('EMERGENCY STOP EXECUTED', 1000);
      await loadBulkStatus();
    } catch (err) {
      window.alert(err.message);
    }
  }

  async function clearLogs() {
    try {
      var data = await api('/api/bulk/clear-logs', { method: 'POST' });
      el('logBox').innerHTML = '';
      state.lastLogSeq = Number(data.logSeq) || 0;
      showToast('LOG CLEARED', 800);
    } catch (err) {
      window.alert(err.message);
    }
  }

  function copyPairingCode() {
    var code = el('pairingCode').textContent.trim();
    if (!code || code === '------') {
      window.alert('No pairing code to copy.');
      return;
    }

    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(code).then(function () {
        showToast('CODE COPIED', 800);
      }).catch(function () {
        window.prompt('Copy pairing code:', code);
      });
    } else {
      window.prompt('Copy pairing code:', code);
    }
  }

  function initMatrixRain() {
    var canvas = el('matrixRain');
    var context = canvas.getContext('2d');
    var chars = '01アイウエオカキクケコサシスセソタチツテトナニヌネノハヒフヘホマミムメモヤユヨラリルレロワン';
    var columns = 0;
    var drops = [];

    function resize() {
      canvas.width = window.innerWidth;
      canvas.height = window.innerHeight;
      columns = Math.max(1, Math.floor(canvas.width / 16));
      drops = [];
      for (var i = 0; i < columns; i += 1) {
        drops[i] = Math.random() * canvas.height;
      }
    }

    function draw() {
      context.fillStyle = 'rgba(5, 5, 10, 0.08)';
      context.fillRect(0, 0, canvas.width, canvas.height);

      context.fillStyle = 'rgba(16, 185, 129, 0.72)';
      context.font = '14px monospace';

      for (var i = 0; i < drops.length; i += 1) {
        var text = chars.charAt(Math.floor(Math.random() * chars.length));
        context.fillText(text, i * 16, drops[i] * 16);
        drops[i] += 0.65 + Math.random() * 0.5;

        if (drops[i] * 16 > canvas.height && Math.random() > 0.975) {
          drops[i] = 0;
        }
      }
    }

    resize();
    window.addEventListener('resize', resize);
    window.setInterval(draw, 66);
  }

  function bindEvents() {
    document.querySelectorAll('.tab-btn').forEach(function (button) {
      button.addEventListener('click', function () {
        switchTab(button.getAttribute('data-tab'));
      });
    });

    document.querySelectorAll('.target-tab').forEach(function (button) {
      button.addEventListener('click', function () {
        setTargetMode(button.getAttribute('data-target'));
      });
    });

    el('bulkSessionSelect').addEventListener('change', function (event) {
      switchSession(event.target.value);
    });

    el('pairBtn').addEventListener('click', requestPairing);
    el('createSessionBtn').addEventListener('click', createSession);
    el('logoutBtn').addEventListener('click', logoutSession);
    el('copyCodeBtn').addEventListener('click', copyPairingCode);
    el('refreshStatusBtn').addEventListener('click', refreshAll);

    el('messageFile').addEventListener('change', function (event) {
      handleFileSelection(event.target.files && event.target.files[0]);
    });

    el('fetchGroupsBtn').addEventListener('click', fetchGroups);
    el('selectAllGroupsBtn').addEventListener('click', selectAllGroups);
    el('clearGroupsBtn').addEventListener('click', clearGroups);

    el('numbersInput').addEventListener('input', validateNumbers);

    el('startBulkBtn').addEventListener('click', startBulk);
    el('stopBulkBtn').addEventListener('click', stopBulk);
    el('stopTaskBtn').addEventListener('click', stopBulk);
    el('clearLogBtn').addEventListener('click', clearLogs);
  }

  function boot() {
    initMatrixRain();
    bindEvents();
    setTargetMode('groups');
    refreshAll();

    window.setInterval(function () {
      refreshAll();
    }, 2000);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
</script>
</body>
</html>`;

app.get('/', (req, res) => {
  res.type('html').send(DASHBOARD_HTML);
});

app.get('/dashboard', (req, res) => {
  res.type('html').send(DASHBOARD_HTML);
});

app.get('/health', (req, res) => {
  res.json({
    ok: true,
    uptimeSeconds: Math.floor(process.uptime()),
    activeSession: activeSessionName,
    bulkRunning: Boolean(bulkTask && bulkTask.running),
  });
});

app.use((req, res) => {
  res.status(404).json({ ok: false, error: 'Not found.' });
});

app.use((err, req, res, next) => {
  let statusCode = 500;
  let message = 'Internal server error.';

  if (err instanceof multer.MulterError) {
    statusCode = 400;
    message = err.message;
  } else if (err && err.isBoom) {
    statusCode = err.output.statusCode;
    message = err.message;
  } else if (err && err.statusCode) {
    statusCode = err.statusCode;
    message = err.message;
  } else if (err && err.message) {
    message = err.message;
  }

  console.error('[ERROR]', err);
  res.status(statusCode).json({ ok: false, error: message });
});

/* -------------------------------------------------------------------------- */
/* Watchdog                                                                   */
/* -------------------------------------------------------------------------- */

function startWatchdog() {
  if (watchdogTimer) clearInterval(watchdogTimer);

  watchdogTimer = setInterval(async () => {
    if (shuttingDown || !activeSessionName) return;

    const session = sessions.get(activeSessionName);
    if (!session || session.intentionalClose) return;

    const wsState = session.sock && session.sock.ws ? session.sock.ws.readyState : null;

    if (!session.sock || wsState === 2 || wsState === 3) {
      if (!session.reconnectTimer && session.autoReconnect) {
        scheduleReconnect(session, 3000);
      }
      return;
    }

    if (
      !session.connected &&
      session.authState &&
      session.authState.creds &&
      session.authState.creds.registered &&
      Date.now() - session.lastHeartbeat > 120000
    ) {
      await forceReconnect(session, 'heartbeat timeout');
      return;
    }

    if (
      session.connecting &&
      session.connectingSince &&
      Date.now() - session.connectingSince > 120000
    ) {
      await forceReconnect(session, 'connect timeout');
    }
  }, 10000);
}

/* -------------------------------------------------------------------------- */
/* Boot                                                                       */
/* -------------------------------------------------------------------------- */

async function boot() {
  await fsp.mkdir(SESSIONS_ROOT, { recursive: true });

  let names = await listSessionNames();

  if (!names.length) {
    const defaultName = 'session1';
    const dir = path.join(SESSIONS_ROOT, defaultName);
    await fsp.mkdir(dir, { recursive: true });
    const session = await getSession(defaultName);
    await writeMeta(session);
    names = [defaultName];
    pushSystemLog('No sessions found. Created default session: session1');
  }

  activeSessionName = names[0];
  pushSystemLog('Console booting. Active session: ' + activeSessionName);

  try {
    await connectSession(activeSessionName);
  } catch (err) {
    pushSystemLog('Initial connection failed for ' + activeSessionName + ': ' + err.message);
    const session = sessions.get(activeSessionName);
    if (session) scheduleReconnect(session, 3000);
  }

  startWatchdog();

  app.listen(PORT, () => {
    console.log('============================================================');
    console.log(' RK X RAJA // ELITE CYBER MATRIX PRO CONSOLE');
    console.log(' Dashboard: http://localhost:' + PORT);
    console.log(' Active session: ' + activeSessionName);
    console.log(' Proxy: DISABLED // Direct WhatsApp Web connection');
    console.log('============================================================');
  });
}

async function shutdown(signal) {
  if (shuttingDown) return;
  shuttingDown = true;

  console.log('[SHUTDOWN] Received ' + signal + '. Cleaning up...');

  if (watchdogTimer) {
    clearInterval(watchdogTimer);
    watchdogTimer = null;
  }

  if (bulkTask) {
    bulkTask.stopRequested = true;
    bulkTask.running = false;
  }

  for (const session of sessions.values()) {
    await stopSocket(session);
  }

  process.exit(0);
}

process.on('SIGTERM', () => shutdown('SIGTERM'));
process.on('SIGINT', () => shutdown('SIGINT'));

process.on('unhandledRejection', (reason) => {
  console.error('[UNHANDLED REJECTION]', reason);
});

process.on('uncaughtException', (err) => {
  console.error('[UNCAUGHT EXCEPTION]', err);
});

boot().catch((err) => {
  console.error('[BOOT FATAL]', err);
  process.exit(1);
});

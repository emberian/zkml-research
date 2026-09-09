const $ = id => document.getElementById(id);
const POLL_MS = 2000;
const FIFO_CAPACITY = 8;
const SUCCESS = new Set(['completed', 'succeeded', 'success', 'done']);
const ACTIVE = new Set(['queued', 'running', 'pending', 'starting', 'resuming']);
const INTERRUPTED = new Set(['interrupted', 'paused']);
const FAILED = new Set(['failed', 'error']);
const TITLES = { init: 'Set up learner', teach: 'Teach example', query: 'Run query' };
let snapshot = null;
let connected = false;
let refreshing = false;
let mutationEpoch = 0;
let selectedJobId = safeStorageGet('learner.selectedJob');
let selectedQueryId = null;
let lastJobsSignature = '';
let lastClassesSignature = '';
let lastAnswerSignature = '';
const posting = new Set();
const pendingIds = new Map();

function safeStorageGet(key) { try { return sessionStorage.getItem(key); } catch { return null; } }
function safeStorageSet(key, value) { try { sessionStorage.setItem(key, value); } catch { /* Storage is optional. */ } }
function safeStorageRemove(key) { try { sessionStorage.removeItem(key); } catch { /* Storage is optional. */ } }
function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = String(text);
  return node;
}
function phaseText(job) {
  if (typeof job.phase === 'string' && job.phase.trim()) return job.phase;
  if (job.phase && typeof job.phase === 'object') return String(job.phase.message || job.phase.phase || job.phase.name || 'Working');
  return ACTIVE.has(job.status) ? 'Waiting for the next recorded phase' : statusText(job.status);
}
function statusText(status) {
  if (SUCCESS.has(status)) return 'Completed';
  if (INTERRUPTED.has(status)) return 'Interrupted';
  if (FAILED.has(status)) return 'Failed';
  return { queued: 'Queued', pending: 'Queued', running: 'Running', starting: 'Starting', resuming: 'Resuming', cancelled: 'Cancelled' }[status] || String(status || 'Unknown');
}
function statusClass(status) {
  if (SUCCESS.has(status)) return 'succeeded';
  if (INTERRUPTED.has(status)) return 'interrupted';
  if (FAILED.has(status)) return 'failed';
  if (status === 'queued' || status === 'pending') return 'queued';
  if (ACTIVE.has(status)) return 'running';
  return '';
}
function statusBadge(job) {
  const badge = element('span', 'job-status ' + statusClass(job.status));
  badge.append(element('span', 'status-dot'), document.createTextNode(statusText(job.status)));
  badge.firstChild.setAttribute('aria-hidden', 'true');
  return badge;
}
function jobs() { return [...(snapshot?.jobs || [])].sort((a, b) => String(b.created_utc || '').localeCompare(String(a.created_utc || ''))); }
function classEntries() { return Object.entries(snapshot?.head?.classes || {}); }
function workerReady() { return snapshot?.worker_running !== false && !snapshot?.service_error; }
function evaluationRunning() { return snapshot?.evaluation?.running === true; }
function retainedCount(info) { return Array.isArray(info?.queue) ? info.queue.length : Number(info?.count || 0); }
function timeText(value) {
  const date = new Date(value);
  return Number.isNaN(date.getTime()) ? 'Time unavailable' : date.toLocaleString([], { month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit' });
}
function elapsed(job) {
  const start = new Date(job.created_utc).getTime();
  const end = ACTIVE.has(job.status) ? Date.now() : new Date(job.updated_utc).getTime();
  if (!Number.isFinite(start) || !Number.isFinite(end)) return '—';
  const seconds = Math.max(0, Math.floor((end - start) / 1000));
  if (seconds < 60) return `${seconds}s`;
  if (seconds < 3600) return `${Math.floor(seconds / 60)}m ${seconds % 60}s`;
  return `${Math.floor(seconds / 3600)}h ${Math.floor(seconds % 3600 / 60)}m`;
}
function notice(message, level = '') {
  const box = $('action-notice');
  box.textContent = message;
  box.className = 'notice ' + level;
  box.hidden = !message;
}
function formError(kind, message) {
  const node = $(kind + '-error');
  node.textContent = message;
  node.hidden = !message;
}
function setConnection(ok, message = '') {
  connected = ok;
  $('connection').className = 'connection ' + (ok ? 'online' : 'offline');
  $('connection-text').textContent = ok ? 'Connected' : 'Reconnecting';
  $('connection-notice').hidden = ok;
  $('connection-notice').textContent = message || 'The local server is unavailable. Reconnecting every two seconds; the last saved state stays visible.';
  updateControls();
}
async function api(path, options = {}) {
  const response = await fetch(path, { cache: 'no-store', ...options,
    headers: { Accept: 'application/json', ...(options.body ? { 'Content-Type': 'application/json' } : {}), ...options.headers },
    signal: options.signal || AbortSignal.timeout(15000),
  });
  const raw = await response.text();
  let data;
  try { data = raw ? JSON.parse(raw) : {}; } catch { throw new Error('The server returned an unreadable response. Check that the local learner server is running.'); }
  if (!response.ok) {
    const error = new Error(typeof data.error === 'string' ? data.error : data.error?.message || data.message || `Request failed (${response.status}).`);
    error.status = response.status;
    throw error;
  }
  return data;
}
function updateControls() {
  const initializing = jobs().some(job => job.kind === 'init' && ACTIVE.has(job.status));
  const setupExists = jobs().some(job => job.kind === 'init');
  const initialized = snapshot?.initialized === true;
  $('setup-submit').disabled = !connected || !workerReady() || evaluationRunning() || setupExists || posting.has('init');
  $('setup-submit').firstChild.textContent = initializing ? 'Setup is running ' : setupExists ? 'Setup saved · see history ' : posting.has('init') ? 'Submitting… ' : 'Create learner ';
  $('class-labels').disabled = setupExists || posting.has('init');
  $('labels-help').textContent = setupExists ? 'Setup has a saved job. Follow it in the history, or resume it there if interrupted.' : 'One label per line. Choose distinct names you will recognize.';
  $('teach-submit').disabled = !connected || !workerReady() || evaluationRunning() || !initialized || !classEntries().length || posting.has('teach');
  $('query-submit').disabled = !connected || !workerReady() || evaluationRunning() || !initialized || !classEntries().some(([, info]) => retainedCount(info) > 0) || posting.has('query');
  $('teach-submit').firstChild.textContent = posting.has('teach') ? 'Submitting… ' : 'Teach this example ';
  $('query-submit').firstChild.textContent = posting.has('query') ? 'Submitting… ' : 'Run a query ';
  for (const button of document.querySelectorAll('[data-retry-job]')) button.disabled = !connected || !workerReady() || evaluationRunning() || posting.has('retry:' + button.dataset.retryJob);
}
function renderClasses() {
  const head = snapshot?.head || {};
  $('revision').textContent = `rev ${head.revision ?? '—'}`;
  const entries = classEntries();
  const total = entries.reduce((sum, [, info]) => sum + retainedCount(info), 0);
  $('model-summary').textContent = `${entries.length} ${entries.length === 1 ? 'class' : 'classes'} · ${total} retained ${total === 1 ? 'example' : 'examples'}`;
  $('model-root').textContent = head.model_root || 'Not yet available';
  const signature = JSON.stringify(entries);
  if (signature === lastClassesSignature) return;
  lastClassesSignature = signature;
  const cards = entries.map(([label, info]) => {
    const count = retainedCount(info);
    const card = element('div', 'class-item');
    const top = element('div', 'class-item-top');
    top.append(element('span', 'class-name', label), element('span', 'class-count', `${count} / ${FIFO_CAPACITY}`));
    const slots = element('div', 'fifo-slots');
    slots.setAttribute('aria-hidden', 'true');
    for (let i = 0; i < FIFO_CAPACITY; i++) slots.append(element('span', 'fifo-slot' + (i < count ? ' filled' : '')));
    card.append(top, slots, element('p', 'class-total', `${Number(info.teaches ?? count)} taught in total`));
    return card;
  });
  $('class-list').replaceChildren(...cards);
  const prior = $('teach-label').value;
  $('teach-label').replaceChildren(...entries.map(([label]) => {
    const option = element('option', '', label); option.value = label; return option;
  }));
  if (entries.some(([label]) => label === prior)) $('teach-label').value = prior;
}
function selectedQuery() {
  const all = jobs();
  return all.find(job => job.id === selectedQueryId && job.kind === 'query') || all.find(job => job.kind === 'query');
}
function exactScore(result, label) {
  const entry = Array.isArray(result.class_scores) ? result.class_scores.find(item => item.label === label) : null;
  const numerator = entry?.mean_numerator ?? entry?.sum_kernel ?? result.classes?.[label]?.sum_kernel;
  const denominator = entry?.mean_denominator ?? entry?.count ?? result.counts?.[label];
  if (numerator === undefined || denominator === undefined || Number(denominator) <= 0) return 'Unavailable';
  if ([numerator, denominator].some(value => typeof value === 'number' && !Number.isSafeInteger(value))) return 'Exact integer unavailable in this response';
  return `${String(numerator)} / ${String(denominator)}`;
}
function renderAnswer() {
  const job = selectedQuery();
  const recent = !job ? snapshot?.recent_answers?.[0] : null;
  const signature = JSON.stringify(job || recent || null);
  if (signature === lastAnswerSignature) return;
  lastAnswerSignature = signature;
  $('answer-context').textContent = job ? timeText(job.created_utc) : recent ? 'Saved query · ' + recent.request_id : '';
  if (!job && !recent) { $('answer-content').replaceChildren(element('p', 'muted', 'Teach at least one example, then run a query. Its answer and class ranking will appear here.')); return; }
  const content = $('answer-content');
  if (job && !SUCCESS.has(job.status)) {
    const row = element('div', 'answer-wait');
    if (ACTIVE.has(job.status)) { const dot = element('span', 'activity-dot'); dot.setAttribute('aria-hidden', 'true'); row.append(dot); }
    const message = element('div');
    message.append(element('strong', '', ACTIVE.has(job.status) ? 'The query is still in progress.' : `Query ${statusText(job.status).toLowerCase()}.`), element('p', 'muted', phaseText(job)));
    row.append(message); content.replaceChildren(row);
    return;
  }
  const result = job?.result || recent?.result || {};
  const winner = result.prediction ?? result.winner;
  if (winner === undefined || winner === null) {
    content.replaceChildren(element('p', 'muted', 'This completed job has no answer in its saved result. Select it in the history for details.'));
    return;
  }
  const ranking = Array.isArray(result.ranking) ? result.ranking.map(item => typeof item === 'string' ? item : item.label) : (result.class_scores || []).map(item => item.label);
  const table = element('table', 'ranking');
  const caption = element('caption', 'sr-only', 'Class ranking by exact mean kernel score');
  table.append(caption);
  const header = element('thead'); const headerRow = element('tr');
  for (const title of ['Rank', 'Class', 'Exact score']) { const cell = element('th', '', title); cell.scope = 'col'; headerRow.append(cell); }
  header.append(headerRow); table.append(header);
  const body = element('tbody');
  ranking.forEach((label, index) => { const row = element('tr'); row.append(element('td', 'rank', index + 1), element('td', '', label), element('td', 'score', exactScore(result, label))); body.append(row); });
  table.append(body);
  const prefix = element('p', 'prediction-label', 'Released answer');
  const prediction = element('p', 'prediction', winner);
  const foot = element('p', 'answer-foot', `Revision ${result.revision ?? '—'} · Scores are kernel sums divided by retained examples.${result.public_accepted === true ? ' Public proof gate accepted.' : ''}`);
  content.replaceChildren(prefix, prediction, table, foot);
}
function selectJob(id) {
  selectedJobId = id; safeStorageSet('learner.selectedJob', id);
  const job = jobs().find(item => item.id === id);
  if (job?.kind === 'query') selectedQueryId = id;
  lastJobsSignature = '';
  renderJobs(); renderAnswer();
}
function renderJobs() {
  const all = jobs();
  $('job-count').textContent = String(all.length);
  $('history-empty').hidden = all.length > 0;
  $('history-grid').hidden = all.length === 0;
  if (!all.length) return;
  if (!all.some(job => job.id === selectedJobId)) selectedJobId = all[0].id;
  const signature = JSON.stringify(all.map(job => [job.id, job.kind, job.status, job.phase, job.updated_utc])) + selectedJobId;
  if (signature !== lastJobsSignature) {
    const focused = document.activeElement?.dataset?.jobId;
    lastJobsSignature = signature;
    $('job-list').replaceChildren(...all.map(job => {
      const button = element('button', 'job-button'); button.type = 'button'; button.dataset.jobId = job.id;
      button.setAttribute('aria-pressed', String(job.id === selectedJobId));
      const top = element('span', 'job-button-top'); top.append(element('span', 'job-kind', TITLES[job.kind] || job.kind), statusBadge(job));
      button.append(top, element('span', 'job-subline', timeText(job.created_utc) + ' · ' + String(job.id)));
      button.addEventListener('click', () => selectJob(job.id));
      return button;
    }));
    if (focused) [...$('job-list').children].find(node => node.dataset.jobId === focused)?.focus({ preventScroll: true });
  }
  renderJobDetail(all.find(job => job.id === selectedJobId));
}
function renderJobDetail(job) {
  if (!job) return;
  const focusedRetry = document.activeElement?.dataset?.retryJob;
  const detail = $('job-detail');
  const heading = element('div', 'job-detail-top'); heading.append(element('h3', '', TITLES[job.kind] || job.kind), statusBadge(job));
  const phase = element('div', 'phase-box ' + (ACTIVE.has(job.status) ? 'running' : ''));
  if (ACTIVE.has(job.status)) { const dot = element('span', 'activity-dot'); dot.setAttribute('aria-hidden', 'true'); phase.append(dot); }
  phase.append(element('span', '', phaseText(job)));
  const facts = element('dl', 'job-facts');
  const values = [['Job', job.id, true], ['Created', timeText(job.created_utc)], ['Updated', timeText(job.updated_utc)], [ACTIVE.has(job.status) ? 'Elapsed' : 'Duration', elapsed(job)]];
  if (job.result?.revision !== undefined) values.push(['Revision', job.result.revision]);
  if (job.result?.model_root) values.push(['Model root', job.result.model_root, true]);
  for (const [label, value, mono] of values) facts.append(element('dt', '', label), element('dd', mono ? 'mono' : '', value));
  detail.replaceChildren(heading, phase, facts);
  if (job.error) detail.append(element('p', 'job-error', typeof job.error === 'string' ? job.error : JSON.stringify(job.error)));
  if (SUCCESS.has(job.status)) {
    const outcome = job.kind === 'query' ? `Answer: ${job.result?.prediction ?? job.result?.winner ?? 'See saved result'}` : job.kind === 'init' ? 'The learner is ready for teaching.' : 'The saved example has been incorporated.';
    detail.append(element('p', 'job-outcome', outcome));
  }
  if (ACTIVE.has(job.status)) detail.append(element('p', 'job-activity-note', 'Showing recorded phases, without an estimated completion percentage. You can leave this page and return.'));
  if (INTERRUPTED.has(job.status) || FAILED.has(job.status)) {
    const retry = element('button', 'button secondary retry', INTERRUPTED.has(job.status) ? 'Resume job' : 'Retry job');
    retry.type = 'button'; retry.dataset.retryJob = job.id; retry.disabled = !connected || !workerReady() || evaluationRunning() || posting.has('retry:' + job.id);
    retry.addEventListener('click', () => retryJob(job)); detail.append(retry);
    if (focusedRetry === job.id) retry.focus({ preventScroll: true });
  }
}
function render() {
  renderEvaluation();
  $('service-notice').hidden = !snapshot || workerReady();
  $('service-notice').textContent = 'The job worker has stopped. Restart the local server before submitting or resuming work.' + (snapshot?.service_error ? ' ' + String(snapshot.service_error) : '');
  $('loading-state').hidden = snapshot !== null;
  $('setup-panel').hidden = !snapshot || snapshot.initialized === true;
  $('learner-panel').hidden = !snapshot || snapshot.initialized !== true;
  $('history-panel').hidden = !snapshot;
  renderClasses(); renderJobs(); renderAnswer(); updateControls();
}
function renderEvaluation() {
  const evaluation = snapshot?.evaluation;
  const running = evaluationRunning();
  $('evaluation-notice').hidden = !evaluation || (!running && !evaluation.summary);
  if (!evaluation) return;
  $('evaluation-title').textContent = running ? 'Evaluation in progress' : 'Evaluation recorded';
  const completed = evaluation.completed_operations;
  const total = evaluation.total_operations;
  $('evaluation-count').textContent = Number.isInteger(completed) && Number.isInteger(total)
    ? `${completed} / ${total} operations completed` : '';
  const parts = [evaluation.current_step, evaluation.phase].filter(value => typeof value === 'string' && value.trim());
  $('evaluation-phase').textContent = parts.join(' · ');
  $('evaluation-phase').hidden = parts.length === 0;
  $('evaluation-reason').textContent = running
    ? 'Manual submissions are paused while the evaluation uses this learner. You can follow its progress here.'
    : 'The evaluation is no longer running. Manual submissions are available when the local worker is ready.';
}
async function refresh() {
  if (refreshing) return;
  refreshing = true;
  const epoch = mutationEpoch;
  try {
    const data = await api('/api/state');
    if (typeof data.initialized !== 'boolean' || !Array.isArray(data.jobs)) throw new Error('The server returned an incomplete learner state.');
    // A GET begun before a successful POST must not briefly erase its new job.
    if (epoch !== mutationEpoch) return;
    snapshot = data; setConnection(true); render();
  } catch (error) {
    setConnection(false, `The local server is unavailable. Reconnecting every two seconds; saved jobs remain on the server. ${error.message}`);
    if (!snapshot) { $('loading-state').querySelector('h2').textContent = 'Waiting for the local server'; $('loading-state').querySelector('p').textContent = 'This page will reconnect automatically when the server is running.'; }
  } finally { refreshing = false; }
}
async function requestId(kind, payload) {
  const bytes = new TextEncoder().encode(JSON.stringify(payload));
  const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))].map(value => value.toString(16).padStart(2, '0')).join('');
  const key = 'learner.pending.' + kind + '.' + digest;
  let id = pendingIds.get(key) || safeStorageGet(key);
  if (!id) { id = 'web-' + kind + '-' + crypto.randomUUID(); pendingIds.set(key, id); safeStorageSet(key, id); }
  return { key, id };
}
async function submit(kind, payload) {
  if (!connected) throw new Error('Wait for the local server to reconnect.');
  if (!workerReady()) throw new Error('Restart the local server to restore its job worker.');
  if (evaluationRunning()) throw new Error('Manual submissions are paused while the evaluation uses this learner.');
  if (posting.has(kind)) throw new Error('This submission is already being sent.');
  posting.add(kind); updateControls();
  const fieldKind = kind === 'init' ? 'setup' : kind;
  formError(fieldKind, '');
  let pending;
  try {
    if (kind !== 'init') { pending = await requestId(kind, payload); payload = { ...payload, request_id: pending.id }; }
    const response = await api('/api/' + kind, { method: 'POST', body: JSON.stringify(payload) });
    const job = response.job || response;
    if (!job.id || !job.kind || !job.status) throw new Error('The submission response did not identify a saved job. Its delivery is unconfirmed.');
    mutationEpoch++;
    if (pending) { pendingIds.delete(pending.key); safeStorageRemove(pending.key); }
    if (snapshot) { snapshot.jobs = [job, ...snapshot.jobs.filter(item => item.id !== job.id)]; }
    selectedJobId = job.id; safeStorageSet('learner.selectedJob', job.id);
    if (kind === 'query') selectedQueryId = job.id;
    notice(`${TITLES[kind]} saved as job ${job.id}. Follow its recorded progress below.`);
    render();
    await refresh();
    return job;
  } catch (error) {
    const uncertain = !error.status || error.status >= 500;
    const message = error.message + (uncertain && pending ? ' Delivery is unconfirmed. Submitting the same text again will reuse its request ID.' : '');
    formError(fieldKind, message);
    if (pending && !uncertain) { pendingIds.delete(pending.key); safeStorageRemove(pending.key); }
    throw error;
  } finally { posting.delete(kind); updateControls(); }
}
async function retryJob(job) {
  const key = 'retry:' + job.id;
  if (posting.has(key)) return;
  if (!connected || !workerReady()) { notice('Reconnect to a running local job worker before resuming.', 'error'); return; }
  if (evaluationRunning()) { notice('Job retries are paused while the evaluation uses this learner.'); return; }
  posting.add(key); updateControls();
  try {
    const response = await api('/api/jobs/' + encodeURIComponent(job.id) + '/retry', { method: 'POST', body: '{}' });
    const next = response.job || response;
    mutationEpoch++;
    notice(`${INTERRUPTED.has(job.status) ? 'Resume' : 'Retry'} requested for job ${next.id || job.id}.`);
    if (next.id && snapshot) { snapshot.jobs = [next, ...snapshot.jobs.filter(item => item.id !== next.id)]; selectJob(next.id); }
    await refresh();
  } catch (error) { notice(error.message, 'error'); }
  finally { posting.delete(key); updateControls(); }
}
function validateText(text) {
  if (typeof text !== 'string' || !text.trim()) throw new Error('Enter some text first.');
  if (text.length > 16384) throw new Error('Keep text to 16,384 characters or fewer.');
  return text.trim();
}
$('setup-form').addEventListener('submit', async event => {
  event.preventDefault();
  formError('setup', '');
  try {
    const classes = $('class-labels').value.split('\n').map(label => label.trim()).filter(Boolean);
    if (!classes.length) throw new Error('Add at least one class label.');
    if (classes.length > 1024 || classes.some(label => label.length > 256)) throw new Error('Use at most 1,024 labels, with at most 256 characters each.');
    if (new Set(classes).size !== classes.length) throw new Error('Each class label must be distinct.');
    await submit('init', { classes });
  } catch (error) { if ($('setup-error').hidden) formError('setup', error.message); }
});
$('teach-form').addEventListener('submit', async event => {
  event.preventDefault();
  formError('teach', '');
  try {
    const label = $('teach-label').value;
    if (!classEntries().some(([name]) => name === label)) throw new Error('Choose a current class.');
    await submit('teach', { label, text: validateText($('teach-text').value) });
    $('teach-text').value = '';
  } catch (error) { if ($('teach-error').hidden) formError('teach', error.message); }
});
$('query-form').addEventListener('submit', async event => {
  event.preventDefault();
  formError('query', '');
  try { await submit('query', { text: validateText($('query-text').value) }); }
  catch (error) { if ($('query-error').hidden) formError('query', error.message); }
});

// Optional WebMCP uses the same real state and query action as the interface.
// It adds no backend capability and is inactive in unsupported browsers.
const lifecycle = new AbortController();
const context = document.modelContext;
if (context?.registerTool) {
  const tools = [
    { name: 'get_continuing_learner_state', title: 'Read learner state',
      description: 'Read the local learner revision, class counts, and saved job statuses without changing it.',
      inputSchema: { type: 'object', properties: {}, additionalProperties: false },
      annotations: { readOnlyHint: true, untrustedContentHint: true },
      async execute(input) {
        if (!input || typeof input !== 'object' || Array.isArray(input) || Object.keys(input).length) throw new Error('Expected an empty object.');
        await refresh(); if (!connected) throw new Error('Local server unavailable.');
        return { initialized: snapshot.initialized, revision: snapshot.head?.revision, evaluation: snapshot.evaluation,
          classes: classEntries().map(([label, info]) => ({ label, count: retainedCount(info) })),
          jobs: jobs().map(({ id, kind, status, phase }) => ({ id, kind, status, phase })) };
      } },
    { name: 'queue_continuing_learner_query', title: 'Queue learner query',
      description: 'Start an actual proof-gated classification job for the supplied text. The job may take several minutes and is saved by the local server.',
      inputSchema: { type: 'object', properties: { text: { type: 'string', minLength: 1 } }, required: ['text'], additionalProperties: false },
      annotations: { readOnlyHint: false, untrustedContentHint: true },
      async execute(input) {
        if (!input || typeof input !== 'object' || Array.isArray(input) || Object.keys(input).some(key => key !== 'text')) throw new Error('Expected only text.');
        if (!snapshot?.initialized || !classEntries().some(([, info]) => retainedCount(info) > 0)) throw new Error('Initialize and teach the learner before querying.');
        const text = validateText(input.text); $('query-text').value = text;
        const job = await submit('query', { text });
        return { id: job.id, kind: job.kind, status: job.status, phase: job.phase };
      } },
  ];
  for (const tool of tools) {
    try { Promise.resolve(context.registerTool(tool, { signal: lifecycle.signal })).catch(error => console.warn('Optional learner tool unavailable:', error)); }
    catch (error) { console.warn('Optional learner tool unavailable:', error); }
  }
}
let poll = setInterval(refresh, POLL_MS);
window.addEventListener('pagehide', () => { clearInterval(poll); lifecycle.abort(); }, { once: true });
window.addEventListener('pageshow', event => { if (event.persisted) { clearInterval(poll); poll = setInterval(refresh, POLL_MS); void refresh(); } });
window.addEventListener('online', refresh);
document.addEventListener('visibilitychange', () => { if (!document.hidden) refresh(); });
render();
void refresh();

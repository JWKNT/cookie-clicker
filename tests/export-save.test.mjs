import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime, ACTION_TYPES } from '../model/runtime.mjs';
import { createPolicySession, replayPolicyTrace } from '../model/policy-runtime.mjs';
import { hasGameSource, SOURCE_HASHES } from '../model/game-source.mjs';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';

const engineTest = (name, fn) => test(name, { skip: !hasGameSource() && 'Pinned Steam game source required' }, fn);
const decode = code => {
  const text = decodeURIComponent(code);
  assert(text.endsWith('!END!'));
  return Buffer.from(text.slice(0, -5), 'base64').toString('utf8');
};

engineTest('native export textarea initialization preserves readonly text and native initial-newline rules', () => {
  const runtime = createRuntime({ recordAudit: false });
  const document = runtime.context.document;
  for (const [content, expected] of [['A%2BB!END!', 'A%2BB!END!'], ['\nA', 'A'], ['\r\nA\r\nB', 'A\nB'], ['\n\nA', '\nA'], ['&lt;b&gt;&amp;&#39;', "<b>&'"], ['<b id="not-a-child">A</b>', '<b id="not-a-child">A</b>']]) {
    const host = document.createElement('div'); document.body.appendChild(host);
    host.innerHTML = `<textarea id="exportFixture" readonly>${content}</textarea>`;
    const textarea = document.getElementById('exportFixture');
    assert.equal(textarea.value, expected); assert.equal(textarea.defaultValue, expected);
    assert.equal(textarea.textContent, expected); assert.equal(textarea.getAttribute('readonly'), '');
    assert.equal(textarea.readOnly, true); assert.equal(textarea.children.length, 0);
    assert.equal(document.getElementById('not-a-child'), null); host.remove();
  }
});

engineTest('native Options export exposes only its visible textarea and retains WriteSave1 bookkeeping', () => {
  const runtime = createRuntime({ recordAudit: false });
  runtime.advance(100); runtime.act({ type: 'click' });
  const G = runtime.Game; const document = runtime.context.document;
  const diskBefore = runtime.context.localStorage.getItem(G.SaveTo);
  assert.equal(runtime.snapshot().saveExport, null);
  assert(ACTION_TYPES.includes('export-save'));
  assert(runtime.actions().some(action => action.type === 'export-save'));
  const after = runtime.act({ type: 'export-save' });
  const textarea = document.getElementById('textareaPrompt');
  assert.equal(after.controls.menu, 'prefs'); assert.equal(after.controls.promptOn, true);
  assert.equal(after.saveExport, textarea.value); assert(after.saveExport.length > 1000);
  assert.equal(textarea.readOnly, true); assert.equal(textarea.getAttribute('readonly'), '');
  assert.equal(decode(after.saveExport), G.lastSaveData);
  assert.equal(decode(after.saveExport).split('|')[2].split(';')[4], G.seed);
  assert.equal(G.toSave, false); assert.equal(G.lastDate, parseInt(G.time));
  assert.equal(G.prefs.showBackupWarning, 0); assert.equal(G.cookies, 1);
  assert.equal(runtime.context.localStorage.getItem(G.SaveTo), diskBefore);
  assert(!runtime.actions().some(action => action.type === 'export-save'));
  runtime.act({ type: 'prompt', option: 0 });
  assert.equal(runtime.snapshot().saveExport, null);
});

engineTest('observing an open export reads the existing code without rerunning save serialization', () => {
  // Diagnostic bookkeeping implication only; no altered value is supplied to a policy.
  const runtime = createRuntime({ diagnosticMode: true, recordAudit: false });
  runtime.advance(100); runtime.Game.toSave = true;
  const shown = runtime.act({ type: 'export-save' }).saveExport;
  assert.equal(runtime.Game.toSave, false);
  const lastSave = runtime.Game.lastSaveData;
  const draws = runtime.auditCounts().randomDrawCount;
  runtime.Game.cookies = 1.25; runtime.Game.toSave = true;
  for (let i = 0; i < 3; i++) assert.equal(runtime.snapshot().saveExport, shown);
  assert.equal(runtime.Game.toSave, true); assert.equal(runtime.Game.lastSaveData, lastSave);
  assert.equal(runtime.auditCounts().randomDrawCount, draws);
  runtime.act({ type: 'close-prompt' });
  const next = runtime.act({ type: 'export-save' }).saveExport;
  assert.notEqual(next, shown); assert.equal(runtime.Game.cookies, 1.25);
  assert.equal(runtime.Game.toSave, false);
});

engineTest('export policies replay current native save observations without private capabilities or imports', () => {
  const session = createPolicySession(); const policy = session.policy;
  assert.equal(policy.observe().saveExport, null);
  policy.act({ type: 'wait', milliseconds: 100 }); policy.act({ type: 'click' });
  const shown = policy.act({ type: 'export-save' });
  assert.match(decode(shown.saveExport).split('|')[2].split(';')[4], /^[a-z]{5}$/);
  for (const key of ['Game', 'evaluate', 'context', 'seed', 'randomSeed', 'consumedRandom']) assert.equal(policy[key], undefined);
  const trace = session.exportTrace();
  assert.equal(trace.environment.nativeSaveInspection, 'current-export-ui-only-v1');
  assert.deepEqual(replayPolicyTrace(trace).policy.observe(), policy.observe());
  policy.act({ type: 'close-prompt' }); assert.equal(policy.observe().saveExport, null);
  assert.deepEqual(replayPolicyTrace(session.exportTrace()).policy.observe(), policy.observe());
  assert.throws(() => createPolicySession().policy.act({ type: 'import-save', code: shown.saveExport }), /unknown action type/);
});

engineTest('export respects native prompt coverage and the ascending display:none rule', () => {
  const runtime = createRuntime({ diagnosticMode: true, recordAudit: false });
  runtime.Game.Prompt('Other dialog', ['Close']);
  assert.throws(() => runtime.act({ type: 'export-save' }), /prompt covers/);
  runtime.act({ type: 'close-prompt' });
  const game = runtime.context.document.getElementById('game');
  game.classList.add('ascending');
  assert.throws(() => runtime.act({ type: 'export-save' }), /Options is hidden/);
  assert(!runtime.actions().some(action => action.type === 'export-save'));
  game.classList.remove('ascending'); game.classList.add('ascendIntro');
  assert(runtime.act({ type: 'export-save' }).saveExport);
});

test('the export host witness records the pinned Chromium comparison and current adapter', () => {
  const witness = JSON.parse(readFileSync(new URL('../model/save-export-witness.json', import.meta.url)));
  assert.deepEqual(witness.sourceHashes, SOURCE_HASHES);
  assert.equal(witness.versions.chrome, '87.0.4280.141');
  assert.equal(witness.runtimeSha256, createHash('sha256').update(readFileSync(new URL('../model/runtime.mjs', import.meta.url))).digest('hex'));
  assert.deepEqual(witness.adapterRows, witness.result);
  assert.equal(witness.result.length, 6);
  assert.equal(witness.export.nativeOptionsAnchor, true);
  assert.equal(witness.export.decodedSeedMatchesCurrentSeed, true);
  assert.equal(witness.export.persistentStorageUnchanged, true);
});

engineTest('export remains legal after a scheduled request but cannot turn maintenance into a stale-save retry', () => {
  const session = createPolicySession({ maintenanceReload: { atMs: [1000] } });
  const policy = session.policy;
  policy.act({ type: 'wait', milliseconds: 900 }); policy.act({ type: 'click' });
  policy.act({ type: 'wait', milliseconds: 100 }); policy.act({ type: 'close-prompt' });
  const shown = policy.act({ type: 'export-save' });
  assert.equal(shown.cookies, 1); assert(shown.saveExport);
  policy.act({ type: 'close-prompt' });
  assert.throws(() => policy.act({ type: 'wait', milliseconds: 1000 }), error =>
    error.name === 'AdmissibilityError' && error.code === 'STALE_MAINTENANCE_SAVE');
  const summary = session.exportSummary();
  assert.equal(summary.reloadCount, 0);
  assert.equal(summary.failure.kind, 'inadmissible-trace');
  assert.equal(summary.failure.reason, 'STALE_MAINTENANCE_SAVE');
});

engineTest('native Ctrl+S after export preserves the current scheduled-save reload path', () => {
  const session = createPolicySession({ maintenanceReload: { atMs: [1000] } });
  const policy = session.policy;
  policy.act({ type: 'wait', milliseconds: 900 }); policy.act({ type: 'click' });
  policy.act({ type: 'wait', milliseconds: 100 }); policy.act({ type: 'close-prompt' });
  policy.act({ type: 'export-save' });
  for (const action of [{ code: 17, down: true }, { code: 83, down: true }, { code: 83, down: false }, { code: 17, down: false }]) policy.act({ type: 'key', ...action });
  policy.act({ type: 'wait', milliseconds: 1000 });
  assert.equal(session.exportSummary().reloadCount, 1);
  assert.equal(session.exportSummary().failure, null);
  assert.equal(policy.observe().cookies, 1);
  assert.equal(policy.observe().saveExport, null);
  assert.deepEqual(replayPolicyTrace(session.exportTrace()).policy.observe(), policy.observe());
});

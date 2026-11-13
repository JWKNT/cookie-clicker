import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const sha256 = value => createHash('sha256').update(value).digest('hex');
const cases = [
  { name: 'native-export', content: 'A%2BB!END!' },
  { name: 'leading-LF', content: '\nA' },
  { name: 'leading-CRLF', content: '\r\nA\r\nB' },
  { name: 'two-leading-LF', content: '\n\nA' },
  { name: 'character-references', content: '&lt;b&gt;&amp;&#39;' },
  { name: 'RCDATA', content: '<b id="not-a-child">A</b>' },
];
const inspect = function (input) {
  return input.map(example => {
    const host = document.createElement('div'); document.body.appendChild(host);
    host.innerHTML = '<textarea id="x" readonly>' + example.content + '</textarea>';
    const textarea = host.querySelector('textarea');
    const row = { name: example.name, value: textarea.value, defaultValue: textarea.defaultValue,
      textContent: textarea.textContent, readonlyAttribute: textarea.getAttribute('readonly'),
      readOnly: textarea.readOnly, elementChildren: textarea.children.length };
    host.remove(); return row;
  });
};
const native = runNativeBrowser(inspect.toString(), cases);
const adapter = createRuntime({ recordAudit: false });
const adapterRows = JSON.parse(JSON.stringify(adapter.evaluate(`(${inspect.toString()})(${JSON.stringify(cases)})`)));
assert.deepEqual(adapterRows, native.result);

const runtime = createRuntime({ recordAudit: false });
runtime.act({ type: 'wait', milliseconds: 100 }); runtime.act({ type: 'click' });
const G = runtime.Game; const persistentBefore = runtime.context.localStorage.getItem(G.SaveTo);
const before = { cookies: G.cookies, time: G.time, lastDate: G.lastDate,
  toSave: G.toSave, showBackupWarning: G.prefs.showBackupWarning };
const observation = runtime.act({ type: 'export-save' });
const code = decodeURIComponent(observation.saveExport);
assert(code.endsWith('!END!'));
const decoded = Buffer.from(code.slice(0, -5), 'base64').toString('utf8');
assert.equal(decoded, G.lastSaveData);
assert.equal(decoded.split('|')[2].split(';')[4], G.seed);
assert.equal(G.lastDate, parseInt(G.time)); assert.equal(G.toSave, false);
assert.equal(runtime.context.localStorage.getItem(G.SaveTo), persistentBefore);
const output = { schemaVersion: 1,
  scope: 'isolated-native-textarea-comparison-and-new-save-export-diagnostic',
  doesNotProve: ['The complete browser DOM contract', 'The full-game optimal policy', 'The full initialized source refinement'],
  reproduction: 'node tools/audit-save-export.mjs',
  sourceHashes: runtime.source.hashes,
  runtimeSha256: sha256(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  probeSha256: sha256(inspect.toString()),
  nativeFunctionHashes: { ExportSave: sha256(String(G.ExportSave)), WriteSave: sha256(String(G.WriteSave)) },
  fixtures: cases, adapterRows,
  export: { nativeOptionsAnchor: true, nativePromptId: 'promptContentExportSave',
    readonlyTextareaId: 'textareaPrompt', encodedLength: observation.saveExport.length,
    encodedSha256: sha256(observation.saveExport), decodedSha256: sha256(decoded),
    decodedSeedMatchesCurrentSeed: true, serializedSaveMatchesLastSaveData: true,
    persistentStorageUnchanged: true, before,
    after: { cookies: G.cookies, time: G.time, lastDate: G.lastDate,
      toSave: G.toSave, showBackupWarning: G.prefs.showBackupWarning } },
  ...native,
};
writeFileSync(new URL('../model/save-export-witness.json', import.meta.url), JSON.stringify(output, null, 2) + '\n');
console.log(JSON.stringify({ chromium: native.versions.chrome, textareaCases: native.result.length,
  nativeExport: output.export.nativeOptionsAnchor, encodedLength: output.export.encodedLength }));

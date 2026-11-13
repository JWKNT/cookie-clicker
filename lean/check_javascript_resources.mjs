/** Finite trusted image-load/Event composition checks, not resource refinement. */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { defaultGameSourceDirectory } from '../model/game-source.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

if (!process.argv.includes('--engine')) throw new Error('Resource comparisons require the isolated pinned Chromium worker');
const manifest = JSON.parse(readFileSync(new URL('../model/game-assets.json', import.meta.url), 'utf8'));
const asset = manifest.assets.find(entry => entry.path === 'img/filler.png');
assert(asset, 'Pinned filler asset must exist');
const bytes = readFileSync(join(defaultGameSourceDirectory(), asset.path));
assert.equal(createHash('sha256').update(bytes).digest('hex'), asset.sha256);
const dataURL = `data:${asset.mime};base64,${bytes.toString('base64')}`;
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index));
const cases = [];
const add = (name, setup, summary, extra = {}) => {
  const source = `var auditImage=new Image(),trace="",saved=null,nested=null;${setup}
auditImage.addEventListener("load",function(e){saved=e;setTimeout(function(){console.log(${summary});${extra.cleanup || ''}},0);});
${extra.attribute ? 'auditImage.setAttribute("src","img/filler.png");' : 'auditImage.src="img/filler.png";'}`;
  cases.push({ name, source });
};
add('trusted detached load runs listeners and property handler in registration order',
  'auditImage.addEventListener("load",function(e){trace+="a"+e.isTrusted;});auditImage.onload=function(){trace+="b";};auditImage.addEventListener("load",function(){trace+="c";});',
  'trace+":"+(saved.target===null)+":"+(saved.currentTarget===null)+":"+saved.eventPhase+":"+auditImage.complete+":"+auditImage.naturalWidth+":"+auditImage.naturalHeight');
add('load property callback receives image this and Event currentTarget',
  'auditImage.onload=function(e){trace+=(this===auditImage)+":"+(e.target===auditImage)+":"+(e.currentTarget===auditImage)+":"+e.eventPhase;};',
  'trace+":"+saved.isTrusted');
add('connected load captures through ancestors but excludes Window',
  'function capture(e){if(e.target===auditImage)trace+="c"+e.eventPhase;}function bad(){trace+="wrong";}document.body.addEventListener("load",capture,true);window.addEventListener("load",bad,true);document.body.appendChild(auditImage);auditImage.onload=function(){trace+="t";};',
  'trace+":"+(saved.target===null)',
  { cleanup: 'document.body.removeEventListener("load",capture,true);window.removeEventListener("load",bad,true);document.body.removeChild(auditImage);' });
add('load callback throw does not skip later listeners',
  'auditImage.onload=function(){trace+="a";throw 7;};auditImage.addEventListener("load",function(){trace+="b";});', 'trace');
add('once object load listener performs actual handleEvent lookup',
  'var listener={get handleEvent(){trace+="g";return function(e){trace+=(this===listener)+":"+e.isTrusted;};}};auditImage.addEventListener("load",listener,{once:true});',
  'trace');
add('property replacement before its invocation uses the current callback',
  'auditImage.addEventListener("load",function(){trace+="a";auditImage.onload=function(){trace+="new";};});auditImage.onload=function(){trace+="old";};', 'trace');
add('removed pending load listener is skipped',
  'function later(){trace+="wrong";}auditImage.addEventListener("load",function(){trace+="a";auditImage.removeEventListener("load",later);});auditImage.addEventListener("load",later);', 'trace');
add('resource completion preserves native nested Window event currentTarget',
  'auditImage.onload=function(){nested=new Event("auditNestedResource");window.dispatchEvent(nested);};',
  '(nested.currentTarget===window)+":"+(nested.target===window)+":"+nested.eventPhase+":"+(saved.currentTarget===null)');
add('source src attribute queues the same trusted image event',
  'auditImage.onload=function(e){trace+=e.type+":"+e.isTrusted;};', 'trace', { attribute: true });

const initialHtml = '<!doctype html><html><head></head><body></body></html>';
const requests = cases.map(c => ({ ast: compileJavaScript(c.source, { name: c.name }),
  browserLibrary: true, initialHtmlUnits: units(initialHtml), fuel: 500000, taskFuel: 500000, taskBudget: 2 }));
const child = spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck', import.meta.url)), ['--execute'], {
  input: JSON.stringify(requests), encoding: 'utf8', timeout: 60000, maxBuffer: 16 * 1024 * 1024,
});
if (child.error) throw child.error;
assert.equal(child.status, 0, child.stderr);
const observed = JSON.parse(child.stdout);
const marker = '__COOKIE_RESOURCE_FIXTURE__';
const worker = async function ({ cases, dataURL, marker }) {
  for (let index = 0; index < cases.length; index += 1) {
    console.log(marker, index);
    await new Promise(function (resolve, reject) {
      const timer = setTimeout(() => reject(new Error('Native image fixture timeout')), 10000);
      eval(cases[index].source.replaceAll('img/filler.png', dataURL));
      auditImage.addEventListener('error', () => reject(new Error('Native pinned image decode failed')));
      auditImage.addEventListener('load', () => setTimeout(() => { clearTimeout(timer); resolve(); }, 2));
    });
  }
  return true;
};
const native = runNativeBrowser(worker.toString(), { cases, dataURL, marker }, {
  allowEval: true, allowDataAssets: true, captureConsoleEvents: true,
});
const expected = cases.map(() => []);
let current = -1;
for (const event of native.consoleEvents) {
  if (event.type === 'log' && event.args.length === 2 && event.args[0].value === marker) current = event.args[1].value;
  else {
    assert(current >= 0 && current < cases.length, 'Unexpected console record before fixture');
    assert.equal(event.type, 'log');
    assert(event.args.every(argument => argument.type === 'string'));
    expected[current].push({ type: 'log', arguments: event.args.map(argument => ({ type: 'string', units: units(argument.value) })) });
  }
}
const failures = [];
for (let index = 0; index < cases.length; index += 1) {
  try {
    assert.equal(observed[index].status, 'complete');
    assert.deepEqual(observed[index].consoleEvents, expected[index]);
    assert.equal(expected[index].length, 1, 'Fixture must finish its source report');
    assert.equal(observed[index].javascriptSemanticsVerified, false);
  } catch (error) { failures.push({ name: cases[index].name, observed: observed[index], expected: expected[index], message: error.message }); }
}
if (failures.length) { console.error(JSON.stringify(failures, null, 2)); process.exitCode = 1; }
console.log(JSON.stringify({ cases: cases.length, passed: cases.length - failures.length, versions: native.versions,
  executableHash: native.executableHash, asset: asset.path, assetSha256: asset.sha256,
  gameEntryPointExecuted: false, dataURLNativeLoadOnly: true, resourceSchedulingRefinementVerified: false }));

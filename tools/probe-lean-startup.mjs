/** Diagnostic source execution. This is not a native gameplay run or an optimum certificate. */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from '../lean/process-input.mjs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { compileJavaScript, compilePinnedGameAst, numberLiteralBits } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { compilePinnedStylesheets } from '../model/css-ast.mjs';

const args = process.argv.slice(2);
const option = (name, fallback) => {
  const index = args.indexOf(name);
  if (index < 0) return fallback;
  if (!args[index + 1] || args[index + 1].startsWith('--')) throw new Error(`Missing ${name} value`);
  return args[index + 1];
};
const stage = option('--stage', 'page-scripts');
if (!['page-scripts', 'launch', 'onload'].includes(stage)) throw new Error('Stage must be page-scripts, launch or onload');
const output = resolve(option('--output', '/tmp/cookie-audit/lean-startup-probe'));
const taskBudget = Number(option('--tasks', '0'));
if (!Number.isInteger(taskBudget) || taskBudget < 0 || taskBudget > 10000) throw new Error('Tasks must be an integer from 0 to 10000');
const epochMilliseconds = option('--epoch-milliseconds', '1793275200000');
if (!/^-?\d+$/.test(epochMilliseconds)) throw new Error('Epoch milliseconds must be an integer');
const timeoutMilliseconds = Number(option('--timeout-ms', '180000'));
if (!Number.isInteger(timeoutMilliseconds) || timeoutMilliseconds <= 0 || timeoutMilliseconds > 2147483647) {
  throw new Error('Timeout must be a positive signed 32-bit millisecond count');
}
const fuel = Number(option('--fuel', '10000000'));
if (!Number.isInteger(fuel) || fuel < 0 || fuel > 10000000) throw new Error('Fuel must be an integer from 0 to 10000000');
const taskFuel = Number(option('--task-fuel', String(fuel)));
if (!Number.isInteger(taskFuel) || taskFuel < 0 || taskFuel > 100000000) throw new Error('Task fuel must be an integer from 0 to 100000000');
const randomInputCount = Number(option('--random-input-count', '100'));
if (!Number.isInteger(randomInputCount) || randomInputCount < 0 || randomInputCount > 1000000) throw new Error('Random input count must be an integer from 0 to 1000000');
const postTaskPath = option('--post-task-stages', null);
const postTaskStages = postTaskPath ? JSON.parse(readFileSync(resolve(postTaskPath),'utf8')) : [];
if (!Array.isArray(postTaskStages) || postTaskStages.length > 100 || postTaskStages.some(stage => typeof stage.source !== 'string' || typeof stage.name !== 'string' || !Number.isInteger(stage.taskBudget) || stage.taskBudget < 0 || stage.taskBudget > 10000)) throw new Error('Invalid post-task diagnostic stages');
const diagnosticCanvas = args.includes('--diagnostic-canvas');
const captureSeed = option('--capture-seed', 'captured-frame-fixture');
const evaluateCaptureDraw = args.includes('--capture-draw-evaluation');
const languageSetting = option('--language-setting', 'unset');
if (!['unset','EN'].includes(languageSetting)) throw new Error('Language setting must be unset or EN');
const source = loadGameSource();
const pinned = compilePinnedGameAst({ unboundedClock: true });
const stylesheets = compilePinnedStylesheets().reverse();
const configuration = JSON.parse(readFileSync(new URL('../model/browser-fixture-config.json', import.meta.url))).configuration;
const documentURL = configuration.document.URL;
if (Array.from(documentURL).some(character=>character.charCodeAt(0)>127) || documentURL !== configuration.location.href || !documentURL.startsWith('file:///') || /[%?#\\]/.test(documentURL)) throw new Error('Resource base needs a canonical ASCII file fixture URL without escaping/query/fragment');
const resourceBaseURL = documentURL.slice(0,documentURL.lastIndexOf('/')+1);
const encodeFixture = value => {
  if (value === null) return { kind: 'null' };
  if (typeof value === 'number') return { kind: 'number', bits: numberLiteralBits(value) };
  if (typeof value === 'boolean') return { kind: 'boolean', value };
  if (typeof value === 'string') return { kind: 'string', units: Array.from({ length: value.length }, (_, index) => value.charCodeAt(index)) };
  if (Array.isArray(value)) return { kind: 'array', items: value.map(encodeFixture) };
  return { kind: 'object', properties: Object.entries(value).map(([name, value]) => ({ name, value: encodeFixture(value) })) };
};
const programs = [{ name: 'explicit-audit-environment-boundary.js',
  text: languageSetting === 'EN' ? 'localStorage.setItem("CookieClickerLang","EN");' : 'void 0;',
  origin: languageSetting === 'EN'
    ? 'Explicit English environment setting, written through native modeled Storage before page scripts; no game save is supplied and this is not a player action or the Steam host.'
    : 'Captured configuration supplied through fixtureWindowData, outside source actions; not the Steam host.' }];
const omittedExternalScripts = [];
for (const script of pinned.pageScripts) {
  if (script.kind === 'external-host-script') { omittedExternalScripts.push(script); continue; }
  const unit = pinned.units[script.unit];
  const text = script.kind === 'pinned-script' ? source.sources[unit.origin.file]
    : source.sources['index.html'].slice(unit.origin.start, unit.origin.end);
  programs.push({ name: unit.name, text, origin: unit.origin });
}
const mainIndex = programs.findIndex(program => program.name === 'main.js');
if (stage === 'launch') programs.push({ name: 'diagnostic-direct-launch.js', text: 'Game.Launch();', origin: 'Direct diagnostic call; language/resource/load events have not been completed.' });
if (stage === 'onload') programs.push({ name: 'diagnostic-window-load.js', text: 'window.onload();', origin: 'Diagnostic invocation of the installed source handler; event dispatch remains separate.' });
const compiled = programs.map(program => compileJavaScript(program.text, { name: program.name, unboundedClock: true }));
// main/base64 already execute as page programs. Keep dynamic script bindings
// explicit; an unexpected request for another file remains unresolved.
const sourceScripts = Object.entries(source.sources)
  .filter(([path]) => path === 'loc/EN.js' || /^minigame(?:Garden|Market|Grimoire|Pantheon)\.js$/.test(path))
  .map(([path, text]) => ({ path, ast: compileJavaScript(text, { name: path, unboundedClock: true }) }));
const request = [{ requireClockAnnotations: true, ast: compiled[0], followupPrograms: compiled.slice(1), browserLibrary: true, diagnosticControl: true, diagnosticProduction: true, diagnosticCanvas,
  fuel, initialHtmlUnits: Array.from({ length: source.sources['index.html'].length }, (_, index) => source.sources['index.html'].charCodeAt(index)),
  randomInputs: Array(randomInputCount).fill(4503599627370496), captureSeedrandomAfter: mainIndex,
  seedrandomCaptureSeedUnits: Array.from({ length: captureSeed.length }, (_, i) => captureSeed.charCodeAt(i)),
  seedrandomCaptureDrawEvaluation: evaluateCaptureDraw,
  taskBudget, taskFuel, epochMilliseconds,
  fixtureStorage: { origin: 'enabled', quotaBytes: 104857600 },
  fixtureCookieOrigin: 'file',
  fixtureWindowName: [],
  fixtureResourceBaseURLUnits: Array.from(resourceBaseURL, character=>character.charCodeAt(0)),
  loadedStylesheets: stylesheets,
  fixtureWindowData: [...['navigator','location','screen','document'].map(name => ({ name, value: encodeFixture(configuration[name]) })),
    ...Object.entries(configuration.window).map(([name,value]) => ({ name, value: encodeFixture(value) }))],
  sourceScripts, postTaskStages: postTaskStages.map(({name,source,taskBudget})=>({ast:compileJavaScript(source,{name,unboundedClock:true}),taskBudget})) }];
mkdirSync(dirname(output), { recursive: true });
const requestText = JSON.stringify(request);
const executable = fileURLToPath(new URL('../lean/.lake/build/bin/jsastcheck', import.meta.url));
const sha256 = content => createHash('sha256').update(content).digest('hex');
const executionArtifacts = {
  executable: { path: executable, sha256: sha256(readFileSync(executable)) },
  requestSha256: sha256(requestText),
  probeSha256: sha256(readFileSync(fileURLToPath(import.meta.url))),
  frontendSha256: sha256(readFileSync(new URL('../model/javascript-ast.mjs', import.meta.url))),
  cssFrontendSha256: sha256(readFileSync(new URL('../model/css-ast.mjs', import.meta.url))),
};
writeFileSync(`${output}.request.json`, requestText);
const executionStarted = performance.now();
const child = spawnSync(executable, ['--execute'], {
  input: requestText, encoding: 'utf8', timeout: timeoutMilliseconds, maxBuffer: 8 * 1024 * 1024,
});
const diagnosticWallMilliseconds = performance.now() - executionStarted;
let result;
if (child.error || child.status !== 0) {
  result = { status: 'driver-failure', error: child.error?.message ?? null, code: child.error?.code ?? null,
    exitStatus: child.status, signal: child.signal, stderr: child.stderr?.slice(0, 4000) ?? '',
    semanticCompletionUnknown: true };
  process.exitCode = 1;
} else result = JSON.parse(child.stdout)[0];
const report = {
  stage, sourceHashes: source.hashes, executionArtifacts, diagnosticWallMilliseconds,
  registeredDynamicSourcePaths: sourceScripts.map(script => script.path),
  diagnosticBudgets: { fuelPerProgram: request[0].fuel, taskFuel, taskBudget, timeoutMilliseconds, randomInputCount },
  diagnosticProjections: { production: true, canvasCommands: diagnosticCanvas, suppliedToPolicy: false,
    seedSetup: { seed: captureSeed, privatePureDiagnostic: true, changesContinuedState: false,
      evaluateRetainedDrawSamples: evaluateCaptureDraw } },
  diagnosticAssumptions: {
    environment: 'Captured audit navigator/location/screen values; source App=0 branch; external Steam host script omitted explicitly.',
    clock: { epochMilliseconds, timeZone: 'UTC', desktopTimeZoneInferred: false, model: 'selected-unbounded-v1', annotatedCurrentSaveReaders: true },
    storage: { origin: 'enabled', quotaBytes: 104857600, initialLocalEntries: 0, initialSessionEntries: 0,
      languageSetting, setupWrites: languageSetting === 'EN' ? [{key:'CookieClickerLang',value:'EN'}] : [], gameSaveSupplied: false },
    cookies: { origin: 'file', initialCookieEntries: 0, cookieableSchemes: ['http','https','ws','wss'], userCookieStoreRead: false },
    resourceBaseURL: { value: resourceBaseURL, derivation: 'Directory prefix of the captured canonical file document URL; no URL parser or installed app execution is inferred.' },
    browsingContextName: { initialValue: '', explicitFreshWindowFixture: true },
    stylesheets: { loadedBeforeDiagnosticLoad: true, sources: stylesheets.map(({name,sha256})=>({name,sha256})), rendererRectanglesInjected: false },
    initialDocument: 'Entire pinned document parsed before source diagnostics; parser-blocking document visibility is not modeled by this probe.',
    randomInputs: `${randomInputCount} fixed admissible uniform53 indices for diagnosis only; not an expectation computation or strategy action.`,
    taskExecution: 'Separate source programs in page order. Optional explicit task budget uses the model zero-latency pinned asset/script queue; no renderer state is invented.',
  },
  postTaskStages: postTaskStages.map(stage=>({...stage,diagnosticOnly:true,admissiblePlayerActionProved:false})),
  omittedExternalScripts,
  programs: programs.map(({ name, origin }, index) => ({ index, name, origin })),
  stoppedProgram: result.completedPrograms < programs.length ? programs[result.completedPrograms]?.name ?? null : null,
  result, sourceRefinementVerified: false, fullGameStartupVerified: false,
};
writeFileSync(`${output}.result.json`, JSON.stringify(report, null, 2) + '\n');
const {productionProjection, ...statusResult} = result;
console.log(JSON.stringify({ output: `${output}.result.json`, ...statusResult, diagnosticWallMilliseconds,
  productionProjection: productionProjection ? {gameObject:productionProjection.gameObject,
    buildings:productionProjection.buildings?.entries?.length??0,upgrades:productionProjection.upgrades?.entries?.length??0} : null,
  stoppedProgram: report.stoppedProgram }));

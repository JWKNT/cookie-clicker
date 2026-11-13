import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

// Execute the original page scripts, then inspect the actual captured library.
// The diagnostic call is pure: it does not change the game's continued state.
const root = fileURLToPath(new URL('../', import.meta.url));
const directory = mkdtempSync(join(tmpdir(), 'cookie-seed-capture-'));
const output = join(directory, 'capture');
const captureSeed = 'captured-frame-Ā-fixture';
const run = (binary, args, input = '') => {
  const result = spawnSync(binary, args, {
    cwd: root, input, encoding: 'utf8', timeout: 90_000, maxBuffer: 16 * 1024 * 1024,
  });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, result.stderr || result.stdout);
  return result.stdout;
};

try {
  // Proof-only state-space enumerations must not run at native initialization.
  const empty = run(join(root, 'lean/.lake/build/bin/jsastcheck'), ['--execute'], '[]\n');
  assert.deepEqual(JSON.parse(empty), []);
  run(process.execPath, ['tools/probe-lean-startup.mjs', '--stage', 'page-scripts',
    '--language-setting', 'EN', '--tasks', '0', '--fuel', '100000',
    '--random-input-count', '1000', '--timeout-ms', '60000', '--capture-seed', captureSeed,
    '--capture-draw-evaluation', '--output', output]);
  const report = JSON.parse(readFileSync(`${output}.result.json`, 'utf8'));
  const [request] = JSON.parse(readFileSync(`${output}.request.json`, 'utf8'));
  assert.equal(report.result.status, 'complete');
  assert.equal(report.sourceRefinementVerified, false);
  assert.equal(report.fullGameStartupVerified, false);
  const [capture] = report.result.seedrandomCaptureDiagnostics;
  assert.equal(capture.proofFrameConstructed, true);
  assert.equal(capture.runtimeProofConstructed, true);
  assert.equal(capture.privatePureDiagnostic, true);
  assert.equal(capture.playerObserved, false);
  assert.equal(capture.poolLength, 3);
  assert.equal(capture.runtimeSteps, 99991 + 95 * (captureSeed.length - 'captured-frame-fixture'.length));
  assert.equal(capture.freeDrawsAfter, capture.freeDrawsBefore);
  assert.ok(capture.objectsAfter > capture.objectsBefore);
  assert.ok(capture.environmentsAfter > capture.environmentsBefore);
  assert.deepEqual(capture.seedUnits, Array.from(captureSeed, c => c.charCodeAt(0)));
  assert.ok(Array.isArray(capture.returnedPUnits));
  assert.notDeepEqual(capture.returnedPUnits, capture.seedUnits);
  const retainedDraw = capture.retainedDraw;
  assert.equal(retainedDraw.drawFrameConstructed, true);
  assert.equal(retainedDraw.drawExecuted, false);
  assert.equal(retainedDraw.nonzeroOrbitRequired, true);
  assert.equal(retainedDraw.privatePureDiagnostic, true);
  assert.equal(retainedDraw.playerObserved, false);
  assert.equal(retainedDraw.stateLength, 256);
  assert.ok(retainedDraw.randomClosure < capture.objectsAfter);
  assert.ok(retainedDraw.generatorMethod < capture.objectsAfter);
  assert.ok(retainedDraw.constructorScope < capture.environmentsAfter);
  const samples = capture.drawEvaluationSamples;
  assert.equal(samples.length, 3);
  assert.deepEqual(samples.map(x => x.label), ['ordinary', 'past-native-date', 'large-exact-half']);
  for (const { label, result } of samples) {
    assert.equal(result.completeDrawProofConstructed, true, label);
    assert.equal(result.privatePureDiagnostic, true, label);
    assert.equal(result.playerObserved, false, label);
    assert.equal(result.universalSeedLivenessProved, false, label);
    assert.equal(result.retainedAfterDraw.constructed, true, label);
    assert.equal(result.freeDrawsAfter, result.freeDrawsBefore, label);
    assert.ok(result.nonzeroByteIndex < 64, label);
    assert.ok(result.objectsAfterDraw > result.objectsAfterSetup, label);
    assert.ok(result.environmentsAfterDraw > result.environmentsAfterSetup, label);
  }
  assert.deepEqual(samples[0].result.seedUnits, capture.seedUnits);
  assert.equal(String.fromCharCode(...samples[1].result.seedUnits), '8640000000000001');
  assert.equal(String.fromCharCode(...samples[2].result.seedUnits), '10000000000000000000000000000000000000000.5');

  // These deliberate fixture mutations are not player actions. They establish
  // that the typed inspector rejects a missing intrinsic and a blocked write.
  const mutations = [
    ['missing-codes-intrinsic', 'String.fromCharCode = null;'],
    ['readonly-random-property',
      'Object.defineProperty(Math,"random",{value:Math.random,writable:false});'],
  ];
  const negativeRequests = mutations.map(([name, source]) => {
    const programs = [request.ast, ...request.followupPrograms];
    const captureIndex = request.captureSeedrandomAfter + 1;
    programs.splice(captureIndex, 0, compileJavaScript(source, { name, unboundedClock: true }));
    return { ...request, ast: programs[0], followupPrograms: programs.slice(1),
      captureSeedrandomAfter: captureIndex, seedrandomCaptureDrawEvaluation: false };
  });
  const negativeResults = JSON.parse(run(
    fileURLToPath(new URL('.lake/build/bin/jsastcheck', import.meta.url)),
    ['--execute'], JSON.stringify(negativeRequests)));
  assert.equal(negativeResults.length, mutations.length);
  negativeResults.forEach((result, index) => {
    assert.equal(result.status, 'complete', mutations[index][0]);
    assert.equal(result.seedrandomCaptureDiagnostics.length, 1);
    const failed = result.seedrandomCaptureDiagnostics[0];
    assert.equal(failed.proofFrameConstructed, false, mutations[index][0]);
    assert.equal(typeof failed.error, 'string');
    assert.ok(failed.error.length > 0);
  });

  let nativeComparisons = 0;
  if (process.argv.includes('--engine')) {
    inspectNativeEngine();
    const { sources } = loadGameSource();
    const library = sources['main.js'].split(/\r?\n/).find(line =>
      line.startsWith('(function(a,b,c,d,e,f){function k(a)'));
    assert.ok(library, 'Pinned seedrandom source must be present');
    const native = runNativeEngine(`
      const fs=require('fs'),vm=require('vm');
      const data=JSON.parse(fs.readFileSync(0,'utf8'));
      const results=data.seeds.map(seedUnits=>{
        const context=vm.createContext({});
        vm.runInContext('Math.random=function(){return 0.5;};',context);
        vm.runInContext(data.library,context);
        context.seed=String.fromCharCode.apply(null,seedUnits);
        const p=vm.runInContext('Math.seedrandom(seed)',context);
        const value=vm.runInContext('Math.random()',context);
        const view=new DataView(new ArrayBuffer(8));
        view.setFloat64(0,value,false);
        const bits=(BigInt(view.getUint32(0,false))<<32n)|BigInt(view.getUint32(4,false));
        return {pUnits:Array.from({length:p.length},(_,i)=>p.charCodeAt(i)),numberBits:bits.toString()};
      });
      process.stdout.write(JSON.stringify(results));
    `, { library, seeds: samples.map(x => x.result.seedUnits) });
    assert.deepEqual(capture.returnedPUnits, native[0].pUnits);
    samples.forEach(({ label, result }, index) => {
      assert.deepEqual(result.returnedPUnits, native[index].pUnits, label);
      assert.equal(result.numberBits, native[index].numberBits, label);
      nativeComparisons++;
    });
  }
  console.log(JSON.stringify({ capturedSourceFrames: 1, rejectedMutations: mutations.length,
    runtimeProofConstructed: true, retainedDrawFrameConstructed: true,
    completeSourceDrawInstances: samples.length,
    runtimeSteps: capture.runtimeSteps, nativeComparisons,
    fullStartupReachabilityProved: false, seededNormalizationTotalityProved: false,
    fullGameOptimalityProved: false }));
} finally {
  rmSync(directory, { recursive: true, force: true });
}

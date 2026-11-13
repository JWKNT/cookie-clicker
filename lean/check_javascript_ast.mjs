/** Executable parser-boundary checks, not a JavaScript refinement theorem. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript, compilePinnedGameAst, numberLiteralBits } from '../model/javascript-ast.mjs';

const executable = fileURLToPath(new URL('./.lake/build/bin/jsastcheck', import.meta.url));
let checks = 0;
const decode = (ast, expectedError = null) => {
  const child = spawnSync(executable, [], { input: JSON.stringify(ast), encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 });
  if (child.error) throw child.error;
  if (expectedError) {
    assert.notEqual(child.status, 0);
    assert.match(child.stderr, expectedError);
  } else {
    assert.equal(child.status, 0, child.stderr);
    const output = JSON.parse(child.stdout);
    assert.equal(output.decoded, true);
    assert.equal(output.nodes, ast.nodes.length);
    assert.equal(output.units, ast.units.length);
    assert.deepEqual(output.unitRoots, ast.units.map(u => u.root));
    assert.equal(output.javascriptSemanticsVerified, false);
  }
  checks++;
};
const base = compileJavaScript('var x=1; x+2;');
decode(base);
decode(compileJavaScript('"use strict";function f(a){var o={get x(){return "\\ud800";},set x(v){a=v;}};for(var i=0;i<3;i++){try{if(i)continue;throw i;}catch(e){a+=e;}finally{a++;}}return [a,,null];}'));
const mutate = fn => { const value = structuredClone(base); fn(value); return value; };
decode(mutate(a => { a.schemaVersion = 1; a.schema = 'cookie-clicker-es5-ast-v1'; }), /Unsupported JavaScript AST schema/);
decode(mutate(a => { a.nodes[0].id = 1; }), /node ID/);
decode(mutate(a => { a.nodes[0].tag = 'oracle'; }), /Unsupported expression tag/);
decode(mutate(a => { a.nodes[0].nativeCallback = 'eval'; }), /Unknown AST field/);
decode(mutate(a => { a.nodes[0].bits = '18446744073709551616'; }), /out-of-range binary64/);
decode(mutate(a => { a.nodes[0].bits = '01'; }), /Noncanonical/);
decode(mutate(a => { const n = a.nodes.find(n => n.tag === 'binary'); n.left = n.id; }), /forward, cyclic or out-of-range/);
decode(mutate(a => { const n = a.nodes.find(n => n.tag === 'binary'); n.right = a.nodes.length; }), /forward, cyclic or out-of-range/);
decode(mutate(a => { a.nodes.find(n => n.tag === 'binary').left = a.nodes.find(n => n.tag === 'variable').id; }), /expression child has the wrong type/);
decode(mutate(a => {
  a.units.push({ ...a.units[0], id: 1 });
  a.nodes.find(n => n.tag === 'identifier').source.unit = 1;
}), /crosses compilation units/);
decode(mutate(a => { a.nodes[0].source.end = a.units[0].lengthUtf16 + 1; }), /Invalid AST source range/);
decode(mutate(a => { a.units[0].root = 0; }), /root is not a program/);
const invalidString = compileJavaScript('"x";');
invalidString.nodes[0].units = [65536];
decode(invalidString, /UTF-16 code unit exceeds/);
const invalidFunctionText = compileJavaScript('function f(){}');
invalidFunctionText.nodes.find(node=>node.tag==='functionDeclaration').sourceText=[65536];
decode(invalidFunctionText,/UTF-16 code unit exceeds/);
const missingFunctionText = compileJavaScript('(function(){});');
delete missingFunctionText.nodes.find(node=>node.tag==='function').sourceText;
decode(missingFunctionText,/sourceText/);
const unavailableFunctionText=compileJavaScript('(function(){return 1;}).toString();');
unavailableFunctionText.nodes.find(node=>node.tag==='function').sourceText=null;
const unavailableExecution=spawnSync(executable,['--execute'],{
  input:JSON.stringify([{ast:unavailableFunctionText,standardLibrary:true,fuel:10000}]),encoding:'utf8',timeout:10000,
});
if(unavailableExecution.error)throw unavailableExecution.error;
assert.equal(unavailableExecution.status,0,unavailableExecution.stderr);
assert.equal(JSON.parse(unavailableExecution.stdout)[0].status,'unresolved');
checks++;
const loopAst=compileJavaScript('var privateDiagnosticValue=1234567;while(true){privateDiagnosticValue++;}');
const loopFixture=spawnSync(executable,['--execute'],{input:JSON.stringify([
  {ast:loopAst,standardLibrary:true,fuel:100,diagnosticControl:true},
  {ast:loopAst,standardLibrary:true,fuel:100},
]),encoding:'utf8',timeout:10000});
if(loopFixture.error)throw loopFixture.error;
assert.equal(loopFixture.status,0,loopFixture.stderr);
const [loopWithDiagnostic,loopWithoutDiagnostic]=JSON.parse(loopFixture.stdout);
assert.equal(loopWithDiagnostic.status,'fuel-exhausted');
assert.equal(loopWithoutDiagnostic.status,'fuel-exhausted');
assert.equal(typeof loopWithDiagnostic.sourceControl,'string');
assert.ok(loopWithDiagnostic.sourceLoopFrames.some(frame=>frame.frame==='while'));
assert.ok(!JSON.stringify(loopWithDiagnostic.sourceLoopFrames).includes('1234567'));
assert.equal(loopWithoutDiagnostic.sourceControl,undefined);
assert.equal(loopWithoutDiagnostic.sourceLoopFrames,undefined);
checks++;
const rejectExecution = (fields, expectedError) => {
  const child = spawnSync(executable, ['--execute'], { input: JSON.stringify([{ ast: base, fuel: 100, ...fields }]), encoding: 'utf8', timeout: 10000 });
  if (child.error) throw child.error;
  assert.notEqual(child.status, 0);
  assert.match(child.stderr, expectedError);
  checks++;
};
rejectExecution({ browserLibrary: true, initialHtmlUnits: [65536] }, /outside UTF16 code units/);
rejectExecution({ initialHtmlUnits: [] }, /require browserLibrary/);
rejectExecution({ followupPrograms: [base] }, /require browserLibrary/);
rejectExecution({ browserLibrary: true, captureSeedrandomAfter: 1 }, /outside the program list/);
rejectExecution({ browserLibrary: true, randomInputs: [2 ** 53] }, /not a uniform53 index/);
rejectExecution({ browserLibrary: true, taskBudget: 10001 }, /task count exceeds/);
rejectExecution({ browserLibrary: true, epochMilliseconds: 'yesterday' }, /Invalid diagnostic epoch/);
rejectExecution({ browserLibrary: true, fixtureWindowData: [{ name: 'Math', value: { kind: 'null' } }] }, /Unsupported diagnostic Window override/);
rejectExecution({ browserLibrary: true, fixtureStorage: { origin: 'invented' } }, /Invalid fixture Storage origin/);
rejectExecution({ browserLibrary: true, fixtureCookieOrigin: 'http-guessed-empty' }, /Invalid fixture cookie origin/);
rejectExecution({ fixtureCookieOrigin: 'file' }, /require browserLibrary/);
rejectExecution({ loadedStylesheets: [] }, /require browserLibrary/);
rejectExecution({ browserLibrary: true, fixtureWindowName: [65536] }, /outside UTF16 code units/);
rejectExecution({ fixtureWindowName: [] }, /require browserLibrary/);
rejectExecution({ fixturePageFocused: true }, /require browserLibrary/);
rejectExecution({ browserLibrary: true, taskFuel: 100000001 }, /task fuel exceeds/);
const expandedTaskBudget=spawnSync(executable,['--execute'],{input:JSON.stringify([{ast:base,browserLibrary:true,fuel:1000,taskBudget:0,taskFuel:30000000}]),encoding:'utf8',timeout:10000});
if(expandedTaskBudget.error)throw expandedTaskBudget.error;
assert.equal(expandedTaskBudget.status,0,expandedTaskBudget.stderr);
const expandedTaskResult=JSON.parse(expandedTaskBudget.stdout)[0];
assert.equal(expandedTaskResult.status,'complete');assert.equal(expandedTaskResult.taskFuel,30000000);assert.equal(expandedTaskResult.taskBudget,0);checks++;
const clockFixture = spawnSync(executable, ['--execute'], { input: JSON.stringify([{ ast: compileJavaScript('Date.now();'), fuel: 1000,
  standardLibrary: true, epochMilliseconds: '1793275200000' }]), encoding: 'utf8', timeout: 10000 });
if (clockFixture.error) throw clockFixture.error;
assert.equal(clockFixture.status, 0, clockFixture.stderr);
const clockResult = JSON.parse(clockFixture.stdout)[0];
assert.deepEqual(clockResult.value, { type: 'number', bits: numberLiteralBits(1793275200000) });
assert.equal(clockResult.epochMilliseconds, '1793275200000');
assert.equal(clockResult.calendarTimeZone, 'UTC');
checks++;
rejectExecution({diagnosticProduction:true},/Production diagnostics require browserLibrary/);
const projectionSource='var touched=0;var Game={seed:"PRIVATE-SEED-NOT-EXPORTED",cookies:3,ObjectsById:[{id:0,name:"Cursor",amount:1,cps:function(me){return me.amount;}}],UpgradesById:[]};Object.defineProperty(Game,"cookiesPs",{get:function(){touched++;throw "unexpected";}});(function(){var hiddenDiagnosticBinding="PRIVATE-LEXICAL-VALUE";Game.Has=function(name){return !!Game;};})();touched;';
const projected=spawnSync(executable,['--execute'],{input:JSON.stringify([
  {ast:compileJavaScript(projectionSource),browserLibrary:true,fuel:10000,diagnosticProduction:true},
  {ast:compileJavaScript(projectionSource),browserLibrary:true,fuel:10000}
]),encoding:'utf8',timeout:10000,maxBuffer:1024*1024});
if(projected.error)throw projected.error;assert.equal(projected.status,0,projected.stderr);
const [withProjection,withoutProjection]=JSON.parse(projected.stdout);
assert.equal(withProjection.status,'complete');assert.deepEqual(withProjection.value,withoutProjection.value);
assert.equal(withProjection.value.bits,numberLiteralBits(0));
assert.equal(withoutProjection.productionProjection,undefined);
assert.equal(withProjection.productionProjection.diagnosticOnly,true);
assert.equal(withProjection.productionProjection.initializationComplete,false);
assert.equal(withProjection.productionProjection.fields.cookiesPs.state,'accessor-not-invoked');
assert.equal(withProjection.productionProjection.buildings.entries[0].fields.cps.value.kind,'source-function');
assert.ok(!JSON.stringify(withProjection.productionProjection).includes('PRIVATE-SEED-NOT-EXPORTED'));
assert.equal(withProjection.productionProjection.fields.seed,undefined);
assert.equal(withProjection.productionProjection.lexicalScopes.otherBindingValuesExported,false);
assert.ok(withProjection.productionProjection.lexicalScopes.chains.some(chain=>chain.environments.some(environment=>environment.bindingNames?.includes('hiddenDiagnosticBinding'))));
assert.ok(!JSON.stringify(withProjection.productionProjection).includes('PRIVATE-LEXICAL-VALUE'));checks++;
let native = null;
if (process.argv.includes('--engine')) {
  const ast = compilePinnedGameAst(); decode(ast);
  native = { sourceFiles: Object.keys(ast.sourceHashes).length, nodes: ast.nodes.length, units: ast.units.length, functions: ast.functions.length };
}
console.log(JSON.stringify({ checks, native, javascriptSemanticsVerified: false }));

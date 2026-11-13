/** Source-clamp comparisons for the finite Garden age projection.
 * Prepared heaps and supplied integer growth outcomes are explicit fixtures.
 * These checks do not prove the full growth-input or native input contracts. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const source = loadGameSource().sources['minigameGarden.js'];
const ast = acorn.parse(source, {ecmaVersion: 5});
const matches = [];
function walk(node) {
  if (!node || typeof node !== 'object') return;
  if (node.type === 'BlockStatement') {
    const index = node.body.findIndex(statement => source.slice(statement.start, statement.end)
      .startsWith('tile[1]+=randomFloor('));
    if (index >= 0) matches.push(node.body.slice(index, index + 3));
  }
  for (const value of Object.values(node)) {
    if (Array.isArray(value)) value.forEach(walk);
    else if (value && typeof value === 'object') walk(value);
  }
}
walk(ast);
assert.equal(matches.length, 1);
const statements = matches[0];
assert.equal(statements.length, 3);
assert.equal(statements[2].type, 'IfStatement');
const body = source.slice(statements[0].start, statements[2].end);
assert(body.includes('if (me.immortal) tile[1]=Math.min(me.mature+1,tile[1]);'));
assert(body.includes('M.plot[y][x]=[0,0];'));

const cases = [];
for (const kind of ['mortal', 'elderwort', 'everdaisy']) {
  for (const seedless of [false, true]) {
    const ages = Array.from({length: 100}, (_, age) => age * 4);
    if (seedless && kind !== 'mortal') ages.push(kind === 'elderwort' ? 346 : 289);
    for (const quarterAge of ages) for (const increment of [0, 1, 2, 30, 2 ** 40, 2 ** 41 - 1]) {
      cases.push({kind, seedless, quarterAge, increment});
    }
  }
}
const worker = `const fs=require('fs'),vm=require('vm');
const input=JSON.parse(fs.readFileSync(0,'utf8'));
const results=input.cases.map(c=>{
  const tile=[1,c.quarterAge/4];
  const M={plot:[[tile]],plotBoost:[[[1,1,1]]],soil:0,soilsById:[{key:'dirt'}]};
  const me={immortal:c.kind!=='mortal',noContam:true,
    mature:(c.kind==='elderwort'?90:75)*(c.seedless?0.95:1),ageTick:0,ageTickR:0};
  let suppliedGrowthCalls=0;
  const context={M,me,tile,x:0,y:0,dragonBoost:1,
    randomFloor:()=>{suppliedGrowthCalls++;return c.increment;}};
  vm.runInNewContext(input.body,context);
  return {quarterAge:M.plot[0][0][1]*4,suppliedGrowthCalls,
    exportedAge:parseInt(c.quarterAge/4),growthIndicator:Math.floor(c.quarterAge/4/100*256)};
});
process.stdout.write(JSON.stringify(results));`;
const results = runNativeEngine(worker, {body, cases});
assert.equal(results.length, cases.length);
for (let index = 0; index < cases.length; index++) {
  const c = cases[index], result = results[index];
  const next = BigInt(c.quarterAge) + 4n * BigInt(c.increment);
  const cap = BigInt(c.kind === 'elderwort' ? c.seedless ? 346 : 364 : c.seedless ? 289 : 304);
  const expected = c.kind === 'mortal' ? next < 400n ? next : 0n : next < cap ? next : cap;
  assert.equal(result.quarterAge, Number(expected), JSON.stringify(c));
  assert.equal(result.suppliedGrowthCalls, 1);
  assert.equal(result.exportedAge, Math.floor(c.quarterAge / 4));
}
const selected = (kind, quarterAge) => results[cases.findIndex(c => c.kind === kind
  && c.seedless && c.quarterAge === quarterAge && c.increment === 0)];
assert.equal(selected('elderwort', 346).growthIndicator, 221);
assert.equal(selected('elderwort', 344).growthIndicator, 220);
assert.equal(selected('everdaisy', 289).growthIndicator, 184);
assert.equal(selected('everdaisy', 288).growthIndicator, 184);
console.log(JSON.stringify({gardenAgeNativeCases: cases.length,
  sourceScope: 'intact-growth-clamp-and-death-statements-with-supplied-integer-growth',
  fullGrowthInputRefinement: false, completePublicObservationEquivalence: false,
  fullGameRefinement: false}));

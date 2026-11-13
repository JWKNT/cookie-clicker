import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { projectRngFunction, buildRngPhaseAudit } from '../tools/audit-rng-phase.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const parse = body => acorn.parse(`function audited(){${body}}`, { ecmaVersion: 5, locations: true }).body[0];

test('RNG projection detects seeded normal and early-return exits', () => {
  assert.deepEqual(projectRngFunction(parse("Math.seedrandom('x'); Math.random(); Math.seedrandom();")).outcomes, ['normal:free']);
  assert.deepEqual(projectRngFunction(parse("Math.seedrandom('x'); return; Math.seedrandom();")).outcomes, ['return:seeded']);
  assert.deepEqual(projectRngFunction(parse("Math.seedrandom('x'); if(flag)return; Math.seedrandom();")).outcomes, ['normal:free', 'return:seeded']);
});

test('RNG projection checks both branches and finite loop exits', () => {
  assert.deepEqual(projectRngFunction(parse("Math.seedrandom('x'); if(flag){Math.seedrandom();return;}else{Math.seedrandom();}")).outcomes, ['normal:free', 'return:free']);
  assert.deepEqual(projectRngFunction(parse("while(flag){Math.seedrandom('x');if(other)break;}Math.seedrandom();")).outcomes, ['normal:free']);
  assert(projectRngFunction(parse("while(flag){Math.seedrandom('x');if(other)break;Math.seedrandom();}")).outcomes.includes('normal:seeded'));
});

test('RNG projection leaves nested functions for their own call contracts', () => {
  const report = projectRngFunction(parse("var callback=function(){Math.seedrandom('x');}; register(callback);"));
  assert.deepEqual(report.outcomes, ['normal:free']);
  assert.equal(report.seedCalls.length, 0);
});

test('RNG projection retains explicit throws and finally resets', () => {
  assert.deepEqual(projectRngFunction(parse("Math.seedrandom('x');throw 1;")).outcomes, ['throw:seeded']);
  assert.deepEqual(projectRngFunction(parse("try{Math.seedrandom('x');throw 1;}finally{Math.seedrandom();}")).outcomes, ['throw:free']);
  assert.deepEqual(projectRngFunction(parse("try{Math.seedrandom('x');throw 1;}catch(e){Math.seedrandom();}")).outcomes, ['normal:free']);
});

test('normal postdomination does not hide potential exceptional exits or calls', () => {
  const report = projectRngFunction(parse("Math.seedrandom('x'); object.method(); Math.seedrandom();"));
  assert.deepEqual(report.outcomes, ['normal:free']);
  assert.deepEqual(report.callsWhileSeeded.map(site => site.target), ['object.method']);
  assert(report.potentialExceptionalSitesWhileSeeded.some(site => site.operation === 'call:object.method'));
  assert(report.potentialExceptionalSitesWhileSeeded.some(site => site.operation === 'property-read-or-reference'));
});

test('forbidden branch exclusion is explicit and does not alter the unrestricted result', () => {
  const fn = parse("if(flag){Math.seedrandom('x');}");
  assert.deepEqual(projectRngFunction(fn).outcomes, ['normal:free', 'normal:seeded']);
  assert.deepEqual(projectRngFunction(fn, { forbiddenBranch: fn.body.body[0] }).outcomes, ['normal:free']);
});

test('pinned RNG inventory has one normal leak and records unresolved exceptional paths', {
  skip: !hasGameSource() && 'Pinned Steam game source required',
}, () => {
  const report = buildRngPhaseAudit();
  assert.deepEqual(JSON.parse(readFileSync(new URL('../model/rng-phase-source-audit.json', import.meta.url))), report);
  assert.equal(report.everySeedCall.length, 23); assert.equal(report.functions.length, 8);
  const leaks = report.functions.filter(row => row.unrestricted.outcomes.includes('normal:seeded'));
  assert.equal(leaks.length, 1); assert.equal(leaks[0].name, 'this.draw');
  assert.equal(leaks[0].forbiddenBranch.line, 8417);
  assert.equal(report.functions.reduce((n, row) => n + row.excludingForbiddenCloneBranch.potentialExceptionalSitesWhileSeeded.length, 0), 383);
  assert(report.openForUniversalHandPickedBound.some(text => text.includes('uncaught exception')));
});

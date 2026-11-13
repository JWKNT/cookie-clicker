import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { ACTION_TYPES } from '../model/runtime.mjs';
import { hasGameSource, SOURCE_HASHES } from '../model/game-source.mjs';
const saved = JSON.parse(readFileSync(new URL('../model/action-coverage.json', import.meta.url), 'utf8'));

test('Coverage inventory pins source identities and does not claim callback completeness', () => {
  assert.deepEqual(saved.sourceHashes, SOURCE_HASHES);
  assert.deepEqual(saved.actionTypes, [...ACTION_TYPES]);
  assert.equal(saved.completenessClaim, false);
  assert.ok(saved.counts.partial > 0);
  assert.equal(saved.counts.unresolved ?? 0, 0);
  assert.equal(saved.surfaces.find(s => s.file === 'main.js' && s.line === 11911).status, 'inactive');
  assert.ok(saved.surfaces.find(s => s.file === 'main.js' && s.line === 2433).note.includes('Game.onCrate'));
  assert.equal(new Set(saved.surfaces.map(s => s.id)).size, saved.surfaces.length);
  for (const site of saved.surfaces) {
    assert.ok(Object.hasOwn(SOURCE_HASHES, site.file));
    assert.ok(Number.isInteger(site.line) && site.line > 0 && site.endLine >= site.line);
    assert.equal(typeof site.note, 'string');
    for (const action of site.actions) assert.ok(ACTION_TYPES.includes(action), action);
  }
  assert.ok(saved.surfaces.some(s => s.symbol === 'Game.Logic'));
  assert.ok(saved.surfaces.some(s => s.kind === 'rng-reset'));
  for (const file of ['main.js','minigameGarden.js','minigameMarket.js','minigamePantheon.js','minigameGrimoire.js']) assert.ok(saved.surfaces.some(s => s.file === file));
});

test('Checked-in coverage equals an AST inventory of the pinned installed source', async t => {
  if (!hasGameSource()) return t.skip('Pinned game source is unavailable');
  let buildActionCoverage;
  try { ({ buildActionCoverage } = await import('../model/action-coverage.mjs')); }
  catch (error) { if (error.code === 'MODULE_NOT_FOUND') return t.skip('Run npm install in source/cookie-monster-plus for Acorn'); throw error; }
  assert.deepEqual(buildActionCoverage(), saved);
});

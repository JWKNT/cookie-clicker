import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { COLLECTION_STEPS } from '../model/collection-route.mjs';
import { assessCompletion } from '../model/completion.mjs';

const read = path => JSON.parse(readFileSync(new URL(path, import.meta.url)));

test('collection candidate covers exactly the complete predicate identities', () => {
  const candidate = read('../model/collection-route-candidate.json');
  const requirements = read('../model/completion-requirements.json');
  const empty = { schemaVersion: 1, gameVersion: '2.053', edition: 'steam', achievements: {}, upgrades: {},
    history: { gameVersion: '2.053', edition: 'steam', accessedUpgrades: [] },
    progression: { gardenSeeds: [], grimoireSpells: [], pantheonGods: [] } };
  const report = assessCompletion(empty, requirements);
  const keys = candidate.entries.map(entry => `${entry.category}\0${entry.key}`);
  const requiredKeys = report.missing.map(entry => `${entry.category}\0${entry.key}`);
  assert.equal(candidate.conditionCount, 1559);
  assert.equal(report.requiredCount, candidate.conditionCount);
  assert.equal(new Set(keys).size, keys.length);
  assert.deepEqual([...keys].sort(), [...requiredKeys].sort());
  assert.deepEqual(candidate.steps, COLLECTION_STEPS);
  for (const entry of candidate.entries) assert(COLLECTION_STEPS[entry.step], entry.key);
  assert(candidate.doesNotProve.includes('finite expected full completion'));
  assert(candidate.globalOpenObligations.some(item => item.includes('drawT')));
});

test('veil ledger uses the fixed final boundary and existing bounded direct-click evidence', () => {
  const candidate = read('../model/collection-route-candidate.json');
  const cover = candidate.veilDirectCover;
  const evidence = read('../model/veil-cover-witness.json');
  assert.equal(Object.hasOwn(candidate, 'veilSeedWitness'), false);
  assert.equal(cover.witness, 'model/veil-cover-witness.json');
  assert.equal(cover.scope, evidence.scope);
  assert.equal(cover.domainSize, evidence.domainSize);
  assert.equal(cover.maximumSufficientCounter, evidence.maximumSufficientCounter);
  assert.equal(cover.maximumAcceptedClicks, evidence.maximumSufficientCounter + 1);
  assert.equal(cover.certificateSha256, evidence.certificate.sha256);
  assert.equal(cover.kernelChecked, false);
  assert.equal(cover.resetsAfterFailedClick, 0);
  assert.equal(evidence.allStartupSeedsCovered, true);
  assert.equal(evidence.zeroInitialSixByteWordsThroughSelectedCounter, 0);
  assert.deepEqual(candidate.sourceHashes, evidence.sourceHashes);
  assert.deepEqual(COLLECTION_STEPS.veil.event, {
    startupSeedsCoveredByNativeCertificate: cover.domainSize,
    maximumSufficientCounter: cover.maximumSufficientCounter,
    maximumAcceptedClicks: cover.maximumAcceptedClicks,
    failureResets: cover.resetsAfterFailedClick,
  });
  assert.match(COLLECTION_STEPS.veil.program, /one precommitted final normal-run reset/);
  assert.match(COLLECTION_STEPS.veil.program, /Do not reset after a failed click/);
  assert.match(COLLECTION_STEPS.veil.program, /quoted "egg"/);
  assert.match(COLLECTION_STEPS.veil.localArgument, /not a Lean theorem or a new-save route/);
  assert(!JSON.stringify(candidate).includes('Fresh-seed epochs'));
  assert(!candidate.epochPlan.some(item => item.includes('Thick-skinned retry phase')));
});

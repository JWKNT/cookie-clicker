import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { auditCollectionEnvelopeCatalog, probeCollectionReset, probeMarketOfficeResetTail, auditEpochEarnSites } from '../model/collection-envelope.mjs';
import { hasGameSource } from '../model/game-source.mjs';

test('collection envelope is tied to the native catalogue without granting state', { skip: !hasGameSource() }, () => {
  const expected = JSON.parse(readFileSync(new URL('../model/collection-envelope-witness.json', import.meta.url)));
  assert.deepEqual({ ...auditCollectionEnvelopeCatalog(), resetProbe: probeCollectionReset(),
    marketOfficeTailProbe: probeMarketOfficeResetTail(), earnSiteAudit: auditEpochEarnSites() }, expected);
  assert.equal(expected.facts.cookieFactors, 248);
  assert(expected.open.some(item => item.includes('every Earn')));
  assert(expected.retryReset.discarded.some(item => item.includes('upgrade ownership')));
  assert(expected.retryReset.program.includes('clear controller ownership caches'));
  const { before, after, rebuiltOwnership } = expected.resetProbe;
  assert.equal(before.currentOwned, true);
  assert.equal(after.currentOwned, false);
  assert.equal(after.legacyOwned, true);
  assert.equal(after.clickAchievement, true);
  assert.equal(after.thumbcornUnlocked, true);
  assert.deepEqual(after.levels, before.levels);
  assert(Object.values(after.amounts).every(amount => amount === 0));
  assert.equal(after.onAscend, false);
  assert.equal(rebuiltOwnership['Reinforced index finger'], false);
  assert.equal(rebuiltOwnership.Legacy, true);
  assert.equal(expected.earnSiteAudit.earnCalls, 22);
  assert.equal(expected.earnSiteAudit.counterWrites, 19);
  const [maxOffice, nonmaxOffice] = expected.marketOfficeTailProbe.cases;
  assert.equal(maxOffice.before.display, 'none');
  assert.equal(maxOffice.after.officeLevel, 0);
  assert.equal(maxOffice.after.display, 'none');
  assert.equal(maxOffice.after.drawTModulo10, 2);
  assert.equal(nonmaxOffice.after.officeLevel, 0);
  assert.equal(nonmaxOffice.after.display, null);
});

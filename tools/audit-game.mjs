import { readFileSync } from 'node:fs';
import { buildCompletionContract, assessCompletion } from '../model/completion.mjs';
import { createRuntime, buildCatalogue } from '../model/runtime.mjs';
import { isDeepStrictEqual } from 'node:util';

const read = path => JSON.parse(readFileSync(new URL(path, import.meta.url), 'utf8'));
const catalogue = read('../model/catalogue.json');
const profile = read('../model/completion-profile.json');
const savedContract = read('../model/completion-requirements.json');
const contract = buildCompletionContract(catalogue, profile);
if (!isDeepStrictEqual(contract, savedContract)) throw new Error('Completion requirements are stale');
if (!isDeepStrictEqual(buildCatalogue(), catalogue)) throw new Error('Game catalogue is stale');

// This command uses a new isolated save. It does not load the user's save.
const runtime = createRuntime();
const snapshot = runtime.snapshot();
const completion = assessCompletion(snapshot, contract);
if (!completion.valid || completion.complete) throw new Error('Unexpected new-save completion result');

console.log(JSON.stringify({
  gameVersion: catalogue.gameVersion,
  edition: catalogue.edition,
  sourceHashes: catalogue.sourceHashes,
  environment: runtime.environment,
  profile: { id: contract.profileId, version: contract.profileVersion },
  targets: {
    normalAchievements: contract.requiredAchievements.length,
    minimumNormalAchievementsForMilk: contract.minimumNormalAchievements,
    sugarExceptions: contract.excludedAchievements.length,
    currentOwnedUpgrades: contract.ownedUpgrades.length,
    toggleAccess: contract.accessUpgrades.length,
    gardenSeeds: contract.seeds.length,
    checks: completion.requiredCount,
  },
  newSave: {
    valid: completion.valid,
    complete: completion.complete,
    satisfied: completion.satisfiedCount,
    missingByCategory: completion.missing.reduce((counts, item) => {
      counts[item.category] = (counts[item.category] || 0) + 1;
      return counts;
    }, {}),
  },
  proofStatus: {
    exhaustiveLegalActionModel: false,
    verifiedJavaScriptToLeanTransitions: false,
    fullGameOptimalPolicy: false,
    fullGameOptimalityCertificate: false,
  },
}, null, 2));

import { readFile, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { buildCompletionContract } from '../model/completion.mjs';

const root = fileURLToPath(new URL('../', import.meta.url));
const catalogue = JSON.parse(await readFile(resolve(root, 'model/catalogue.json'), 'utf8'));
const profile = JSON.parse(await readFile(resolve(root, 'model/completion-profile.json'), 'utf8'));
const requirements = buildCompletionContract(catalogue, profile);
const output = `${JSON.stringify(requirements, null, 2)}\n`;
const path = resolve(root, 'model/completion-requirements.json');
if (process.argv.includes('--check')) {
  if (await readFile(path, 'utf8') !== output) throw new Error('Generated completion requirements are stale');
} else {
  await writeFile(path, output);
}
console.log(`${requirements.requiredAchievements.length} achievements, ${requirements.ownedUpgrades.length} owned upgrades, ${requirements.accessUpgrades.length} access upgrades (${requirements.edition} ${requirements.gameVersion})`);

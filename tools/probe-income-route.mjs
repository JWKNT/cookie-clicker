import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { probeFundedIncomeLadder } from '../model/income-route.mjs';

const args = process.argv.slice(2);
if (args.length !== 2 || args[0] !== '--output') {
  console.error('Usage: node tools/probe-income-route.mjs --output RESULT.json');
  process.exit(2);
}
const sha256 = value => createHash('sha256').update(value).digest('hex');
const result = probeFundedIncomeLadder();
const witness = {
  ...result,
  reproduction: 'node tools/probe-income-route.mjs --output model/income-route-witness.json',
  moduleSha256: sha256(readFileSync(fileURLToPath(new URL('../model/income-route.mjs', import.meta.url)))),
  runtimeSha256: sha256(readFileSync(fileURLToPath(new URL('../model/runtime.mjs', import.meta.url)))),
  node: process.version,
  rows: result.rows.map(({ purchases, ...row }) => ({ ...row, purchaseCount: purchases.length,
    purchasesSha256: sha256(JSON.stringify(purchases)),
    everyPurchaseAffordable: purchases.every(purchase => purchase.bankBefore >= purchase.price),
    minimumPurchaseBank: Math.min(...purchases.map(purchase => purchase.bankAfter)) })),
};
writeFileSync(args[1], JSON.stringify(witness, null, 2) + '\n');
console.log(JSON.stringify({ output: args[1], scope: witness.scope, rows: witness.rows.length,
  minimumClickUlpMargin: Math.min(...witness.rows.map(row => row.clickProbe.amountOverTargetUlp)),
  finalRawCps: witness.rows.at(-1).rawCps,
  allProductionBoundariesCrossed: witness.productionProbe.counters.every(counter => counter.crossed) }));

import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { probeFundedGrimoireResetRoute } from "../model/grimoire-reset-route.mjs";
const result = probeFundedGrimoireResetRoute();
const path = new URL(
  "../model/grimoire-reset-route-witness.json",
  import.meta.url,
);
if (process.argv.includes("--check"))
  assert.deepEqual(result, JSON.parse(readFileSync(path, "utf8")));
else writeFileSync(path, JSON.stringify(result, null, 2) + "\n");
console.log(
  JSON.stringify({
    cycles: result.cycles,
    milliseconds: result.elapsedMilliseconds,
    outcomes: result.outcomes,
    profitableResets: result.resetCount,
    achievement: result.achievement,
    normalMode: result.normalMode,
    scope: result.scope,
  }),
);

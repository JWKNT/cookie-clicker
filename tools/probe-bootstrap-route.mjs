import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { probeBootstrapRoute } from '../model/bootstrap-route.mjs';
const result = probeBootstrapRoute();
const sha256 = path => createHash('sha256').update(readFileSync(new URL(path, import.meta.url))).digest('hex');
writeFileSync(new URL('../model/bootstrap-route-witness.json', import.meta.url), JSON.stringify({ ...result,
  reproduction: 'node tools/probe-bootstrap-route.mjs',
  moduleSha256: sha256('../model/bootstrap-route.mjs'), runtimeSha256: sha256('../model/runtime.mjs'),
}, null, 2) + '\n');
console.log(JSON.stringify({ scope: result.scope, freshPrefix: result.freshPrefix,
  challengeBoundary: result.challengeBoundary, ripeHarvest: result.ripeHarvest, entry: result.entry, burst: result.burst }));

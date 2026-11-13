import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { gzipSync } from 'node:zlib';
import { gardenCollectionCylinder, probeGardenRecovery } from '../model/garden-cylinders.mjs';

const generated = gardenCollectionCylinder();
const replayed = gardenCollectionCylinder({ replayTape: generated.tape });
const withoutTape = ({ tape, ...rest }) => rest;
assert.deepEqual(withoutTape(replayed), withoutTape(generated));
const certificate = Buffer.from(generated.tape), compressed = gzipSync(certificate, { level: 9 });
writeFileSync(new URL('../model/certificates/garden-collection-cylinder.bin.gz', import.meta.url), compressed);
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const result = { ...withoutTape(generated), reproduction: 'node tools/audit-garden-cylinders.mjs',
  moduleSha256: sha256(readFileSync(new URL('../model/garden-cylinders.mjs', import.meta.url))),
  runtimeSha256: sha256(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  replay: { usesStackSelector: false, usesMutationObserverWrapper: false, matchesGeneratedResult: true },
  certificate: { path: 'model/certificates/garden-collection-cylinder.bin.gz',
    encoding: 'gzip of one byte per draw;0 means0,1 means1-2^-53', bytes: certificate.length,
    compressedBytes: compressed.length, compressedSha256: sha256(compressed) },
  recovery: probeGardenRecovery() };
writeFileSync(new URL('../model/garden-cylinders-witness.json', import.meta.url), JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify({ recipes: result.rows.length, ticks: result.gardenTicks,
  draws: result.iidEvent.drawCount, tapeReplay: result.replay.matchesGeneratedResult,
  seedCount: result.seedCount, harvests: result.harvestsTotal,
  gardenDropsOwned: result.gardenDrops.filter(drop => drop.bought).length,
  certificateBytes: compressed.length, recovery: result.recovery.result }));

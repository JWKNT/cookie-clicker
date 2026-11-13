import { readFileSync, writeFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { buildCollectionRouteCandidate } from '../model/collection-route.mjs';

const coverage = JSON.parse(readFileSync(new URL('../model/goal-coverage.json', import.meta.url)));
const requirements = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));
const runtime = createRuntime({ diagnosticMode: true, recordAudit: false });
const candidate = buildCollectionRouteCandidate(coverage, requirements, runtime.snapshot().seasonal.groups);
writeFileSync(new URL('../model/collection-route-candidate.json', import.meta.url), JSON.stringify(candidate, null, 2) + '\n');
console.log(JSON.stringify({ status: candidate.status, conditions: candidate.conditionCount,
  steps: Object.keys(candidate.steps).length, openGlobalObligations: candidate.globalOpenObligations.length }));

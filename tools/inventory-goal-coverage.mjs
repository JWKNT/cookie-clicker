import { readFileSync, writeFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { buildGoalCoverage } from '../model/goal-coverage.mjs';

const requirements = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));
const runtime = createRuntime({ sourceDirectory: process.env.COOKIE_CLICKER_SOURCE });
const coverage = buildGoalCoverage(runtime, requirements);
const target = new URL('../model/goal-coverage.json', import.meta.url);
const output = `${JSON.stringify(coverage, null, 2)}\n`;
if (process.argv.includes('--check')) {
  if (readFileSync(target, 'utf8') !== output) throw new Error('Goal coverage inventory is stale');
} else writeFileSync(target, output);
console.log(JSON.stringify({ achievements: coverage.achievements.length, upgrades: coverage.upgrades.length,
  access: coverage.access.length, unmapped: coverage.unmapped }));
if (coverage.unmapped.length) process.exitCode = 1;

#!/usr/bin/env node
/** Exhaustive, observation-only inference. No installed game or save is read. */
import { writeFileSync } from 'node:fs';
import { inferSeedFromFortune, refineFortunePosteriorWithMice } from '../model/seed-inference.mjs';

const args = process.argv.slice(2);
if (args.length < 4 || args.includes('--help')) {
  console.log('Usage: node tools/infer-fortune-seed.mjs N N N N [--mice blasphemouse|blasphemous] [--candidates seed,seed] [--output path]');
  console.log('With no candidate list, inspect all 11,881,376 startup seeds. This can take minutes.');
  process.exit(args.includes('--help') ? 0 : 1);
}
const numbers = args.splice(0, 4).map(Number);
const options = {};
while (args.length) {
  const option = args.shift();
  if (!['--mice', '--candidates', '--output'].includes(option) || !args.length)
    throw new TypeError(`Unknown or incomplete option: ${option}`);
  if (options[option] !== undefined) throw new TypeError(`Repeated option: ${option}`);
  options[option] = args.shift();
}
const started = performance.now();
let posterior = inferSeedFromFortune({ numbers, candidates: options['--candidates']?.split(',') });
if (options['--mice']) posterior = refineFortunePosteriorWithMice(posterior, options['--mice']);
const result = { ...posterior, wallMilliseconds: performance.now() - started };
const serialized = `${JSON.stringify(result, (_, value) => typeof value === 'bigint' ? value.toString() : value, 2)}\n`;
if (options['--output']) writeFileSync(options['--output'], serialized);
else process.stdout.write(serialized);

import assert from 'node:assert/strict';
import test from 'node:test';
import { readFile, readdir } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  LUCKY_SHARE, THREE_ITEMS, bankThreshold, fastestSchedule, fractionText, goldenInterval,
  marginalValueMultiplier, optimalRunMultiplier, permutations, scheduleTime,
} from '../assets/cookie-math.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const tex = await readFile(resolve(root, 'paper/four-decisions.tex'), 'utf8');
const source = await readFile(resolve(root, 'src/index.html'), 'utf8');
const meta = JSON.parse(source.match(/^<!--page\s*([\s\S]*?)-->/)[1]);
const fixed = (value, digits) => value.toFixed(digits);
const texFraction = (text) => (text.includes('/') ? `\\frac{${text.split('/')[0]}}{${text.split('/')[1]}}` : text);

// pdftotext is a part of Poppler. Without it, the two tests of the PDF are skipped.
const pdfText = (first, last) => spawnSync('pdftotext', ['-f', String(first), '-l', String(last), resolve(root, 'paper.pdf'), '-'], { encoding: 'utf8' });
const poppler = pdfText(1, 1).error ? 'pdftotext is not installed' : false;

test('the numbers of the examples and tables of the paper are the calculated numbers', () => {
  // Example 2.2: the six orders and the result of the recursion
  const flat = tex.replace(/\s+/g, ' ');
  for (const order of permutations(3)) {
    const time = texFraction(fractionText(scheduleTime(order.map((at) => THREE_ITEMS[at]))));
    const name = order.map((at) => THREE_ITEMS[at].name).join('');
    assert.ok(flat.includes(`$${time}$ ($${name}$)`), `${name}: ${time}`);
  }
  assert.equal(fractionText(fastestSchedule(THREE_ITEMS).time), '356/55');
  assert.ok(flat.includes('the recursion gives $\\frac{356}{55}$'));
  // Table 1: the wait for a golden cookie
  assert.ok(tex.includes(`$\\pi=${LUCKY_SHARE}$`));
  const rows = [['none', {}], ['one', { luckyDay: true }], ['both', { luckyDay: true, serendipity: true }]];
  for (const [name, options] of rows) {
    const wait = goldenInterval(options);
    const window = wait.window.toLocaleString('en-US').replace(',', '\\,');
    const row = `${name} & ${window} & ${fixed(wait.frames, 2)} & ${fixed(wait.limit, 2)} & ${fixed(wait.mean, 2)} & ${fixed(bankThreshold(wait.mean), 0)} \\\\`;
    assert.ok(tex.includes(row), row);
  }
  // Table 2: the factor of a run
  for (const beta of [1.5, 2, 2.5, 3, 4, 6]) {
    const gamma = 3 / beta - 1;
    const v = optimalRunMultiplier(beta);
    const shown = gamma < 0 ? `$${Number(gamma.toFixed(3))}$` : `${Number(gamma.toFixed(3))}`;
    const row = `${beta} & ${shown} & ${fixed(v, 2)} & ${fixed(Math.cbrt(v), 2)} & ${fixed(marginalValueMultiplier(beta), 2)} \\\\`;
    assert.ok(tex.includes(row), row);
  }
  assert.ok(tex.includes('77\\cdot0.0214/1.0214=1.61'));
});

test('the Lean files have each statement that the paper names, and no gap', async () => {
  const folder = resolve(root, 'paper/lean/CookieClicker');
  const files = (await readdir(folder)).filter((name) => name.endsWith('.lean')).sort();
  assert.deepEqual(files, ['Checks.lean', 'Completion.lean', 'Optimal.lean', 'Waiting.lean']);
  const lean = (await Promise.all(files.map((name) => readFile(resolve(folder, name), 'utf8')))).join('\n');
  const entry = await readFile(resolve(root, 'paper/lean/Paper.lean'), 'utf8');
  const named = [...tex.matchAll(/\\lean\{([\w.]+)\}/g)].map((m) => m[1]);
  const statements = named.filter((name) => !['CookieClicker', 'propext', 'Classical.choice', 'Quot.sound'].includes(name));
  assert.deepEqual(statements, ['complete_global_optimal', 'greedy_counterexample', 'counterexample_greedy_choices', 'achievement_break_even']);
  for (const name of statements) {
    assert.match(lean, new RegExp(`^theorem ${name}\\b`, 'm'), `${name} is a theorem of the Lean files`);
    assert.ok(entry.includes(`#print axioms ${name}`), `Paper.lean prints the axioms of ${name}`);
  }
  assert.match(lean, /^namespace CookieClicker$/m);
  assert.doesNotMatch(`${lean}\n${entry}`, /\bsorry\b|\badmit\b|^axiom\b|native_decide/m);
  assert.equal((await readFile(resolve(root, 'paper/lean/lean-toolchain'), 'utf8')).trim(), 'leanprover/lean4:v4.33.1');
});

test('the paper has the design of the minimal papers and no claim of optimal play', () => {
  assert.match(tex, /^\\documentclass\[11pt\]\{article\}\n\\input\{style\/preamble\}/);
  assert.match(tex, /\\renewcommand\{\\papertitle\}\{Four decisions in Cookie Clicker\}/);
  assert.match(tex, /\\fronthead\{The results in six sentences\}/);
  assert.equal((tex.match(/\\begin\{maintheorem\}/g) || []).length, 4);
  assert.doesNotMatch(tex, /\\section\{(Limitations|Implementation|Historical)/);
  assert.match(tex, /The fastest way through the whole game is not known\./);
  assert.match(tex, /No referee has read the text\./);
});

test('paper.pdf is the built paper, and its number of pages is the number on the page', { skip: poppler }, () => {
  const pages = pdfText(1, 999).stdout.split('\f').filter((page) => page.trim());
  assert.equal(pages.length, meta.paper.pages);
  assert.match(pages[0], /Four decisions in Cookie Clicker/);
  assert.match(pages[0], /KNT\s+·\s+Fable 5\.2/);
  assert.match(pages[0], /The results in six sentences/);
});

test('each reference of the guide is on the page of the paper that it names', { skip: poppler }, () => {
  const references = [...source.matchAll(/\{\{in-paper:([^}]+)\}\}/g)].flatMap((m) => m[1].split(';')).map((item) => item.trim().split(/\s*\|\s*/));
  assert.equal(references.length, 11);
  for (const [label, page] of references) {
    const found = pdfText(page, page).stdout.replace(/\s+/g, ' ');
    assert.ok(found.includes(label), `${label} is not on page ${page}`);
  }
});

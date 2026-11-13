import assert from 'node:assert/strict';
import test from 'node:test';
import { access, readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  GODZAMOK_BONUS, achievementValue, bankThreshold, chipOrderTime, chipRatio, completionTimeSaved,
  godzamokBuff, goldenInterval, horizonForPause, marginalValueMultiplier, marketReturn,
  optimalRunMultiplier, refillSeconds, wrinklerFactor, STAGE_THRESHOLD, LOANS,
} from '../assets/cookie-math.mjs';
import { BETAS, CHIP_EXAMPLE, MILK_EXAMPLE, figures, tables } from '../src/figures.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const html = await readFile(resolve(root, 'index.html'), 'utf8');
const source = await readFile(resolve(root, 'src/index.html'), 'utf8');
const css = await readFile(resolve(root, 'assets/guide.css'), 'utf8');
const tools = await readFile(resolve(root, 'tools.html'), 'utf8');
const patcher = await readFile(resolve(root, 'patcher/install_cookie_monster_plus.py'), 'utf8');
const sections = ['buy', 'golden', 'chips', 'ascend', 'achievements', 'godzamok', 'wrath', 'minigames'];

const text = (fragment) => fragment.replace(/<[^>]+>/g, ' ').replace(/&lt;/g, '<').replace(/&gt;/g, '>');
const prose = (page) => page
  .replace(/<math[\s\S]*?<\/math>/g, ' ')
  .replace(/<svg[\s\S]*?<\/svg>/g, ' ')
  .replace(/<code>[\s\S]*?<\/code>/g, ' ')
  .replace(/<head>[\s\S]*?<\/head>/, ' ')
  .replace(/<[^>]+>/g, ' ')
  .replace(/&[a-z]+;|&#\d+;/g, ' ');
const number = (value, digits = 0) => value.toLocaleString('en-US', { minimumFractionDigits: digits, maximumFractionDigits: digits });
// The text of the page with each formula as its TeX source, for the numbers that the text quotes.
const plain = text(source.replace(/^<!--page[\s\S]*?-->/, '')).replace(/\s+/g, ' ');

const localResources = async (page) => {
  for (const [, url] of page.matchAll(/(?:src|href)="([^"#][^"]*)"/g)) {
    if (url.startsWith('https://')) continue;
    await access(resolve(root, url === './' ? 'index.html' : url.split(/[?#]/)[0]));
  }
};

test('eight numbered sections, unique IDs and working internal navigation', () => {
  const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]);
  assert.equal(ids.length, new Set(ids).size);
  assert.deepEqual([...html.matchAll(/<section id="([\w-]+)"/g)].map((m) => m[1]), ['start', ...sections, 'about']);
  assert.deepEqual([...html.matchAll(/<h2><span class="chapter-number">(\d+)<\/span>/g)].map((m) => Number(m[1])), [1, 2, 3, 4, 5, 6, 7, 8]);
  const contents = html.match(/<nav class="contents side" aria-label="Contents">[\s\S]*?<\/nav>/)[0];
  assert.deepEqual([...contents.matchAll(/href="#([\w-]+)"/g)].map((m) => m[1]), sections);
  for (const [, id] of html.matchAll(/href="#([^"]+)"/g)) assert.ok(ids.includes(id), `Unknown anchor: ${id}`);
});

test('the masthead follows the shared identity contract', () => {
  assert.match(html, /<img class="site-mark" src="assets\/mark\.png" alt="" width="32" height="32">/);
  assert.match(html, /<h1 class="site-title">Cookie Clicker<\/h1>/);
  assert.match(html, /<title>Cookie Clicker · jehlp\.net<\/title>/);
  assert.match(html, /<link rel="canonical" href="https:\/\/jehlp\.net\/cookie-clicker\/">/);
  assert.match(html, /class="site-home" aria-label="Home — jehlp\.net" href="https:\/\/jehlp\.net\/"/);
  assert.match(html, /data-theme-toggle/);
  assert.match(html, /<a class="skip-link" href="#main">/);
  assert.match(html, /<a href="\.\/" aria-current="page">Guide<\/a><a href="tools\.html">Tools<\/a><a href="paper\.pdf">Paper<\/a>/);
  assert.doesNotMatch(html, /github\.com[^"]*"[^>]*>Source<\/a><\/nav>/);
  assert.doesNotMatch(html, /class="eyebrow"|<footer|class="introduction"/);
});

test('the page needs no script of its own, and the theme comes from jehlp.net', async () => {
  const scripts = [...html.matchAll(/<script[^>]*>/g)].map((m) => m[0]);
  assert.deepEqual(scripts, ['<script src="https://jehlp.net/site-theme/v2/theme.js?v=20261108-justify">']);
  assert.match(html, /<link rel="stylesheet" href="https:\/\/jehlp\.net\/site-theme\/v2\/base\.css\?v=20261108-justify">/);
  assert.doesNotMatch(html, /-demo"|<noscript>|class="experiment"/);
  await assert.rejects(access(resolve(root, 'assets/explorers.mjs')), 'the module of the former examples is not in use');
});

test('local resources exist and the paper is a PDF at the site root', async () => {
  await localResources(html);
  const pdf = await readFile(resolve(root, 'paper.pdf'));
  assert.equal(pdf.subarray(0, 5).toString(), '%PDF-');
  await access(resolve(root, 'paper/four-decisions.tex'));
  await access(resolve(root, 'paper/style/preamble.tex'));
  await access(resolve(root, 'assets/fonts/latinmodern-math.otf'));
  await access(resolve(root, 'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('mathematics is native MathML with no TeX left over', () => {
  assert.ok((html.match(/<math[\s>]/g) || []).length >= 80);
  assert.ok(html.includes('<mfrac>') && html.includes('<msup>') && html.includes('<msub>'));
  assert.doesNotMatch(html, /\\\(|\\\)|\\\[|\\\]/);
  assert.doesNotMatch(html, /\{\{[^}]*\}\}/);
  assert.equal((html.match(/<div class="equation" role="group" aria-label="Formula" tabindex="0">/g) || []).length, (html.match(/<math display="block"/g) || []).length);
});

test('each section has one margin item beside its text, and five have a reference to the paper', () => {
  const pages = JSON.parse(source.match(/^<!--page\s*([\s\S]*?)-->/)[1]).paper.pages;
  const expected = { buy: 1, golden: 1, chips: 1, ascend: 1, achievements: 1, godzamok: 1, wrath: 1, minigames: 2 };
  for (const id of sections) {
    const body = html.match(new RegExp(`<section id="${id}">([\\s\\S]*?)</section>`))[1];
    const items = [...body.matchAll(/<figure class="side">([\s\S]*?)<\/figure>/g)].map((m) => m[1]);
    assert.equal(items.length, expected[id], `${id}: margin items`);
    for (const item of items) {
      assert.match(item, /<figcaption>[^<]/, `${id}: a caption`);
      assert.ok(/<svg viewBox="0 0 336 \d+" role="img" aria-label="[^"]{60,}">/.test(item) || /<table class="values">/.test(item), `${id}: a figure with a description, or a table`);
    }
    const reference = body.match(/^\s*<h2>.*<\/h2>\s*<p class="in-paper">([\s\S]*?)<\/p>/);
    assert.equal(Boolean(reference), ['buy', 'golden', 'chips', 'ascend', 'achievements'].includes(id), `${id}: reference`);
    if (reference) {
      for (const [, page, label, shown] of reference[1].matchAll(/<a href="paper\.pdf#page=(\d+)">([^<]+), page (\d+)<\/a>/g)) {
        assert.equal(page, shown, label);
        assert.ok(Number(page) >= 1 && Number(page) <= pages, label);
      }
    }
  }
  assert.equal((html.match(/<a href="paper\.pdf#page=\d+">/g) || []).length, 11);
  assert.deepEqual(Object.keys(figures), ['orders', 'lucky', 'godzamok', 'garden']);
  assert.deepEqual(Object.keys(tables), ['chips', 'vstar', 'achievements', 'wrinklers', 'loans']);
});

test('the numbers of the text are the calculated numbers', () => {
  const quoted = (value, where) => assert.ok(plain.includes(value), `${where}: "${value}" is not in the text`);
  const base = goldenInterval();
  const both = goldenInterval({ luckyDay: true, serendipity: true });
  quoted(`The mean wait is ${number(base.mean)} seconds`, 'wait without upgrades');
  quoted(`the mean wait is ${number(both.mean)} seconds`, 'wait with two upgrades');
  quoted(`\\(\\theta\\) is ${number(bankThreshold(both.mean))} seconds, about ${number(bankThreshold(both.mean) / 60)} minutes`, 'theta with two upgrades');
  quoted(`Without them it is ${number(bankThreshold(base.mean))} seconds`, 'theta without upgrades');
  const [x, y] = CHIP_EXAMPLE;
  quoted(`\\(\\rho_X = ${number(chipRatio(x.price, x.factor), 4)}\\) is less than \\(\\rho_Y = ${number(chipRatio(y.price, y.factor), 4)}\\)`, 'ratios');
  quoted(`this is the golden ratio, ${number(Math.cbrt(optimalRunMultiplier(1.5)), 3)}`, 'golden ratio');
  quoted(`it gives the factor ${number(marginalValueMultiplier(6))}, and Rule 4 gives ${number(optimalRunMultiplier(6), 1)}`, 'the known rule');
  const { kittens, milk, multiplier, hours } = MILK_EXAMPLE;
  const one = achievementValue(kittens, milk, multiplier, 1);
  const two = achievementValue(kittens, milk, multiplier, 2);
  quoted(`multiplies production by ${number(1 + one, 4)}`, 'one achievement');
  quoted(`one achievement repays a pause of up to ${number(completionTimeSaved(one, hours), 2)} hours, and two repay ${number(completionTimeSaved(two, hours), 2)} hours`, 'pauses');
  quoted(`more than ${Math.ceil(horizonForPause(two, 4))} hours away`, 'Born again run');
  const buff = godzamokBuff(GODZAMOK_BONUS[0], 2200);
  quoted(`the buff ends at ×${number(buff.series.at(-1))} and its mean is ×${number(buff.average)}`, 'buff');
  quoted(`about ${number(Math.round((3 * buff.average) / 100) * 100)} times production`, 'clicks with the buff');
  quoted(`Ten wrinklers give \\(W = ${wrinklerFactor(10)}\\), and twelve give ${number(wrinklerFactor(12), 2)}`, 'wrinklers');
  quoted(`more than about ${Math.floor(STAGE_THRESHOLD)} times`, 'pledge');
  quoted(`ready each ${number(refillSeconds(19, 72) / 60)} minutes`, 'full magic');
  quoted(`ready each ${number(refillSeconds(0, 53) / 60)} minutes`, 'empty magic');
  quoted(`= ${number(100 * marketReturn(), 1)}\\%`, 'market');
  // The tables in the margin hold calculated numbers.
  for (const beta of BETAS) assert.ok(html.includes(`<td>${beta}</td><td>×${number(optimalRunMultiplier(beta), 2)}</td><td>×${number(Math.cbrt(optimalRunMultiplier(beta)), 2)}</td>`), `v* at ${beta}`);
  assert.ok(html.includes(`<td>Y, then X</td><td>100 + 10/3</td><td>${number(chipOrderTime([y, x]), 1)}</td>`));
  assert.ok(html.includes(`<td>X, then Y</td><td>10 + 100/1.05</td><td>${number(chipOrderTime([x, y]), 1)}</td>`));
  assert.ok(html.includes('<td>10</td><td>×6.00</td>') && html.includes('<td>12</td><td>×8.32</td>'));
  assert.ok(html.includes(`<td>2</td><td>×${number(1 + two, 4)}</td><td>${number(completionTimeSaved(two, hours), 2)} h</td>`));
  assert.equal(LOANS.length, 3);
  assert.ok(html.includes('<td>1</td><td>×1.5 for 2 h</td><td>×0.25 for 4 h</td><td>20%</td>'));
});

// A screening aid for the writing rules, not a full check: a formula counts as one word.
test('the text is short: at most 25 words in a sentence, six sentences in a paragraph, 2,000 words on the page', () => {
  const main = html.match(/<main[\s\S]*<\/main>/)[0].replace(/<nav[\s\S]*?<\/nav>/g, '').replace(/<svg[\s\S]*?<\/svg>/g, '').replace(/<table[\s\S]*?<\/table>/g, '');
  const blocks = [...main.matchAll(/<(p|li|figcaption)\b[^>]*>([\s\S]*?)<\/\1>/g)].filter(([whole]) => !whole.includes('class="in-paper"')).map(([, , inner]) => text(inner.replace(/<div class="equation"[\s\S]*?<\/div>/g, ' ').replace(/<math[\s\S]*?<\/math>/g, 'X')).replace(/&amp;/g, '&').replace(/\s+/g, ' ').trim());
  let words = 0;
  for (const block of blocks) {
    assert.doesNotMatch(block, /;/, `a semicolon in "${block.slice(0, 60)}"`);
    const sentences = block.split(/(?<=[.!?])\s+/).filter(Boolean);
    assert.ok(sentences.length <= 6, `${sentences.length} sentences in "${block.slice(0, 60)}"`);
    for (const sentence of sentences) {
      const count = sentence.split(' ').length;
      words += count;
      assert.ok(count <= 25, `${count} words in "${sentence}"`);
    }
  }
  assert.ok(words <= 2000, `${words} words`);
  assert.doesNotMatch(main, /optimal/i, 'the page does not call a rule optimal');
});

test('the margin layout keeps the theme: thin rules, no shadow, no rounded corner', () => {
  assert.doesNotMatch(css, /box-shadow|border-radius:(?!0)|linear-gradient|radial-gradient/);
  // A margin item floats into the space on the right of the text column, on a wide screen only.
  assert.match(css, /@media \(min-width:62rem\) \{\s*main > section \{ display:flow-root; padding-right:max\(calc\(var\(--side\) \+ var\(--side-gap\)\), calc\(100% - var\(--text\)\)\); \}\s*main > section > :is\(\.in-paper, \.side\) \{ float:right; clear:right; width:var\(--side\);/);
  assert.match(css, /\.statement \{[^}]*border-left:3px solid var\(--blue\); background:var\(--surface-blue\)/);
  // Figure colours come from theme tokens, so the two colour modes have them.
  for (const rule of css.match(/\.fig-[\w-]+ \{[^}]*\}/g)) assert.doesNotMatch(rule, /#[0-9a-f]{3,8}\b|rgb\(/i, rule);
  for (const [, name] of html.matchAll(/class="(fig-[\w-]+)/g)) assert.ok(css.includes(`.${name} {`), `style for ${name}`);
});

test('the Tools page follows the shared tools pattern', async () => {
  assert.match(tools, /<link rel="canonical" href="https:\/\/jehlp\.net\/cookie-clicker\/tools\.html">/);
  assert.match(tools, /<img class="site-mark" src="assets\/mark\.png" width="32" height="32" alt="">|<img class="site-mark" src="assets\/mark\.png" alt="" width="32" height="32">/);
  assert.match(tools, /<a class="site-title" href="\.\/">Cookie Clicker<\/a>/);
  assert.match(tools, /<a href="tools\.html" aria-current="page">Tools<\/a>/);
  assert.match(tools, /<a href="paper\.pdf">Paper<\/a>/);
  assert.match(tools, /site-theme\/v2\/reader\.css/);
  assert.match(tools, /<main class="tools-shell">[\s\S]*<section class="tool-list" id="downloads"/);
  assert.match(tools, /<a class="skip-link" href="#downloads">/);
  assert.doesNotMatch(text(tools), /optimal (autoplay|time|play)/i, 'the Tools page does not call the mod optimal');
  await localResources(tools);
});

test('the download card names the patcher version, its archive and its digest', () => {
  const version = patcher.match(/^VERSION = "([^"]+)"/m)[1];
  const card = tools.match(/<p class="tool-version">v([\d.]+) · \d+ KB<\/p>/);
  assert.ok(card, 'version and size');
  assert.equal(card[1], version);
  const download = `https://github.com/JWKNT/cookie-clicker/releases/download/v${version}/Cookie-Monster-Plus-Patcher-v${version}.zip`;
  assert.ok(tools.includes(`href="${download}">Download patcher</a>`));
  assert.ok(tools.includes(`href="https://github.com/JWKNT/cookie-clicker/releases/tag/v${version}">Release notes</a>`));
  assert.match(tools, /<p class="tool-hash"><span>SHA-256<\/span> <code>[0-9a-f]{64}<\/code><\/p>/);
  assert.match(tools, /Game\.LoadMod\('https:\/\/jehlp\.net\/cookie-clicker\/mod\/main\.js'\)/);
});

test('the release manifest verifies every mod file and all source version fields', async () => {
  const manifest = JSON.parse(await readFile(resolve(root, 'mod/manifest.json'), 'utf8'));
  const version = patcher.match(/^VERSION = "([^"]+)"/m)[1];
  assert.equal(manifest.version, version);
  const pkg = JSON.parse(await readFile(resolve(root, 'source/cookie-monster-plus/package.json'), 'utf8'));
  assert.equal(pkg.version, version);
  const data = await readFile(resolve(root, 'source/cookie-monster-plus/src/Data/Moddata.js'), 'utf8');
  const major = data.match(/VersionMajor = '([^']+)'/)[1];
  const minor = data.match(/VersionMinor = '([^']+)'/)[1];
  assert.equal(`${major}.${minor}`, version);
  const info = JSON.parse(await readFile(resolve(root, 'mod/info.txt'), 'utf8'));
  // Steam stores ModVersion as a number, so JSON drops a final decimal zero.
  assert.equal(typeof info.ModVersion, 'number');
  assert.equal(info.ModVersion, Number(`${major}${minor.padStart(2, '0')}`));
  for (const [name, entry] of Object.entries(manifest.files)) {
    const contents = await readFile(resolve(root, 'mod', name));
    assert.equal(contents.length, entry.size, name);
    assert.equal(createHash('sha256').update(contents).digest('hex'), entry.sha256, name);
  }
});

test('original prose has no semicolons', () => {
  assert.doesNotMatch(prose(html), /;/);
  assert.doesNotMatch(prose(tools), /;/);
});

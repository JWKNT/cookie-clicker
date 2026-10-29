import assert from 'node:assert/strict';
import test from 'node:test';
import { access, readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const html = await readFile(resolve(root, 'index.html'), 'utf8');
const tools = await readFile(resolve(root, 'tools.html'), 'utf8');
const patcher = await readFile(resolve(root, 'patcher/install_cookie_monster_plus.py'), 'utf8');
const experiments = ['order', 'lucky', 'interval', 'ascend', 'worth', 'godzamok', 'wrinkler', 'garden'];

const prose = (page) => page
  .replace(/<math[\s\S]*?<\/math>/g, ' ')
  .replace(/<code>[\s\S]*?<\/code>/g, ' ')
  .replace(/<head>[\s\S]*?<\/head>/, ' ')
  .replace(/<[^>]+>/g, ' ')
  .replace(/&[a-z]+;|&#\d+;/g, ' ');

const localResources = async (page) => {
  for (const [, url] of page.matchAll(/(?:src|href)="([^"#][^"]*)"/g)) {
    if (url.startsWith('https://')) continue;
    await access(resolve(root, url === './' ? 'index.html' : url.split('?')[0]));
  }
};

test('nine chapters, unique IDs and working internal navigation', () => {
  const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]);
  assert.equal(ids.length, new Set(ids).size);
  assert.equal((html.match(/<section id=/g) || []).length, 9);
  for (const [, id] of html.matchAll(/href="#([^"]+)"/g)) assert.ok(ids.includes(id), `Unknown anchor: ${id}`);
});

test('every experiment has a host and a no-script fallback', () => {
  for (const id of experiments) {
    const at = html.indexOf(`id="${id}-demo"`);
    assert.ok(at > 0, id);
    assert.ok(html.indexOf('<noscript>', at) > at && html.indexOf('<noscript>', at) - at < 300, `noscript after ${id}`);
  }
  const script = html.match(/<script src="(assets\/explorers\.mjs)[^"]*" type="module">/);
  assert.ok(script, 'explorers module');
});

test('the masthead follows the shared identity contract', () => {
  assert.match(html, /<img class="site-mark" src="assets\/mark\.png" alt="" width="32" height="32">/);
  assert.match(html, /<h1 class="site-title">Cookie Clicker<\/h1>/);
  assert.match(html, /<link rel="canonical" href="https:\/\/jehlp\.net\/cookie-clicker\/">/);
  assert.match(html, /class="site-home" aria-label="Home — jehlp\.net" href="https:\/\/jehlp\.net\/"/);
  assert.match(html, /data-theme-toggle/);
  assert.match(html, /<a class="skip-link" href="#main">/);
  assert.match(html, /<a href="\.\/" aria-current="page">Guide<\/a><a href="tools\.html">Tools<\/a><a href="paper\.pdf">Paper<\/a>/);
  assert.doesNotMatch(html, /github\.com[^"]*"[^>]*>Source<\/a><\/nav>/);
});

test('local resources exist and the paper is a PDF at the site root', async () => {
  await localResources(html);
  const pdf = await readFile(resolve(root, 'paper.pdf'));
  assert.equal(pdf.subarray(0, 5).toString(), '%PDF-');
  await access(resolve(root, 'paper/cookie-clicker-optimal-play.tex'));
  await access(resolve(root, 'assets/fonts/latinmodern-math.otf'));
  await access(resolve(root, 'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('mathematics is native MathML with no TeX left over', () => {
  assert.ok((html.match(/<math[\s>]/g) || []).length >= 100);
  assert.ok(html.includes('<mfrac>') && html.includes('<msup>') && html.includes('<msub>'));
  assert.doesNotMatch(html, /\\\(|\\\)|\\\[|\\\]/);
});

test('the guide has no download section', () => {
  assert.doesNotMatch(html, /id="install"|class="tool-card"/);
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

test('original prose has no semicolons', () => {
  assert.doesNotMatch(prose(html), /;/);
  assert.doesNotMatch(prose(tools), /;/);
});

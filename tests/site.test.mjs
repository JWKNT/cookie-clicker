import assert from 'node:assert/strict';
import test from 'node:test';
import { access, readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const html = await readFile(resolve(root, 'index.html'), 'utf8');
const experiments = ['order', 'lucky', 'interval', 'ascend', 'worth', 'godzamok', 'wrinkler', 'garden'];

test('ten chapters, unique IDs and working internal navigation', () => {
  const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]);
  assert.equal(ids.length, new Set(ids).size);
  assert.equal((html.match(/<section id=/g) || []).length, 10);
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
  assert.doesNotMatch(html, /github\.com[^"]*"[^>]*>Source<\/a><\/nav>/);
});

test('local resources exist and the paper is a PDF', async () => {
  for (const [, url] of html.matchAll(/(?:src|href)="([^"#][^"]*)"/g)) {
    if (url.startsWith('https://')) continue;
    await access(resolve(root, url.split('?')[0]));
  }
  const pdf = await readFile(resolve(root, 'paper/cookie-clicker-optimal-play.pdf'));
  assert.equal(pdf.subarray(0, 5).toString(), '%PDF-');
  assert.match(html, /href="paper\/cookie-clicker-optimal-play\.pdf">Paper<\/a>/);
  await access(resolve(root, 'assets/fonts/latinmodern-math.otf'));
  await access(resolve(root, 'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('mathematics is native MathML with no TeX left over', () => {
  assert.ok((html.match(/<math[\s>]/g) || []).length >= 100);
  assert.ok(html.includes('<mfrac>') && html.includes('<msup>') && html.includes('<msub>'));
  assert.doesNotMatch(html, /\\\(|\\\)|\\\[|\\\]/);
});

test('the download card lists the release archive and its digest', () => {
  assert.match(html, /href="https:\/\/github\.com\/JWKNT\/cookie-clicker\/releases\/download\/v(\d+\.\d+\.\d+)\/Cookie-Monster-Plus-Patcher-v\1\.zip">Download patcher<\/a>/);
  assert.match(html, /<p class="tool-hash"><span>SHA-256<\/span> <code>[0-9a-f]{64}<\/code><\/p>/);
  assert.match(html, /Game\.LoadMod\('https:\/\/jehlp\.net\/cookie-clicker\/mod\/main\.js'\)/);
});

test('original prose has no semicolons', () => {
  const prose = html
    .replace(/<math[\s\S]*?<\/math>/g, ' ')
    .replace(/<code>[\s\S]*?<\/code>/g, ' ')
    .replace(/<head>[\s\S]*?<\/head>/, ' ')
    .replace(/<[^>]+>/g, ' ')
    .replace(/&[a-z]+;|&#\d+;/g, ' ');
  assert.doesNotMatch(prose, /;/);
});

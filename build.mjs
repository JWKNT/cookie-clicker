// Renders src/index.html to index.html: every \( … \) and \[ … \] becomes native MathML (Temml).
// The published page needs no runtime library. Run `node build.mjs`; `--check` fails if index.html is stale.
import { readFile, writeFile } from 'node:fs/promises';
import temml from 'temml';

const root = new URL('./', import.meta.url);
const source = await readFile(new URL('src/index.html', root), 'utf8');

const render = (tex, displayMode) => temml.renderToString(tex.trim(), { displayMode, throwOnError: true, xml: false });
const html = source
  .replace(/\\\[([\s\S]+?)\\\]/g, (_, tex) => render(tex, true))
  .replace(/\\\(([\s\S]+?)\\\)/g, (_, tex) => render(tex, false));
if (/\\\(|\\\)|\\\[|\\\]/.test(html)) throw new Error('Unbalanced TeX delimiters in src/index.html');

const target = new URL('index.html', root);
if (process.argv.includes('--check')) {
  const current = await readFile(target, 'utf8').catch(() => '');
  if (current !== html) {
    console.error('index.html is out of date. Run node build.mjs.');
    process.exit(1);
  }
} else {
  await writeFile(target, html);
  console.log(`Wrote index.html with ${(html.match(/<math[\s>]/g) || []).length} formulas.`);
}

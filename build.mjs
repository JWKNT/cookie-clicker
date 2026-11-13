// Builds index.html from src/index.html.
//
//   node build.mjs           write the page
//   node build.mjs --check   fail if index.html differs from the build
//
// The source is HTML with a small header and a few directives.
//   <!--page { ...JSON... } -->                 title, description, navigation, paper
//   <section id="x" data-title="Title">         a numbered section
//   {{in-paper: Theorem 2.1 | 3 ; Lemma 3.2 | 7}}  links to pages of the paper, directly after
//                                               the section tag
//   class="side"                                a figure or a table for the margin column
//   {{fig:name}} and {{table:name}}             a figure or a table of src/figures.mjs
//   \( ... \) and \[ ... \]                     TeX, which Temml changes to MathML
//
// The published page needs no script. Temml 0.14.0 is the only dependency of the build.
import { readFile, writeFile } from 'node:fs/promises';
import temml from 'temml';
import { figures, tables } from './src/figures.mjs';

const ROOT = 'https://jehlp.net/cookie-clicker/';
const VERSION = { theme: '20261108-justify', guide: '20261113-margin' };
const root = new URL('./', import.meta.url);

const escapeHtml = (value) => String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;');
// The source is HTML, so TeX in it escapes <, > and &. Temml needs the plain characters.
const plainTex = (tex) => tex.trim().replaceAll('&lt;', '<').replaceAll('&gt;', '>').replaceAll('&amp;', '&');

function typesetMath(html) {
  const render = (tex, displayMode) => temml.renderToString(plainTex(tex), { displayMode, throwOnError: true, annotate: false });
  return html
    .replace(/\\\[([\s\S]+?)\\\]/g, (_, tex) => `<div class="equation" role="group" aria-label="Formula" tabindex="0">${render(tex, true)}</div>`)
    .replace(/\\\(([\s\S]+?)\\\)/g, (_, tex) => render(tex, false))
    // A browser can break a line between a formula and the punctuation after it. Hold them together.
    .replace(/(<math>(?:(?!<\/math>)[\s\S])*<\/math>)([,.:;)]+)/g, '<span class="math-nobreak">$1$2</span>');
}

function parseSource(source) {
  const header = source.match(/^<!--page\s*([\s\S]*?)-->\s*/);
  if (!header) throw new Error('src/index.html needs a <!--page {...} --> header');
  const meta = JSON.parse(header[1]);
  for (const key of ['title', 'description']) {
    if (typeof meta[key] !== 'string') throw new Error(`The header needs "${key}"`);
  }
  return { meta, body: source.slice(header[0].length) };
}

function expandDirectives(meta, body) {
  const stops = [];
  let html = body.replace(/<section id="([\w-]+)" data-title="([^"]+)">/g, (_, id, title) => {
    stops.push({ id, title });
    return `<section id="${id}">\n<h2><span class="chapter-number">${stops.length}</span> ${title}</h2>`;
  });
  // The list of the sections is the first item of the first section, so that it is at the top
  // of the margin. On a narrow screen the style sheet puts it after the first paragraphs.
  const contents = `<nav class="contents side" aria-label="Contents"><p class="contents-title">Contents</p><ol>${stops.map(({ id, title }) => `<li><a href="#${id}">${title}</a></li>`).join('')}</ol></nav>\n`;
  if (!/^\s*<section id="start"/.test(html)) throw new Error('The first section must have id="start"');
  html = html.replace(/(<section id="start"[^>]*>\n?)/, `$1${contents}`);
  html = html.replace(/\{\{in-paper:([^}]+)\}\}/g, (_, list) => {
    const links = list.split(';').map((item) => {
      const [, text, page] = item.match(/^\s*([^|]+?)\s*\|\s*(\d+)\s*$/) ?? [];
      if (!text || Number(page) < 1 || Number(page) > meta.paper.pages) throw new Error(`Bad reference "${item.trim()}"`);
      return `<a href="${meta.paper.file}#page=${page}">${text}, page ${page}</a>`;
    });
    // A separator stays on the line of the link before it.
    const items = links.map((link, i) => `<span class="in-paper-item">${link}${i < links.length - 1 ? '<span aria-hidden="true"> ·</span>' : ''}</span>`).join(' ');
    return `<p class="in-paper"><span class="in-paper-label">Paper</span> ${items}</p>`;
  });
  html = html.replace(/\{\{fig:([\w-]+)\}\}/g, (_, figure) => {
    if (!Object.hasOwn(figures, figure)) throw new Error(`Unknown figure ${figure}`);
    return figures[figure]();
  });
  html = html.replace(/\{\{table:([\w-]+)\}\}/g, (_, table) => {
    if (!Object.hasOwn(tables, table)) throw new Error(`Unknown table ${table}`);
    return tables[table]();
  });
  const leftover = html.match(/\{\{[^}]*\}\}/);
  if (leftover) throw new Error(`Unknown directive ${leftover[0]}`);
  return html;
}

function frame(meta, main) {
  const nav = meta.nav.map(({ label, href, current }) => `<a href="${href}"${current ? ' aria-current="page"' : ''}>${escapeHtml(label)}</a>`).join('');
  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="theme-color" content="#fbfaf7"><title>${escapeHtml(meta.title)} · jehlp.net</title><meta name="description" content="${escapeHtml(meta.description)}"><meta property="og:type" content="article"><meta property="og:title" content="${escapeHtml(meta.title)}"><meta property="og:description" content="${escapeHtml(meta.description)}"><meta property="og:url" content="${ROOT}"><meta property="og:site_name" content="jehlp.net"><link rel="canonical" href="${ROOT}"><link rel="icon" href="assets/favicon.png" type="image/png"><script src="https://jehlp.net/site-theme/v2/theme.js?v=${VERSION.theme}"></script><link rel="stylesheet" href="https://jehlp.net/site-theme/v2/base.css?v=${VERSION.theme}"><link rel="stylesheet" href="assets/guide.css?v=${VERSION.guide}"></head>
<body><a class="skip-link" href="#main">Skip to the guide</a><header class="site-header site-header--identity"><div class="site-identity site-brand"><img class="site-mark" src="assets/mark.png" alt="" width="32" height="32"><h1 class="site-title">${escapeHtml(meta.title)}</h1></div><nav aria-label="Main">${nav}<span class="site-utility-pair"><a class="site-home" aria-label="Home — jehlp.net" href="https://jehlp.net/"><span aria-hidden="true">Home</span></a><button type="button" data-theme-toggle="" class="theme-toggle" aria-label="Use dark theme"></button></span></nav></header>
<main id="main" class="tour">
${main.trim()}
</main>
</body></html>
`;
}

export async function buildPage() {
  const { meta, body } = parseSource(await readFile(new URL('src/index.html', root), 'utf8'));
  const main = typesetMath(expandDirectives(meta, body));
  if (/\\[([]|\\[)\]]/.test(main)) throw new Error('TeX remains after the build');
  return frame(meta, main);
}

if (process.argv[1] && new URL(`file://${process.argv[1]}`).pathname === new URL(import.meta.url).pathname) {
  const html = await buildPage();
  const target = new URL('index.html', root);
  if (process.argv.includes('--check')) {
    const current = await readFile(target, 'utf8').catch(() => '');
    if (current !== html) {
      console.error('index.html is out of date. Run node build.mjs.');
      process.exit(1);
    }
    console.log('index.html is up to date');
  } else {
    await writeFile(target, html);
    console.log(`Wrote index.html with ${(html.match(/<math[\s>]/g) || []).length} formulas.`);
  }
}

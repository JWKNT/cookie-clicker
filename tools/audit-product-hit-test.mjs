import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createRuntime } from '../model/runtime.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const runtime = createRuntime({ recordAudit: false });
const hash = value => createHash('sha256').update(value).digest('hex');
const css = readFileSync(join(runtime.source.directory, 'style.css'), 'utf8');
const escape = value => String(value).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/"/g, '&quot;');
// Serialize the live adapter tree, including native mutations after launch.
// No script, inline event handler or player save is loaded in the renderer.
const serialize = node => {
  if (node.nodeType === 3) return escape(node.textContent);
  if (node.nodeType !== 1 || ['SCRIPT', 'LINK', 'META', 'STYLE'].includes(node.tagName)) return '';
  const attributes = { ...node.attributes, id: node.id, class: node.className };
  delete attributes.style;
  const styles = Object.entries(node.style).filter(([, value]) => typeof value !== 'function');
  if (styles.length) attributes.style = styles.map(([key, value]) => `${key.replace(/[A-Z]/g, letter => '-' + letter.toLowerCase())}:${value}`).join(';');
  const attrs = Object.entries(attributes).filter(([key, value]) => !key.startsWith('on') && value !== '')
    .map(([key, value]) => ` ${key}="${escape(value)}"`).join('');
  return `<${node.tagName.toLowerCase()}${attrs}>${node.childNodes.map(serialize).join('')}</${node.tagName.toLowerCase()}>`;
};
const cases = [{ name: 'fresh-locked', body: serialize(runtime.context.document.body), hitIds: [0, 1] }];
runtime.Game.cookiesEarned = 2 ** 100;
runtime.advance(200);
cases.push({ name: 'earned-threshold-fixture', body: serialize(runtime.context.document.body), hitIds: [0, 1, 2, 19] });
const inspect = function (input) {
  const sheet = new CSSStyleSheet(); sheet.replaceSync(input.css);
  document.adoptedStyleSheets = [sheet];
  const cases = [];
  for (const example of input.cases) {
  const parsed = new DOMParser().parseFromString(example.body, 'text/html');
  document.body.replaceWith(document.importNode(parsed.body, true));
  // CSP rejects serialized style attributes. Set the same native style values
  // through the CSSOM, which is the channel native game code uses as well.
  for (const element of document.querySelectorAll('[style]')) element.style.cssText = element.getAttribute('style');
  const section = document.getElementById('sectionRight');
  const results = [];
  for (const id of [0, 1, 2, 19]) {
    const product = document.getElementById('product' + id);
    product.scrollIntoView({ block: 'center' });
    const box = product.getBoundingClientRect();
    const sectionBox = section.getBoundingClientRect();
    const x = (Math.max(box.left, sectionBox.left) + Math.min(box.right, sectionBox.right)) / 2;
    const y = (Math.max(box.top, sectionBox.top) + Math.min(box.bottom, sectionBox.bottom)) / 2;
    const hit = document.elementFromPoint(x, y);
    let bubbledClicks = 0;
    product.addEventListener('click', () => { bubbledClicks++; });
    hit?.dispatchEvent(new MouseEvent('click', { bubbles: true, clientX: x, clientY: y }));
    const style = getComputedStyle(product);
    results.push({ id, className: product.className, opacity: style.opacity, display: style.display,
      visibility: style.visibility, pointerEvents: style.pointerEvents,
      rectangle: { left: box.left, top: box.top, width: box.width, height: box.height },
      point: { x, y }, scrollTop: section.scrollTop, hitId: hit?.id || '',
      hitInsideProduct: !!hit && product.contains(hit), bubbledClicks });
  }
  cases.push({ name: example.name, expectedHitIds: example.hitIds,
    section: { overflowY: getComputedStyle(section).overflowY, scrollHeight: section.scrollHeight, clientHeight: section.clientHeight }, results });
  }
  return { viewport: { width: innerWidth, height: innerHeight }, cssRules: sheet.cssRules.length, cases };
};
const native = runNativeBrowser(inspect.toString(), { css, cases });
if (!native.result.cases.every(example => example.results.every(row =>
  row.hitInsideProduct === example.expectedHitIds.includes(row.id) && row.bubbledClicks === (example.expectedHitIds.includes(row.id) ? 1 : 0))))
  throw new Error('A native product row failed hit testing: ' + JSON.stringify(native.result));
const output = { schemaVersion: 1, scope: 'isolated-pinned-browser-layout-and-hit-testing',
  proves: ['Fresh visible locked rows receive a bubbling click', 'The generic toggledOff rule hides later product rows from hit testing', 'Unlocked later rows receive a click after ordinary store scrolling'],
  doesNotProve: ['A complete native new-save strategy', 'An exhaustive action-space refinement', 'Trusted-input event identity; the event is dispatched to the native hit-test result'],
  command: 'node tools/audit-product-hit-test.mjs', sourceHashes: { ...runtime.source.hashes, 'style.css': hash(css) },
  fixturePremises: ['The second case assigns cookiesEarned=2^100, then runs 200ms of native timers solely to exercise unlocked store layout'],
  generatedMarkupSha256: cases.map(example => ({ name: example.name, sha256: hash(example.body) })),
  runtimeSha256: hash(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  nativeClickProductSource: String(runtime.Game.ClickProduct), ...native };
writeFileSync(new URL('../model/product-hit-test-witness.json', import.meta.url), JSON.stringify(output, null, 2) + '\n');
console.log(JSON.stringify({ version: native.versions.chrome, cases: native.result.cases }, null, 2));

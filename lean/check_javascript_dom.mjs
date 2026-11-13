/** Native DOM comparisons use an isolated bundle, never the game entry/save. */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { runNativeBrowser } from '../model/native-browser.mjs';
import { loadGameSource } from '../model/game-source.mjs';

const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index));
const cases = [];
const fragment = (input, context = 'div', extra = {}) => cases.push({ operation: 'fragment', context, units: units(input), ...extra });
for (const input of [
  '', 'plain é😀\ud800', 'A\r\nB\rC', 'a &amp; b &#x1f600;', '<DIV ID="a" id="b" CLASS=x>text</DIV>',
  '<input disabled value="A&amp;B" data-icon=3>', '<div/>x<span>y</span>', '<br><hr/><img src="data:,"></br>',
  '<div><b>bold</b><q>quote</q><small>small</small></div>', '<!--<a onclick="throw 1">inert</a>--><span>x</span>',
  '<a onclick="x=&quot;a&quot;;" href="data:,">link</a>', '<span x="&notit; &amp= &notin;">&notit; &amp= &notin;</span>',
  '<textarea>\nA&amp;B<br></textarea><b>end</b>', '<textarea>&#10;abc</textarea>', '<title>A&amp;B</title>',
  '<style>.x:before{content:"<b>&amp;"}</style><div>x</div>', '<script>var x="&amp;";</script><div>x</div>',
  '<pre>\nline</pre><pre>&#10;line</pre>', '<pre><!--x-->\nline</pre>', '<div><span>unclosed',
  '<select><option value="1">One</option><option selected value="2">Two</option></select>',
  'a < 3 and 4 > 2', '<sig data-x="é">x</sig>', '<div a="1"b="2" a="3"></div>',
]) fragment(input);
for (const context of ['body', 'div', 'span', 'textarea', 'title', 'style', 'pre', 'input']) fragment('A &amp; B\r\nC', context);
fragment('<option value="1">One</option><option>Two</option>', 'select');
for (const input of ['<table><tr><td>x</td></tr></table>', '<col>', '<form><div>x</div></form>', '<b><i>x</b></i>', '<p>x<div>y</div>', '<a>x<a>y</a>', '<!--x--!>', '<!-->', '<!--->', '<script><!--<script></script>--></script>', '<svg><circle/></svg>', '<div x="unclosed', '\0']) fragment(input, 'div', { expectedStatus: 'unsupported' });
fragment('text', 'table', { expectedStatus: 'unsupported' });
fragment('<div>x</div>', 'div', { fuel: 0, expectedStatus: 'fuel' });
const source = loadGameSource();
cases.push({ operation: 'document', units: units(source.sources['index.html']), sourceHash: source.hashes['index.html'] });
for (const document of [
  '<!DOCTYPE html><html><head><title>x</title></head><body><div>x</div></body></html>',
  '<!--before--><!doctype html><!--after doctype--><html>\n<!--before head--><head>\n<meta name=x>\n</head>\n<!--between--><body>x</body>\n<!--after body--></html>\n<!--after html-->',
  '\ufeff<!doctype html>\r\n<html><head><style>x{content:"<b>"}</style><script>var x="</body>";</script></head><body>a</body>\n</html>\n',
]) cases.push({ operation: 'document', units: units(document) });
for (const tail of ['</body><!--a--></html><!--b-->', '</body>\n<!--a--></html><!--b-->',
  '</body><!--a-->\n</html><!--b-->', '</body></html>\n<!--b-->', '</body>\n</html>\n<!--b-->']) {
  cases.push({ operation: 'document', units: units('<!doctype html><html><head></head><body>x' + tail) });
}
for (const document of ['<html><head></head><body></body></html>', '<!doctype html><html><head>nonwhite</head><body></body></html>', '<!doctype html><html><head></head><body><div>x</body></html>']) {
  cases.push({ operation: 'document', units: units(document), expectedStatus: 'unsupported' });
}

const entities = JSON.parse(readFileSync(new URL('../model/standards/html-entities.json', import.meta.url)));
for (const name of Object.keys(entities)) {
  for (const attribute of [false, true]) {
    for (const suffix of ['', 'x=']) cases.push({ operation: 'decode', attribute, units: units(name + suffix) });
  }
}
for (const value of [0, 1, 9, 10, 13, 31, 127, ...Array.from({ length: 32 }, (_, i) => 128 + i), 0xd800, 0xdfff, 0x10000, 0x10ffff, 0x110000, 999999999]) {
  for (const reference of [`&#${value};`, `&#${value}x`, `&#x${value.toString(16)};`, `&#X${value.toString(16)}x`]) {
    cases.push({ operation: 'decode', attribute: false, units: units(reference) });
  }
}
for (const text of ['&unknown;', '&;', '&#;', '&#x;', '&notit;', '&amp=', '&ltx', '&&amp;', '&CounterClockwiseContourIntegral;']) {
  for (const attribute of [false, true]) cases.push({ operation: 'decode', attribute, units: units(text) });
}
const executable = fileURLToPath(new URL('.lake/build/bin/jsdomsyntaxcheck', import.meta.url));
const child = spawnSync(executable, [], { input: JSON.stringify(cases), encoding: 'utf8', timeout: 120000, maxBuffer: 32 * 1024 * 1024 });
if (child.error) throw child.error;
assert.equal(child.status, 0, child.stderr);
const actual = JSON.parse(child.stdout);
assert.equal(actual.length, cases.length);
const worker = function (cases) {
  const units = text => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i));
  const encode = node => {
    if (node.nodeType === 3) return { type: 'text', units: units(node.data) };
    if (node.nodeType === 8) return { type: 'comment', units: units(node.data) };
    if (node.nodeType === 10) return { type: 'doctype', name: node.name, publicId: node.publicId, systemId: node.systemId };
    if (node.nodeType === 1) return { type: 'element', name: node.localName,
      attributes: Array.from(node.attributes, a => ({ name: a.name, units: units(a.value) })),
      children: Array.from(node.childNodes, encode) };
    throw new Error('Unexpected native node type ' + node.nodeType);
  };
  return cases.map(c => {
    if (c.expectedStatus) return { status: c.expectedStatus };
    const input = String.fromCharCode(...c.units);
    if (c.operation === 'document') {
      // The pinned file is UTF-8 with a BOM; byte decoding consumes that marker
      // before HTML tokenization. DOMParser takes already-decoded JS strings.
      const node = new DOMParser().parseFromString(input.replace(/^\ufeff/, ''), 'text/html');
      return { status: 'parsed', nodes: Array.from(node.childNodes, encode) };
    }
    if (c.operation === 'decode') {
      if (c.attribute) {
        const node = document.createElement('div');
        node.innerHTML = '<span data-value="' + input.replace(/"/g, '&quot;') + '"></span>';
        return { status: 'decoded', units: units(node.firstChild.getAttribute('data-value')) };
      }
      const node = document.createElement('textarea'); node.innerHTML = input;
      return { status: 'decoded', units: units(node.textContent) };
    }
    const node = document.createElement(c.context); node.innerHTML = input;
    return { status: 'parsed', nodes: Array.from(node.childNodes, encode) };
  });
};
const native = runNativeBrowser(worker.toString(), cases);
for (let index = 0; index < cases.length; index += 1) {
  const observed = cases[index].expectedStatus ? { status: actual[index].status } : actual[index];
  assert.deepEqual(observed, native.result[index], JSON.stringify({ index, case: cases[index] }));
}
console.log(JSON.stringify({ cases: cases.length, passed: cases.length, identity: native.identity,
  renderer: native.renderer, executableHash: native.executableHash,
  gameEntryPointExecuted: native.gameEntryPointExecuted, externalNetworking: native.externalNetworking,
  fullHtmlParserVerified: false }));

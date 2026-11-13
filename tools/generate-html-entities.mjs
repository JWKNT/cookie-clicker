import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const source = new URL('../model/standards/html-entities.json', import.meta.url);
const metadata = JSON.parse(readFileSync(new URL('../model/standards/html-entities.metadata.json', import.meta.url)));
const bytes = readFileSync(source);
if (createHash('sha256').update(bytes).digest('hex') !== metadata.sha256) throw new Error('HTML entity data hash mismatch');
const entries = Object.entries(JSON.parse(bytes)).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
if (entries.length !== metadata.entries) throw new Error('HTML entity entry count mismatch');
const rows = entries.map(([name, value]) => {
  if (!/^&[A-Za-z][A-Za-z0-9]*;?$/.test(name)) throw new Error(`Unexpected entity name ${name}`);
  const units = Array.from({ length: value.characters.length }, (_, i) => value.characters.charCodeAt(i));
  return `  (${JSON.stringify(name.slice(1))}, [${units.join(', ')}])`;
});
const chunks = [];
for (let start = 0; start < rows.length; start += 100) {
  chunks.push(`private def chunk${chunks.length} : Array (String × JSString) := #[\n${rows.slice(start, start + 100).join(',\n')}\n]\n`);
}
const output = `import CookieClicker.JavaScriptSyntax\n\n/-! Generated from ${metadata.url}\nSHA-256: ${metadata.sha256}\nRun node tools/generate-html-entities.mjs to reproduce.\nThe table is data; parser/native refinement is a separate obligation. -/\nnamespace CookieClicker.JavaScript.HtmlEntities\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\n\n${chunks.join('\n')}\ndef entries : Array (String × JSString) := ${chunks.map((_, i) => `chunk${i}`).join(' ++ ')}\n\nend CookieClicker.JavaScript.HtmlEntities\n`;
const target = fileURLToPath(new URL('../lean/CookieClicker/JavaScriptHtmlEntities.lean', import.meta.url));
if (process.argv.includes('--check')) {
  if (readFileSync(target, 'utf8') !== output) throw new Error('Generated HTML entity data is stale');
} else writeFileSync(target, output);
console.log(JSON.stringify({ entries: entries.length, sha256: metadata.sha256 }));

import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { compilePinnedGameAst } from '../model/javascript-ast.mjs';

const args = process.argv.slice(2);
const value = flag => { const i = args.indexOf(flag); return i < 0 ? undefined : args[i + 1]; };
const output = value('--output');
if (!output) throw new Error('Use --output PATH to write the compiled pinned-source AST');
const artifact = compilePinnedGameAst({ sourceDirectory: value('--source-directory') });
writeFileSync(resolve(output), `${JSON.stringify(artifact)}\n`);
console.log(JSON.stringify({ schema: artifact.schema, output: resolve(output), pinnedFiles: artifact.coverage.pinnedFiles,
  units: artifact.units.length, nodes: artifact.nodes.length, functions: artifact.functions.length,
  generatedHandlers: artifact.generatedHandlers.reduce((counts, h) => ({ ...counts, [h.status]: (counts[h.status] || 0) + 1 }), {}),
  inventory: artifact.inventory, javascriptSemanticsVerified: false }));

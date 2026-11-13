import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const input = fileURLToPath(new URL('../model/game-assets.json', import.meta.url));
const output = fileURLToPath(new URL('../lean/CookieClicker/JavaScriptBrowserAssets.lean', import.meta.url));
const bytes = readFileSync(input);
const manifest = JSON.parse(bytes);
const digest = createHash('sha256').update(bytes).digest('hex');
const quote = value => JSON.stringify(value);
const numberBits = value => {
  if (typeof value !== 'number' || !Number.isFinite(value)) throw new Error('Expected finite captured media duration');
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, value, false);
  return view.getBigUint64(0, false).toString();
};
const rows = manifest.assets.map(asset => {
  if (asset.native.status !== 'loaded') throw new Error(`Unexpected unresolved asset ${asset.path}`);
  if (!/^[A-Za-z0-9_./+ -]+$/.test(asset.path)) throw new Error(`Unreviewed asset path ${asset.path}`);
  let kind;
  if (asset.mime.startsWith('image/')) {
    if (![asset.native.naturalWidth, asset.native.naturalHeight].every(n => Number.isSafeInteger(n) && n > 0)) {
      throw new Error(`Invalid captured image size: ${asset.path}`);
    }
    kind = `.image ${asset.native.naturalWidth} ${asset.native.naturalHeight}`;
  } else if (asset.mime === 'audio/mpeg') {
    kind = `.audio ${numberBits(asset.native.duration)} ${asset.native.readyState} ${asset.native.networkState}`;
  } else throw new Error(`Unsupported captured asset MIME ${asset.mime}`);
  return `  ⟨${quote(asset.path)}, ${quote(asset.mime)}, ${asset.byteLength}, ${quote(asset.sha256)}, (${kind})⟩`;
});
const chunks = [];
for (let i = 0; i < rows.length; i += 64) {
  chunks.push(`private def chunk${chunks.length} : Array Asset := #[\n${rows.slice(i, i + 64).join(',\n')}\n]\n`);
}
const source = `import CookieClicker.JavaScriptSyntax

/-! Generated captured local-resource metadata. Image/audio bytes are not stored
here. Native decoding, loading-event ordering and rendering need separate
refinement; these observations are explicit host data, not proved decoders.
Reproduce with node tools/generate-browser-assets.mjs.
-/
namespace CookieClicker.JavaScript.BrowserAssets

inductive Metadata where
  | image (width height : Nat)
  | audio (duration : UInt64) (readyState networkState : Nat)
  deriving Repr, DecidableEq

structure Asset where
  path : String
  mime : String
  byteLength : Nat
  sha256 : String
  metadata : Metadata
  deriving Repr, DecidableEq

def manifestSha256 : String := ${quote(digest)}
def executableSha256 : String := ${quote(manifest.executableSha256)}

${chunks.join('\n')}
def assets : Array Asset := ${chunks.map((_, i) => `chunk${i}`).join(' ++ ')}

end CookieClicker.JavaScript.BrowserAssets
`;
if (process.argv.slice(2).join(' ') === '--check') {
  if (readFileSync(output, 'utf8') !== source) throw new Error('Generated Lean browser asset metadata is stale');
} else if (process.argv.length === 2) writeFileSync(output, source);
else throw new Error('Expected no arguments or --check');
console.log(JSON.stringify({ input, output, assets: rows.length, manifestSha256: digest }));

import { createHash } from 'node:crypto';
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { extname, join } from 'node:path';
import { loadGameSource } from '../model/game-source.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

// Read the installation, without loading its app entry or any player save.
// Store metadata and hashes only. Asset bytes stay in the local audit process.
const source = loadGameSource();
const types = { '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
  '.gif': 'image/gif', '.ico': 'image/x-icon', '.mp3': 'audio/mpeg' };
function paths(directory, prefix = '') {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const relative = prefix + entry.name;
    return entry.isDirectory() ? paths(join(directory, entry.name), relative + '/') : [relative];
  });
}
const assets = ['img', 'snd'].flatMap(directory => paths(join(source.directory, directory))
  .map(path => directory + '/' + path)).sort().filter(path => types[extname(path)]).map(path => {
  const bytes = readFileSync(join(source.directory, path));
  const mime = types[extname(path)];
  return { path, mime, byteLength: bytes.length,
    sha256: createHash('sha256').update(bytes).digest('hex'),
    data: `data:${mime};base64,${bytes.toString('base64')}` };
});
if (process.argv.includes('--check-files')) {
  const saved = JSON.parse(readFileSync(new URL('../model/game-assets.json', import.meta.url)));
  const identities = entries => entries.map(({ path, mime, byteLength, sha256 }) => ({ path, mime, byteLength, sha256 }));
  if (JSON.stringify(identities(assets)) !== JSON.stringify(identities(saved.assets)) ||
      JSON.stringify(source.hashes) !== JSON.stringify(saved.sourceHashes)) {
    throw new Error('Installed source or asset identities differ from the pinned metadata manifest');
  }
  console.log(JSON.stringify({ checkedLocalAssetIdentities: assets.length, capturedNewMetadata: false }));
  process.exit(0);
}
const report = runNativeBrowser(`async assets => {
  const output = new Array(assets.length);
  let next = 0;
  async function worker() {
    for (;;) {
      const index = next++;
      if (index >= assets.length) return;
      const asset = assets[index];
      output[index] = await new Promise(resolve => {
        const image = asset.mime.startsWith('image/');
        const element = image ? new Image() : new Audio();
        let timer;
        let finished = false;
        const done = status => {
          if (finished) return;
          finished = true;
          clearTimeout(timer);
          resolve(image ? { status, complete: element.complete,
            naturalWidth: element.naturalWidth, naturalHeight: element.naturalHeight,
            width: element.width, height: element.height }
            : { status, readyState: element.readyState, networkState: element.networkState,
                duration: Number.isFinite(element.duration) ? element.duration : String(element.duration),
                errorCode: element.error ? element.error.code : null });
          if (!image) { element.removeAttribute('src'); element.load(); }
        };
        timer = setTimeout(() => done('timeout'), 15000);
        element.addEventListener(image ? 'load' : 'loadedmetadata', () => done('loaded'), { once: true });
        element.addEventListener('error', () => done('error'), { once: true });
        if (!image) { element.preload = 'metadata'; element.muted = true; }
        element.src = asset.data;
      });
    }
  }
  await Promise.all(Array.from({ length: 8 }, worker));
  return output;
}`, assets.map(({ mime, data }) => ({ mime, data })), { allowDataAssets: true, timeout: 180000 });
if (!Array.isArray(report.result) || report.result.length !== assets.length) throw new Error('Incomplete asset report');
if (report.result.some(value => value.status === 'timeout')) throw new Error('Native asset metadata timed out');
const manifest = {
  schema: 1, gameVersion: source.version, sourceHashes: source.hashes,
  interpretation: 'Pinned local file hashes and native Chromium metadata, read from data URLs in an isolated renderer. This is not a proof of decoder behavior, file-URL task ordering, audio playback, canvas pixels, or zero-latency load scheduling.',
  versions: report.versions, executableSha256: report.executableHash,
  gameEntryPointExecuted: report.gameEntryPointExecuted, externalNetworking: report.externalNetworking,
  auditConfiguration: report.auditConfiguration,
  assets: assets.map(({ data, ...metadata }, index) => ({ ...metadata, native: report.result[index] })),
};
writeFileSync(new URL('../model/game-assets.json', import.meta.url), JSON.stringify(manifest, null, 2) + '\n');
console.log(JSON.stringify({ assets: assets.length,
  images: assets.filter(asset => asset.mime.startsWith('image/')).length,
  audio: assets.filter(asset => asset.mime.startsWith('audio/')).length,
  failures: manifest.assets.filter(asset => asset.native.status !== 'loaded').map(({ path, native }) => ({ path, native })) }));

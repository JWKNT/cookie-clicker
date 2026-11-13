/** Pure clock extension checks; no source Value integration or full-clock refinement claim. */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

const buffer = new ArrayBuffer(8), view = new DataView(buffer);
const toBits = n => { view.setFloat64(0, n); return view.getBigUint64(0).toString(); };
const fromBits = bits => { view.setBigUint64(0, BigInt(bits)); return view.getFloat64(0); };
const unitText = text => Array.from(text, c => c.charCodeAt(0));
const limit = 8640000000000000n;
function normalize({ numerator, scale }) {
  while (scale > 0 && numerator % 2n === 0n) { numerator /= 2n; scale--; }
  return { numerator, scale };
}
function dyadic(bits) {
  bits = BigInt(bits);
  const exponent = Number(bits >> 52n & 2047n), fraction = bits & ((1n << 52n) - 1n);
  assert.notEqual(exponent, 2047);
  const mantissa = exponent ? fraction + (1n << 52n) : fraction;
  const e = exponent ? exponent - 1075 : -1074;
  const signed = bits >> 63n ? -mantissa : mantissa;
  return normalize(e >= 0 ? { numerator: signed << BigInt(e), scale: 0 } : { numerator: signed, scale: -e });
}
function sum(a, b) {
  const scale = Math.max(a.scale, b.scale);
  return normalize({ numerator: (a.numerator << BigInt(scale - a.scale)) + (b.numerator << BigInt(scale - b.scale)), scale });
}
function decimal(d) {
  d = normalize(d);
  const sign = d.numerator < 0n ? '-' : '', magnitude = d.numerator < 0n ? -d.numerator : d.numerator;
  if (!d.scale) return sign + magnitude;
  const digits = (magnitude * 5n ** BigInt(d.scale)).toString().padStart(d.scale + 1, '0');
  return sign + digits.slice(0, -d.scale) + '.' + digits.slice(-d.scale);
}
function inside(d) { return (d.numerator < 0n ? -d.numerator : d.numerator) <= limit << BigInt(d.scale); }
function encoded(d, nativeBits = null, nativeText = null) {
  if (nativeBits !== null) d = dyadic(nativeBits);
  else if (inside(d)) { nativeBits = toBits(Number(decimal(d))); d = dyadic(nativeBits); }
  d = normalize(d);
  const divisor = 1n << BigInt(d.scale);
  const floor = d.numerator / divisor - (d.numerator < 0n && d.numerator % divisor ? 1n : 0n);
  return { kind: nativeBits === null ? 'exact' : 'native', bits: nativeBits,
    numerator: d.numerator.toString(), scale: d.scale,
    text: unitText(nativeBits === null ? decimal(d) : nativeText ?? String(fromBits(nativeBits))), floor: floor.toString() };
}
const nativeTime = n => ({ kind: 'native', bits: toBits(n) });
const exactTime = d => ({ kind: 'exact', numerator: d.numerator.toString(), scale: d.scale });
const requests = [], expected = [], finite = [];
for (const n of [-8640000000000000, -8639999999999999, -(2**40), -1, -0, 0, 1, 1793275200000, 2**52, 8639999999999999, 8640000000000000]) {
  for (const duration of [-1000, -1, -.1, -Number.MIN_VALUE, -0, 0, Number.MIN_VALUE, .1, 1, 1000]) {
    if (!inside(sum(dyadic(toBits(n)), dyadic(toBits(duration))))) continue;
    finite.push({ op: 'add', left: toBits(n), right: toBits(duration) });
    requests.push({ op: 'add', time: nativeTime(n), duration: toBits(duration) });
  }
}
let seed = 0x12345678;
const random = () => (seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0);
for (let i = 0; i < 300; i++) {
  const n = Number(BigInt(random()) * 1048576n + BigInt(random() % 1048576));
  const duration = (random() - 2147483648) / 128;
  finite.push({ op: 'add', left: toBits(n), right: toBits(duration) });
  requests.push({ op: 'add', time: nativeTime(n), duration: toBits(duration) });
}
for (const [a, b] of [[0, -0], [-0, 0], [8640000000000000, -8640000000000000], [1793275200000, 1793275199999], [-.1, .1]]) {
  finite.push({ op: 'difference', left: toBits(a), right: toBits(b) });
  requests.push({ op: 'difference', left: nativeTime(a), right: nativeTime(b) });
}
const worker = `const fs=require('fs'),b=new ArrayBuffer(8),v=new DataView(b);function get(s){v.setBigUint64(0,BigInt(s));return v.getFloat64(0);}function bits(n){v.setFloat64(0,n);return v.getBigUint64(0).toString();}process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{const n=c.op==='add'?get(c.left)+get(c.right):get(c.left)-get(c.right);return{bits:bits(n),text:String(n)};})));`;
const native = process.argv.includes('--engine');
let nativeResults;
if (native) nativeResults = runNativeEngine(worker, finite);
else {
  const child = spawnSync(process.execPath, ['-e', worker], { input: JSON.stringify(finite), encoding: 'utf8' });
  assert.equal(child.status, 0, child.stderr); nativeResults = JSON.parse(child.stdout);
}
for (let i = 0; i < finite.length; i++) expected.push(finite[i].op === 'difference'
  ? { bits: nativeResults[i].bits } : encoded(null, nativeResults[i].bits, nativeResults[i].text));
const nativeCases = requests.length;
for (const n of [limit, limit + 1n, 1n << 54n, 1n << 100n, 1n << 1200n, -(1n << 100n)]) {
  for (const duration of [1, -1, .1, -.1, Number.MIN_VALUE, -Number.MIN_VALUE, Infinity, -Infinity, NaN]) {
    const d = { numerator: n, scale: 0 };
    requests.push({ op: 'add', time: exactTime(d), duration: toBits(duration) });
    if (!Number.isFinite(duration)) expected.push({ kind: 'ordinary', bits: toBits(duration) });
    else expected.push(encoded(sum(d, dyadic(toBits(duration)))));
  }
}
for (const scale of [0, 1, 3, 52, 1074]) for (const sign of [1n, -1n]) {
  const d = { numerator: sign * ((1n << BigInt(100 + scale)) + 3n), scale };
  requests.push({ op: 'time', time: exactTime(d) }); expected.push(encoded(d));
  requests.push({ op: 'parse', text: decimal(d) }); expected.push(encoded(d));
  requests.push({ op: 'difference', left: exactTime(d), right: exactTime({ ...d, numerator: d.numerator - (1n << BigInt(scale)) }) });
  expected.push({ bits: toBits(1) });
}
for (const n of [0n, -1n, limit, limit+1n, 1n<<100n, -(1n<<1200n)]) {
  requests.push({ op: 'integer', value: n.toString() }); expected.push({ text: n.toString(), decoded: encoded({ numerator: n, scale: 0 }) });
}
for (const text of ['8640000000000000.125', '-8640000000000000.125']) {
  const negative = text[0] === '-', numerator = (limit*8n + 1n) * (negative ? -1n : 1n);
  requests.push({ op: 'parse', text }); expected.push(encoded({ numerator, scale: 3 }));
}
requests.push({ op: 'parse', text: '8640000000000000.1' }); expected.push({ error: 'CookieClicker.JavaScript.ClockValue.Codec.ReadError.nonDyadicOutsideNativePrefix' });
requests.push({ op: 'parse', text: '123junk' }); expected.push({ error: 'CookieClicker.JavaScript.ClockValue.Codec.ReadError.invalidDecimal' });

const child = spawnSync(process.env.LAKE || join(homedir(), '.elan/bin/lake'), ['env', 'lean', '--run', 'JavaScriptClockValueMain.lean'], {
  cwd: fileURLToPath(new URL('.', import.meta.url)), input: JSON.stringify(requests), encoding: 'utf8', timeout: 120000, maxBuffer: 32*1024*1024,
});
if (child.error) throw child.error;
assert.equal(child.status, 0, child.stderr || child.stdout);
const actual = JSON.parse(child.stdout); assert.equal(actual.length, expected.length);
for (let i=0; i<actual.length; i++) assert.deepEqual(actual[i], expected[i], JSON.stringify(requests[i]));
console.log(JSON.stringify({ passed: actual.length, nativePrefixComparisons: nativeCases,
  extensionReference: 'Independent BigInt exact dyadic arithmetic and decimal rendering; out-of-range cases are the selected extension, not native Date behavior.',
  comparisonEngine: native ? inspectNativeEngine() : { node: process.version, v8: process.versions.v8 }, sourceClockIntegrationVerified: false }));

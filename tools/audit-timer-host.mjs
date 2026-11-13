import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import assert from 'node:assert/strict';
import { chromium87TimerDelay, nextChromiumTimerId } from '../model/runtime.mjs';

const root = new URL('../model/browser-source/chromium-87/', import.meta.url);
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const paths = {
  'dom_timer.cc': 'third_party/blink/renderer/core/frame/dom_timer.cc',
  'dom_timer_coordinator.cc': 'third_party/blink/renderer/core/frame/dom_timer_coordinator.cc',
  'dom_timer_coordinator.h': 'third_party/blink/renderer/core/frame/dom_timer_coordinator.h',
  'window_or_worker_global_scope.idl': 'third_party/blink/renderer/core/frame/window_or_worker_global_scope.idl',
  'timer.cc': 'third_party/blink/renderer/platform/timer.cc',
  'LICENSE': 'LICENSE',
};
const sources = Object.entries(paths).map(([file, path]) => ({ file,
  url: `https://github.com/chromium/chromium/blob/87.0.4280.141/${path}`,
  sha256: sha256(readFileSync(new URL(file, root))) }));
assert.equal(chromium87TimerDelay(1000 / 30), 33);
assert.equal(chromium87TimerDelay(0, 3), 1);
assert.equal(chromium87TimerDelay(0, 4), 4);
assert.equal(nextChromiumTimerId(0x7fffffff, id => id === 1), 2);
const result = {
  schemaVersion: 1,
  scope: 'pinned-browser-source-and-runtime-diagnostics-not-a-compiler-refinement-proof',
  reproduction: 'node tools/audit-timer-host.mjs',
  installedFrameworkVersion: '11.5.0',
  frameworkVersionEvidence: 'Contents/Frameworks/Electron Framework.framework/Resources/Info.plist: CFBundleVersion',
  officialRelease: 'https://releases.electronjs.org/release/v11.5.0',
  chromiumVersion: '87.0.4280.141', v8Version: '8.7.220.31',
  timerSemantics: 'chromium-87-long-min1-preincrement5-zero-host-latency-v1',
  sources,
  rules: {
    timeoutConversion: 'Web IDL signed long, before native delay clamps',
    minimumDelayMilliseconds: 1,
    nesting: 'Increment before the >=5 test; minimum4ms at that new nesting level',
    nestedZeroDelayFireOffsetsMs: [1, 2, 3, 4, 8, 12, 16, 20],
    interval: 'Schedule the next task before its callback; callback-created timers inherit the current task nesting, before the interval increment',
    activeHtmlTimerIdMaximum: 2147483647,
    idAllocation: 'Circular positive signed32 IDs; skip every active ID; a fully occupied native allocator does not return',
    nativeLoopTimerMilliseconds: 33,
    inputAndAssetLatency: 'Zero; this does not remove the native timer minimum',
  },
  runtimeSha256: sha256(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  remainingCorrespondence: [
    'The browser scheduler and compiler have not been formally refined to this adapter',
    'The adapter uses deterministic deadline/initialization order across timer task categories',
    'Timer-ID exhaustion is reported as a diagnostic error, not silently scored as game failure',
    'Runtime clock/calendar arithmetic is still finite host JavaScript; the accepted unbounded mathematical clock is a separate model',
  ],
};
writeFileSync(new URL('../model/timer-host-witness.json', import.meta.url), JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify({ sources: sources.length, timerSemantics: result.timerSemantics, nativeLoopTimerMilliseconds: 33 }));

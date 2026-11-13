import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { createRuntime, chromium87TimerDelay, nextChromiumTimerId } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const engineTest = (name, fn) => test(name, { skip: !hasGameSource() && 'Pinned Steam source is required' }, fn);

test('Timer host evidence pins the installed Electron release and the audited Chromium sources', () => {
  const witness = JSON.parse(readFileSync(new URL('../model/timer-host-witness.json', import.meta.url)));
  assert.equal(witness.installedFrameworkVersion, '11.5.0');
  assert.equal(witness.chromiumVersion, '87.0.4280.141');
  assert.equal(witness.sources.length, 6);
  for (const source of witness.sources) {
    const content = readFileSync(new URL(`../model/browser-source/chromium-87/${source.file}`, import.meta.url));
    assert.equal(createHash('sha256').update(content).digest('hex'), source.sha256);
  }
  assert.equal(witness.rules.activeHtmlTimerIdMaximum, 2147483647);
});

test('Chromium 87 converts signed Web IDL long, clamps nesting before five and enforces one millisecond', () => {
  for (const [input, output] of [[1000 / 30, 33], [3.9, 3], [-3.9, 1], [NaN, 1], [Infinity, 1],
    [undefined, 1], [null, 1], ['7.9', 7], [2 ** 31, 1], [2 ** 32 + 7.9, 7], [-(2 ** 32) + 7, 7]]) {
    assert.equal(chromium87TimerDelay(input), output);
  }
  assert.equal(chromium87TimerDelay(0, 3), 1);
  assert.equal(chromium87TimerDelay(0, 4), 4);
  assert.equal(chromium87TimerDelay(10, 6), 10);
  assert.throws(() => chromium87TimerDelay(1n), TypeError);
  assert.throws(() => chromium87TimerDelay(Symbol()), TypeError);
});

test('Chromium timer IDs wrap, skip active IDs and report native exhaustion explicitly', () => {
  assert.equal(nextChromiumTimerId(0, () => false), 1);
  assert.equal(nextChromiumTimerId(0x7fffffff, () => false), 1);
  assert.equal(nextChromiumTimerId(0x7fffffff, id => id === 1), 2);
  assert.equal(nextChromiumTimerId(2, id => id !== 1, 3), 1);
  assert.throws(() => nextChromiumTimerId(2, () => true, 3), /native allocation does not return/);
});

engineTest('HTML integer delay preserves a fractional request time and callback arguments', () => {
  const r = createRuntime();
  r.advance(0.25);
  const start = r.clock.now;
  r.evaluate(`var timerResult=null; setTimeout(function(a,b){'use strict';timerResult={now:performance.now(),date:Date.now(),a,b,windowThis:this===window};},1000/30,'one',2);`);
  r.advance(32.75); assert.equal(r.context.timerResult, null);
  r.advance(0.25);
  assert.deepEqual(JSON.parse(JSON.stringify(r.context.timerResult)), { now: start + 33, date: Math.floor(start + 33), a: 'one', b: 2, windowThis: true });
  assert.equal(r.environment.timerSemantics, 'chromium-87-long-min1-preincrement5-zero-host-latency-v1');
});

engineTest('The unmodified native main loop uses the converted thirty-three-millisecond timer', () => {
  const r = createRuntime(), initialFrame = r.Game.T;
  r.advance(32); assert.equal(r.Game.T, initialFrame);
  r.advance(1); assert.equal(r.Game.T, initialFrame + 1);
  r.advance(32); assert.equal(r.Game.T, initialFrame + 1);
  r.advance(1); assert.equal(r.Game.T, initialFrame + 2);
});

engineTest('Pinned nested timeouts and intervals first fire at 1,2,3,4,8 milliseconds', () => {
  const r = createRuntime(), start = r.clock.now;
  r.evaluate(`var nestingTimes=[]; function nestedFixture(){nestingTimes.push(performance.now());if(nestingTimes.length<8)setTimeout(nestedFixture,0);} setTimeout(nestedFixture,0);
    var intervalTimes=[];var zeroInterval=setInterval(function(){intervalTimes.push(performance.now());if(intervalTimes.length===8)clearTimeout(zeroInterval);},0);`);
  r.advance(0);
  assert.deepEqual(Array.from(r.context.nestingTimes), []);
  assert.deepEqual(Array.from(r.context.intervalTimes), []);
  r.advance(20);
  const expected = [1, 2, 3, 4, 8, 12, 16, 20].map(offset => start + offset);
  assert.deepEqual(Array.from(r.context.nestingTimes), expected);
  assert.deepEqual(Array.from(r.context.intervalTimes), expected);
  r.advance(10); assert.equal(r.context.intervalTimes.length, 8);
});

engineTest('Equal-deadline timers follow scheduling order across interval firings', () => {
  const r = createRuntime();
  r.evaluate(`var order=[];var repeated=setInterval(function(){order.push('interval');if(order.length===3)clearInterval(repeated);},10);
    setTimeout(function(){order.push('timeout');},20);`);
  r.advance(20);
  assert.deepEqual(Array.from(r.context.order), ['interval', 'timeout', 'interval']);
});

engineTest('A repeating native timer schedules its next task before executing the current callback', () => {
  const r = createRuntime();
  r.evaluate(`var order=[];var repeated=setInterval(function(){order.push('interval');if(order.length===1)setTimeout(function(){order.push('child');},10);else clearInterval(repeated);},10);`);
  r.advance(20);
  assert.deepEqual(Array.from(r.context.order), ['interval', 'interval', 'child']);
});

engineTest('Image loading is a host task and does not inherit HTML timer nesting', () => {
  const r = createRuntime(), start = r.clock.now;
  r.evaluate(`var hostTime=null;var hostSteps=0;function hostFixture(){if(++hostSteps<6)setTimeout(hostFixture,0);else {var image=new Image();image.onload=function(){setTimeout(function(){hostTime=performance.now();},0);};image.src='fixture.png';}}setTimeout(hostFixture,0);`);
  r.advance(12); assert.equal(r.context.hostTime, null);
  r.advance(1); assert.equal(r.context.hostTime, start + 13);
});

engineTest('Equal-time native GFD callbacks retain multiplicity because both casts change the game', () => {
  const r = createRuntime({ diagnosticMode: true, recordAudit: false });
  // Diagnostic entry premises, not a route from a new save. Both explicit
  // seeded choices select Hand of Fate; no timer callback is called directly.
  r.evaluate("Game.Objects['Wizard tower'].amount=700;Game.Objects['Wizard tower'].highest=700;Game.Objects['Wizard tower'].level=1;Game.LoadMinigames();");
  r.advance(1000);
  const M = r.Game.Objects['Wizard tower'].minigame;
  r.Game.seed = 'aaacg'; M.magic = M.magicM; M.spellsCastTotal = 0;
  const due = r.clock.now + 1000;
  for (let i = 0; i < 2; i++) r.act({ type: 'cast-spell', spell: "gambler's fever dream" }, { observe: false });
  assert.equal(Array.from(r.timers.values()).filter(timer => timer.due === due).length, 2);
  assert.equal(M.magic, 96); assert.equal(M.spellsCastTotal, 2);
  assert.equal(r.Game.shimmers.length, 0);
  r.advance(1000);
  assert.equal(r.Game.shimmers.length, 2);
  assert(r.Game.shimmers.every(shimmer => shimmer.type === 'golden' && !shimmer.spawnLead));
  assert.equal(M.spellsCastTotal, 2); // Passthrough casts do not increment it.
});

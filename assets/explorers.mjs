import {
  GODZAMOK_BONUS, achievementValue, bankThreshold, checkerboard, exchangeIndex, godzamokBuff,
  goldenInterval, luckyPayout, marginalValueMultiplier, optimalRunMultiplier, orderTimes,
  stageIncomes, wrinklerFactor,
} from './cookie-math.mjs';

const SVG_NS = 'http://www.w3.org/2000/svg';

function element(tag, attributes = {}, text) {
  const node = document.createElement(tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  if (text !== undefined) node.textContent = text;
  return node;
}
function svgElement(tag, attributes = {}) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  return node;
}
function number(value, digits = 1) {
  if (!Number.isFinite(value)) return '∞';
  return value.toLocaleString('en-US', { maximumFractionDigits: digits, minimumFractionDigits: 0 });
}
function duration(seconds) {
  if (!Number.isFinite(seconds)) return 'never';
  if (seconds < 600) return `${number(seconds, 1)} s`;
  if (seconds < 7200) return `${number(seconds / 60, 1)} min`;
  return `${number(seconds / 3600, 2)} h`;
}
function output() {
  return element('div', { class: 'demo-output', 'aria-live': 'polite' });
}
function lines(node, texts) {
  node.replaceChildren(...texts.map((text) => element('p', {}, text)));
}
function numberField(controls, label, value, attributes = {}) {
  const wrap = element('label', {}, `${label} `);
  const input = element('input', { type: 'number', value, inputmode: 'decimal', ...attributes });
  wrap.append(input);
  controls.append(wrap);
  return input;
}
function rangeField(controls, label, attributes) {
  const wrap = element('label', {}, `${label} `);
  const input = element('input', { type: 'range', ...attributes });
  wrap.append(input);
  controls.append(wrap);
  return input;
}
function checkField(controls, label, checked = false) {
  const wrap = element('label', { class: 'demo-check' });
  const input = element('input', { type: 'checkbox' });
  input.checked = checked;
  wrap.append(input, document.createTextNode(label));
  controls.append(wrap);
  return input;
}
function value(input) {
  const parsed = Number(input.value);
  return Number.isFinite(parsed) ? parsed : 0;
}
function mount(id, build) {
  const host = document.getElementById(id);
  if (host) build(host);
}

mount('order-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const income = numberField(controls, 'Income per second', 100, { min: 1, step: 'any' });
  const priceA = numberField(controls, 'Price of A', 1000, { min: 1, step: 'any' });
  const gainA = numberField(controls, 'Gain of A', 10, { min: 0.001, step: 'any' });
  const priceB = numberField(controls, 'Price of B', 5000, { min: 1, step: 'any' });
  const gainB = numberField(controls, 'Gain of B', 80, { min: 0.001, step: 'any' });
  const out = output();
  const update = () => {
    const c = Math.max(value(income), 1e-9);
    const a = { price: Math.max(value(priceA), 0), gain: Math.max(value(gainA), 1e-9) };
    const b = { price: Math.max(value(priceB), 0), gain: Math.max(value(gainB), 1e-9) };
    const eA = exchangeIndex(a.price, a.gain, c);
    const eB = exchangeIndex(b.price, b.gain, c);
    const times = orderTimes(a, b, c);
    const first = eA <= eB ? 'A' : 'B';
    lines(out, [
      `Index of A: ${number(eA)} s. Index of B: ${number(eB)} s. Buy ${first} first.`,
      `A then B: both items after ${duration(times.ab)}. B then A: after ${duration(times.ba)}.`,
    ]);
  };
  controls.addEventListener('input', update);
  host.append(controls, out);
  update();
});

mount('interval-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const luckyDay = checkField(controls, 'Lucky day', true);
  const serendipity = checkField(controls, 'Serendipity', true);
  const goose = checkField(controls, 'Golden goose egg');
  const out = output();
  const update = () => {
    const timing = goldenInterval({ luckyDay: luckyDay.checked, serendipity: serendipity.checked, goldenGooseEgg: goose.checked });
    lines(out, [
      `Window: ${duration(timing.min)} to ${duration(timing.max)}. The mean arrives ${number(timing.share * 100, 1)}% into the window.`,
      `Mean interval: ${duration(timing.mean)}. A banked cookie pays itself back through "Lucky!" in ${number(bankThreshold(timing.mean), 0)} s.`,
    ]);
  };
  controls.addEventListener('change', update);
  host.append(controls, out);
  update();
});

mount('lucky-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const bank = rangeField(controls, 'Bank, in seconds of CpS', { min: 0, max: 12000, step: 100, value: 3000 });
  const out = output();
  const update = () => {
    const seconds = value(bank);
    const payout = luckyPayout(seconds, 1) - 13;
    lines(out, [
      `Bank: ${number(seconds, 0)} s of CpS. "Lucky!" pays ${number(payout, 0)} s of CpS (${number((100 * payout) / Math.max(seconds, 1), 1)}% of the bank).`,
      seconds < 6000 ? 'Below the cap, every banked cookie adds to the payout.' : 'At the cap: more cookies in the bank do not increase the payout.',
    ]);
  };
  bank.addEventListener('input', update);
  host.append(controls, out);
  update();
});

mount('ascend-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const beta = rangeField(controls, 'Growth exponent β', { min: 1.2, max: 8, step: 0.1, value: 2 });
  const out = output();
  const update = () => {
    const b = value(beta);
    const v = optimalRunMultiplier(b);
    const naive = marginalValueMultiplier(b);
    lines(out, [
      `β = ${number(b, 1)}, γ = ${number(3 / b - 1, 3)}. Ascend when all-time cookies have grown by ${number(v, 2)} times.`,
      `Prestige then grows by ${number(Math.cbrt(v), 2)} times per run. The marginal value theorem gives ${number(naive, 2)} times instead.`,
    ]);
  };
  beta.addEventListener('input', update);
  host.append(controls, out);
  update();
});

mount('worth-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const kittens = numberField(controls, 'Kitten upgrades', 8, { min: 0, max: 15, step: 1 });
  const milk = numberField(controls, 'Milk (%)', 952, { min: 0, step: 4 });
  const multiplier = numberField(controls, 'Milk multiplier', 1.1, { min: 0, step: 0.05 });
  const hours = numberField(controls, 'Hours played', 77, { min: 0, step: 1 });
  const out = output();
  const update = () => {
    const x = achievementValue(Math.round(Math.min(Math.max(value(kittens), 0), 15)), value(milk) / 100, value(multiplier));
    const h = Math.max(value(hours), 1);
    lines(out, [
      `One achievement adds ${number(100 * x, 2)}% to production. Over ${number(h, 0)} more hours it is worth ${number(x * h, 2)} h.`,
      2 * x * h > 4
        ? `Neverclick and Hardcore together are worth ${number(2 * x * h, 2)} h, more than the 4-hour Born again run.`
        : `Neverclick and Hardcore together are worth ${number(2 * x * h, 2)} h, less than the 4-hour Born again run.`,
    ]);
  };
  controls.addEventListener('input', update);
  host.append(controls, out);
  update();
});

mount('godzamok-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const slot = element('select', { 'aria-label': 'Godzamok slot' });
  ['First slot', 'Second slot', 'Third slot'].forEach((label, index) => slot.append(element('option', { value: index }, label)));
  const slotLabel = element('label', {}, 'Slot ');
  slotLabel.append(slot);
  controls.append(slotLabel);
  const units = rangeField(controls, 'Buildings per frame', { min: 100, max: 3000, step: 100, value: 2200 });
  const out = output();
  const figure = element('div', { class: 'demo-diagram' });
  const update = () => {
    const bonus = GODZAMOK_BONUS[Number(slot.value)];
    const buff = godzamokBuff(bonus, value(units));
    const peak = buff.series[buff.series.length - 1];
    lines(out, [
      `${number(value(units), 0)} buildings per frame: the buff reaches ×${number(peak, 0)} after 10 seconds and averages ×${number(buff.average, 0)}.`,
      `With clicks worth 3 times CpS before the buff, clicking brings about ${number(3 * buff.average, 0)} times CpS.`,
    ]);
    const width = 600;
    const height = 180;
    const svg = svgElement('svg', { viewBox: `0 0 ${width} ${height}`, class: 'demo-svg', role: 'img', 'aria-label': 'Buff multiplier over two buffs' });
    const top = 3000 * 0.01 * 300;
    const points = [];
    for (let repeat = 0; repeat < 2; repeat++) {
      buff.series.forEach((m, k) => {
        const x = 40 + ((repeat * 300 + k) / 600) * (width - 60);
        points.push(`${x.toFixed(1)},${(height - 24 - (m / top) * (height - 40)).toFixed(1)}`);
      });
    }
    svg.append(
      svgElement('path', { class: 'plot-axis', d: `M40 ${height - 24}H${width - 20}M40 ${height - 24}V12` }),
      svgElement('polyline', { class: 'plot-line', points: points.join(' ') }),
    );
    const label = svgElement('text', { x: 44, y: 22, class: 'plot-label' });
    label.textContent = 'click multiplier';
    const axis = svgElement('text', { x: width - 20, y: height - 6, class: 'plot-label', 'text-anchor': 'end' });
    axis.textContent = '20 seconds';
    svg.append(label, axis);
    figure.replaceChildren(svg);
  };
  controls.addEventListener('input', update);
  host.append(controls, out, figure);
  update();
});

mount('wrinkler-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const count = rangeField(controls, 'Wrinklers', { min: 0, max: 12, step: 1, value: 10 });
  const sacrilegious = checkField(controls, 'Sacrilegious corruption');
  const spawn = checkField(controls, 'Wrinklerspawn');
  const ratio = rangeField(controls, 'Click income ÷ CpS (log scale)', { min: -1, max: 5, step: 0.25, value: 0.5 });
  const out = output();
  const update = () => {
    const n = value(count);
    const w = wrinklerFactor(n, { sacrilegious: sacrilegious.checked, wrinklerspawn: spawn.checked });
    const k = 10 ** value(ratio);
    const stages = stageIncomes(k);
    lines(out, [
      `${n} wrinklers turn CpS into ${number(w, 2)} times as much income.`,
      `Click income ${number(k, k < 10 ? 2 : 0)} times CpS: calm earns ${number(stages.calm, 1)}, wrath earns ${number(stages.wrath, 1)} (per unit of CpS). ${stages.calm > stages.wrath ? 'Choose calm.' : 'Choose wrath.'}`,
    ]);
  };
  controls.addEventListener('input', update);
  host.append(controls, out);
  update();
});

mount('garden-demo', (host) => {
  const controls = element('div', { class: 'demo-controls' });
  const level = element('select', { 'aria-label': 'Farm level' });
  for (let i = 1; i <= 9; i++) level.append(element('option', { value: i }, `Farm level ${i}`));
  const levelLabel = element('label', {}, 'Plot ');
  levelLabel.append(level);
  controls.append(levelLabel);
  const out = output();
  const figure = element('div', { class: 'demo-diagram' });
  const update = () => {
    const layout = checkerboard(Number(level.value));
    const cell = 46;
    const svg = svgElement('svg', {
      viewBox: `0 0 ${layout.width * cell + 4} ${layout.height * cell + 4}`, class: 'demo-svg garden-svg', role: 'img',
      'aria-label': `Breeding layout on a ${layout.width} by ${layout.height} plot`,
    });
    layout.rows.forEach((row, y) => row.forEach((tile, x) => {
      const group = svgElement('g', { transform: `translate(${2 + x * cell} ${2 + y * cell})` });
      group.append(svgElement('rect', { width: cell - 4, height: cell - 4, x: 2, y: 2, class: tile ? 'garden-parent' : 'garden-empty' }));
      if (tile) {
        const text = svgElement('text', { x: cell / 2, y: cell / 2 + 6, 'text-anchor': 'middle', class: 'garden-label' });
        text.textContent = tile;
        group.append(text);
      }
      svg.append(group);
    }));
    figure.replaceChildren(svg);
    lines(out, [
      `${layout.width} × ${layout.height} plot: ${layout.parents} parent tiles and ${layout.empty} empty tiles for mutations.`,
      layout.touchesBoth ? 'Every empty tile touches both parent kinds.' : 'Some empty tiles do not touch both parent kinds.',
    ]);
  };
  level.addEventListener('change', update);
  host.append(controls, out, figure);
  update();
});

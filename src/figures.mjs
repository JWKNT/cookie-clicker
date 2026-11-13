// Figures and tables for the margin of the guide. Each figure is an inline SVG about as wide as
// the margin column, and it takes its colours from the theme through the classes of
// assets/guide.css. The build calculates each number with assets/cookie-math.mjs.
import {
  GODZAMOK_BONUS, LOANS, THREE_ITEMS, achievementValue, checkerboard, chipOrderTime,
  completionTimeSaved, fastestSchedule, fractionValue, godzamokBuff, indexRuleOrder,
  optimalRunMultiplier, scheduleTime, wrinklerFactor,
} from '../assets/cookie-math.mjs';

const round = (value) => Math.round(value * 100) / 100;
const line = (a, b, cls) => `<line x1="${round(a[0])}" y1="${round(a[1])}" x2="${round(b[0])}" y2="${round(b[1])}" class="${cls}"/>`;
const node = (p, cls = 'fig-node', radius = 3.6) => `<circle cx="${round(p[0])}" cy="${round(p[1])}" r="${radius}" class="${cls}"/>`;
const label = (p, text, cls = 'fig-text', anchor = 'middle') => `<text x="${round(p[0])}" y="${round(p[1])}" text-anchor="${anchor}" class="${cls}">${text}</text>`;
const path = (points, cls) => `<polyline points="${points.map(([x, y]) => `${round(x)},${round(y)}`).join(' ')}" class="${cls}"/>`;
const svg = (width, height, title, body) => `<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${title}">${body}</svg>`;
const number = (value, digits = 0) => value.toLocaleString('en-US', { minimumFractionDigits: digits, maximumFractionDigits: digits });
const table = (head, rows) => `<table class="values"><thead><tr>${head.map((cell) => `<th scope="col">${cell}</th>`).join('')}</tr></thead><tbody>${rows.map((row) => `<tr>${row.map((cell) => `<td>${cell}</td>`).join('')}</tr>`).join('')}</tbody></table>`;

const timeOf = (order) => scheduleTime(order.map((at) => THREE_ITEMS[at]));

// The order of Rule 1 and the fastest order for the three items, on one time axis.
function orders() {
  const scale = 43, left = 14, axis = 132;
  const x = (seconds) => left + scale * seconds;
  const rows = [
    { order: indexRuleOrder(THREE_ITEMS), y: 44, cls: 'fig-accent fig-thick', text: 'fig-text', title: 'Rule 1' },
    { order: fastestSchedule(THREE_ITEMS).order, y: 100, cls: 'fig-warm', text: 'fig-text fig-text-warm', title: 'Fastest' },
  ];
  const parts = [];
  for (const { order, y, cls, text, title } of rows) {
    const end = fractionValue(timeOf(order));
    parts.push(line([x(0), y], [x(end), y], cls));
    parts.push(label([x(0), y - 22], `${title}: ${order.map((at) => THREE_ITEMS[at].name).join(', ')}`, text, 'start'));
    order.forEach((at, k) => {
      const when = fractionValue(timeOf(order.slice(0, k + 1)));
      parts.push(node([x(when), y]));
      // The last two purchases of the fastest order are 0.27 seconds apart.
      const shift = k === order.length - 1 && end - fractionValue(timeOf(order.slice(0, k))) < 0.5 ? 7 : 0;
      parts.push(label([x(when) + shift, y - 9], THREE_ITEMS[at].name, text));
    });
    parts.push(label([x(end) + 8, y + 17], `${number(end, 2)} s`, 'fig-text fig-text-note', 'end'));
  }
  parts.push(line([x(0), axis], [x(6.6), axis], 'fig-edge'));
  for (let second = 0; second <= 6; second++) {
    parts.push(line([x(second), axis], [x(second), axis + 4], 'fig-edge'));
    parts.push(label([x(second), axis + 18], `${second}`, 'fig-text fig-text-note'));
  }
  return svg(336, 156, `Two time lines from 0 to 6.5 seconds. Rule 1 buys A at 3 seconds, B at 5.5 seconds and C at 6.5 seconds. The fastest order buys B at 5 seconds, C at 6.2 seconds and A at 6.47 seconds.`, parts.join(''));
}

// The Lucky payout against the bank, both in seconds of income.
function lucky() {
  const x = (bank) => 44 + (bank / 9000) * 272;
  const y = (payout) => 132 - (payout / 900) * 96;
  const parts = [
    line([x(0), y(0)], [x(9300), y(0)], 'fig-edge'),
    line([x(0), y(0)], [x(0), y(1010)], 'fig-edge'),
    line([x(6000), y(0)], [x(6000), y(900)], 'fig-frame'),
    line([x(0), y(900)], [x(6000), y(900)], 'fig-frame'),
    line([x(0), y(0)], [x(6000), y(900)], 'fig-accent fig-thick'),
    line([x(6000), y(900)], [x(9300), y(900)], 'fig-warm'),
    node([x(6000), y(900)]),
  ];
  for (const bank of [3000, 6000, 9000]) parts.push(label([x(bank), y(0) + 17], number(bank), 'fig-text fig-text-note'));
  for (const payout of [450, 900]) parts.push(label([x(0) - 6, y(payout) + 4], `${payout}`, 'fig-text fig-text-note', 'end'));
  parts.push(label([x(3700), y(250)], '15% of the bank', 'fig-text', 'start'));
  parts.push(label([x(7650), y(900) - 9], 'cap', 'fig-text fig-text-warm'));
  return svg(336, 158, 'The Lucky payout against the bank, each in seconds of production. The payout is 15% of the bank up to a bank of 6,000 seconds. From there it stays at 900 seconds.', parts.join(''));
}

// The Godzamok buff during one buff of 10 seconds, with 2,200 buildings in each frame.
const GODZAMOK_UNITS = 2200;
function godzamok() {
  const { series, average } = godzamokBuff(GODZAMOK_BONUS[0], GODZAMOK_UNITS);
  const top = series.at(-1);
  const x = (frame) => 52 + (frame / 300) * 262;
  const y = (factor) => 130 - (factor / top) * 100;
  const parts = [
    line([x(0), y(0)], [x(308), y(0)], 'fig-edge'),
    line([x(0), y(0)], [x(0), y(top * 1.08)], 'fig-edge'),
    line([x(0), y(average)], [x(300), y(average)], 'fig-frame'),
    path([[x(0), y(1)], ...series.map((factor, k) => [x(k + 1), y(factor)])], 'fig-accent fig-thick'),
    node([x(300), y(top)]),
    label([x(0) - 6, y(top) + 4], `×${number(top)}`, 'fig-text fig-text-note', 'end'),
    label([x(0) - 6, y(average) + 4], `×${number(average)}`, 'fig-text fig-text-note', 'end'),
    label([x(96), y(average) - 7], 'mean', 'fig-text fig-text-note'),
  ];
  for (const seconds of [0, 5, 10]) parts.push(label([x(seconds * 30), y(0) + 17], `${seconds} s`, 'fig-text fig-text-note'));
  return svg(336, 156, `The buff to click power during 10 seconds. It increases in a straight line from 1 to ${number(top)}. Its mean is ${number(average)}.`, parts.join(''));
}

// The breeding layout on the full plot of 6 by 6 tiles.
function garden() {
  const { rows } = checkerboard(9);
  const size = 30, left = 78, top = 6;
  const parts = [];
  rows.forEach((row, r) => row.forEach((tile, c) => {
    const x = left + c * size, y = top + r * size;
    parts.push(`<rect x="${x}" y="${y}" width="${size}" height="${size}" class="${tile === 'A' ? 'fig-bar' : tile === 'B' ? 'fig-tile-b' : 'fig-piece'}"/>`);
    if (tile) parts.push(label([x + size / 2, y + size / 2 + 5], tile, tile === 'A' ? 'fig-text' : 'fig-text fig-text-warm'));
  }));
  return svg(336, 192, 'A garden plot of 6 by 6 tiles. Parent A and parent B are on every second tile, like the dark squares of a chessboard: A in the columns 1, 3 and 5, B in the columns 2, 4 and 6. The other 18 tiles are empty, and each of them touches an A tile and a B tile.', parts.join(''));
}

export const figures = { orders, lucky, godzamok, garden };

// ---------- tables ----------
export const CHIP_EXAMPLE = [
  { name: 'X', price: 10, factor: 1.05 },
  { name: 'Y', price: 100, factor: 3 },
];
function chipTable() {
  const [x, y] = CHIP_EXAMPLE;
  const row = (first, second) => [`${first.name}, then ${second.name}`, `${first.price} + ${second.price}/${first.factor}`, number(chipOrderTime([first, second]), 1)];
  return table(['Order', 'Wait', ''], [row(y, x), row(x, y)]);
}

export const BETAS = [1.5, 2, 2.5, 3, 4, 6];
function vstarTable() {
  return table(['β', 'Cookies', 'Prestige'], BETAS.map((beta) => {
    const v = optimalRunMultiplier(beta);
    return [`${beta}`, `×${number(v, 2)}`, `×${number(Math.cbrt(v), 2)}`];
  }));
}

// The game of the example: eight kitten upgrades, 952% milk, a milk multiplier of 1.1, a goal 77 hours away.
export const MILK_EXAMPLE = { kittens: 8, milk: 9.52, multiplier: 1.1, hours: 77 };
function achievementTable() {
  const { kittens, milk, multiplier, hours } = MILK_EXAMPLE;
  return table(['Achievements', 'Production', 'Pause'], [1, 2, 5, 10].map((count) => {
    const gain = achievementValue(kittens, milk, multiplier, count);
    return [`${count}`, `×${number(1 + gain, 4)}`, `${number(completionTimeSaved(gain, hours), 2)} h`];
  }));
}

function wrinklerTable() {
  return table(['Wrinklers', 'Factor'], [0, 4, 8, 10, 12].map((count) => [`${count}`, `×${number(wrinklerFactor(count), 2)}`]));
}

function loanTable() {
  return table(['Loan', 'Boost', 'Then', 'Down'], LOANS.map((loan, at) => [
    `${at + 1}`, `×${loan.boost} for ${loan.boostTime}`, `×${loan.penalty} for ${loan.penaltyTime}`, `${loan.down}%`,
  ]));
}

export const tables = {
  chips: chipTable,
  vstar: vstarTable,
  achievements: achievementTable,
  wrinklers: wrinklerTable,
  loans: loanTable,
};

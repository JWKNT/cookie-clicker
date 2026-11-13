import vm from 'node:vm';
import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { loadGameSource } from './game-source.mjs';
import { maintenanceSchedule, maintenanceRequestTime } from './maintenance-schedule.mjs';

function immutable(value) {
  if (value && typeof value === 'object') { for (const child of Object.values(value)) immutable(child); Object.freeze(value); }
  return value;
}

const MINIGAMES = {
  Farm: 'minigameGarden.js', Bank: 'minigameMarket.js',
  Temple: 'minigamePantheon.js', 'Wizard tower': 'minigameGrimoire.js',
};

/** Chromium 87 timer delay after Web IDL `long` conversion. */
export function chromium87TimerDelay(value, nestingLevel = 0) {
  // Unary + uses ToNumber (and rejects BigInt/Symbol), then |0 implements
  // Web IDL's signed 32-bit wrapping conversion, including NaN and infinity.
  const delay = Math.max(1, (+value) | 0);
  // Chromium 87 increments nesting before its >=5 test, then applies a
  // historical 1ms minimum. These rules differ from the current HTML spec.
  return nestingLevel >= 4 ? Math.max(4, delay) : delay;
}

/** Positive signed-32-bit IDs, wrapping and skipping active IDs as in Blink. */
export function nextChromiumTimerId(current, occupied, maximum = 0x7fffffff) {
  if (!Number.isInteger(maximum) || maximum < 1 || maximum > 0x7fffffff || !Number.isInteger(current) || current < 0 || current > maximum) throw new Error('Invalid timer identifier range');
  for (let searched = 0; searched < maximum; searched++) {
    current = current === maximum ? 1 : current + 1;
    if (!occupied(current)) return current;
  }
  // Native NextID does not terminate when every ID is occupied. Report the
  // diagnostic limit explicitly instead of hanging the audit process.
  throw new Error('Timer identifier space exhausted; native allocation does not return');
}

function makeBrowser(source, clock, timers, evaluate, storage = new Map()) {
  const elements = new Map();
  const noop = () => {};
  let layout = { width: 1200, height: 900, scale: 1 };
  const setViewport = (width, height) => {
    const scale = Math.min(width / Math.max(800, width), height / Math.max(200, height));
    layout = { width: Math.floor(width / scale), height: Math.floor(height / scale), scale };
  };
  // Reviewed desktop subset of Steam 2.053 style.css: sectionLeft 30%;
  // sectionMiddle right318/margin-right15/padding-left16; centerArea left16,
  // top112 and a17px vertical scrollbar; rowCanvas width100%, height128.
  // This supplies client geometry, not a general CSS or text-layout engine.
  const box = element => {
    const width = layout.width; const height = layout.height;
    const middle = Math.max(116, width - width * 0.3 - 318 - 15);
    const center = middle - 16;
    const row = Math.max(0, center - 17);
    if (['wrapper', 'game'].includes(element.id)) return { width, height };
    if (element.id === 'sectionLeft') return { width: Math.max(100, width * 0.3), height };
    if (element.id === 'sectionMiddle') return { width: middle, height };
    if (element.id === 'sectionRight') return { width: 317, clientWidth: 300, height };
    if (element.id === 'centerArea') return { width: center, clientWidth: row, height: Math.max(0, height - 112) };
    if (element.id === 'rows') return { width: row, height: element._offsetHeight };
    if (/^rowCanvas\d+$/.test(element.id) || element.classList.contains('rowCanvas')) return { width: row, height: 128 };
    if (/^row(?:Special)?\d+$/.test(element.id)) return { width: row, height: element._offsetHeight };
    return null;
  };
  const observers = new Set();
  const notifyMutation = (target, type) => {
    for (const observer of observers) {
      let current = target;
      while (current && current !== observer.target && observer.options.subtree) current = current.parentNode;
      if (current !== observer.target || !observer.options[type]) continue;
      observer.records.push({ type, target });
      if (!observer.pending) observer.pending = timers.add(() => {
        observer.pending = null; const records = observer.takeRecords();
        if (records.length && observers.has(observer)) observer.callback(records, observer);
      }, 0);
    }
  };
  class MutationObserver {
    constructor(callback) { this.callback = callback; this.records = []; this.pending = null; }
    observe(target, options) { this.target = target; this.options = options; observers.add(this); }
    disconnect() { observers.delete(this); this.records = []; if (this.pending) timers.remove(this.pending); this.pending = null; }
    takeRecords() { const records = this.records; this.records = []; return records; }
  }
  const matches = (element, selector) => {
    const tokens = selector.trim().split(/\s+(?![^[]*\])/);
    const own = tokens.pop();
    if (!own || element.nodeType !== 1) return false;
    const tag = own.match(/^[\w*-]+/)?.[0];
    if (tag && tag !== '*' && element.tagName !== tag.toUpperCase()) return false;
    for (const match of own.matchAll(/([.#])([\w-]+)|\[([\w-]+)(?:=["']?([^\]"']*)["']?)?\]/g)) {
      if (match[1] === '#' && element.id !== match[2]) return false;
      if (match[1] === '.' && !element.classList.contains(match[2])) return false;
      if (match[3] && (element.getAttribute(match[3]) === null || match[4] !== undefined && element.getAttribute(match[3]) !== match[4])) return false;
    }
    if (tokens.length) { let parent = element.parentNode; while (parent) { if (matches(parent, tokens.join(' '))) return true; parent = parent.parentNode; } return false; }
    return true;
  };
  class Element {
    constructor(tag = 'div') {
      this.nodeType = 1; this.tagName = tag.toUpperCase(); this.nodeName = this.tagName; this.type = tag.toLowerCase() === 'input' ? 'text' : ''; this.style = { removeProperty(name) { delete this[name]; }, setProperty(name, value) { this[name] = value; } }; this.attributes = {}; this.dataset = {};
      this.childNodes = []; this.listeners = {};
      this.parentNode = null; this.offsetWidth = this.clientWidth = this.width = 1200;
      this.offsetHeight = this.clientHeight = this.height = 900;
      this.scrollHeight = 900; this.scrollTop = 0; this.offsetTop = this.offsetLeft = 0;
      this.value = ''; if (this.tagName === 'TEXTAREA') { this.defaultValue = ''; this.readOnly = false; } this.className = ''; this._html = ''; this._textContent = '';
      this.classList = {
        add: (...names) => { this.className += ` ${names.join(' ')}`; },
        remove: (...names) => { this.className = this.className.split(/\s+/).filter(x => !names.includes(x)).join(' '); },
        contains: name => this.className.split(/\s+/).includes(name),
        toggle: name => { if (this.classList.contains(name)) this.classList.remove(name); else this.classList.add(name); },
      };
    }
    get clientWidth() { const geometry = box(this); return geometry ? Math.round(geometry.clientWidth ?? geometry.width) : this._clientWidth; }
    set clientWidth(value) { this._clientWidth = value; }
    get offsetWidth() { const geometry = box(this); return geometry ? Math.round(geometry.width) : this._offsetWidth; }
    set offsetWidth(value) { this._offsetWidth = value; }
    get clientHeight() { const geometry = box(this); return geometry ? Math.round(geometry.height) : this._clientHeight; }
    set clientHeight(value) { this._clientHeight = value; }
    get offsetHeight() { const geometry = box(this); return geometry ? Math.round(geometry.height) : this._offsetHeight; }
    set offsetHeight(value) { this._offsetHeight = value; }
    get children() { return this.childNodes.filter(child => child.nodeType === 1); }
    set textContent(text) { this._textContent = String(text); this.childNodes = this._textContent ? [{ nodeType: 3, nodeValue: this._textContent, textContent: this._textContent, parentNode: this }] : []; notifyMutation(this, 'childList'); }
    get textContent() { return this.childNodes.map(child => child.textContent ?? child.nodeValue ?? '').join(''); }
    set id(id) { this._id = id; if (!elements.has(id)) elements.set(id, this); }
    get id() { return this._id || ''; }
    set innerHTML(html) {
      const removeIds = node => {
        for (const child of node.children) removeIds(child);
        if (node.id && elements.get(node.id) === node) elements.delete(node.id);
      };
      for (const child of this.children) removeIds(child);
      this._html = String(html); this.childNodes = [];
      // Comments have no active descendants or event handlers.
      const markup = this._html.replace(/<!--[\s\S]*?-->/g, match => ' '.repeat(match.length));
      const stack = [this];
      const decode = value => value.replace(/&#39;/g, "'").replace(/&#34;|&quot;/g, '"').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
      let lastEnd = 0;
      for (const match of markup.matchAll(/<(\/?)([\w-]+)\b(?:[^>"']|"[^"]*"|'[^']*')*>/g)) {
        // Native textarea contents are RCDATA, not active child markup.
        const tag = match[2].toLowerCase();
        if (stack.at(-1).tagName === 'TEXTAREA' && !(match[1] && tag === 'textarea')) continue;
        if (match.index > lastEnd) stack.at(-1).childNodes.push({ nodeType: 3, nodeValue: decode(markup.slice(lastEnd, match.index)), textContent: decode(markup.slice(lastEnd, match.index)), parentNode: stack.at(-1) });
        lastEnd = match.index + match[0].length;
        if (match[1]) {
          for (let i = stack.length - 1; i > 0; i--) if (stack[i].tagName.toLowerCase() === tag) {
            const closed = stack[i]; closed._html = this._html.slice(closed._contentStart, match.index);
            if (tag === 'textarea') {
              const value = decode(closed._html.replace(/\r\n?/g, '\n')).replace(/^\n/, '');
              closed.childNodes = value ? [{ nodeType: 3, nodeValue: value, textContent: value, parentNode: closed }] : [];
              closed.defaultValue = value; closed.value = value;
            }
            stack.length = i; break;
          }
          continue;
        }
        const child = new Element(tag); child.parentNode = stack.at(-1); child._contentStart = match.index + match[0].length;
        for (const attr of match[0].matchAll(/([\w-]+)\s*=\s*(?:"([^"]*)"|'([^']*)')/g)) {
          const value = decode(attr[2] ?? attr[3]);
          if (attr[1].toLowerCase().startsWith('on')) { child.attributes[attr[1].toLowerCase()] = value; child[attr[1].toLowerCase()] = function (event) { return evaluate(`(function(event){${value}\n})`).call(this, event); }; }
          else child.setAttribute(attr[1], value);
        }
        // The pinned ExportSave textarea uses a bare boolean readonly attribute.
        const unquotedAttributes = match[0].replace(/"[^"]*"|'[^']*'/g, '');
        if (/(?:\s)readonly(?:\s|=|\/?>)/i.test(unquotedAttributes) && child.getAttribute('readonly') === null) child.setAttribute('readonly', '');
        child.parentNode.childNodes.push(child);
        if (!['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'].includes(tag) && !match[0].endsWith('/>')) stack.push(child);
      }
      if (lastEnd < markup.length) stack.at(-1).childNodes.push({ nodeType: 3, nodeValue: decode(markup.slice(lastEnd)), textContent: decode(markup.slice(lastEnd)), parentNode: stack.at(-1) });
      notifyMutation(this, 'childList');
    }
    get innerHTML() { return this._html; }
    get firstChild() { return this.childNodes[0] || null; }
    get lastChild() { return this.childNodes.at(-1) || null; }
    get firstElementChild() { return this.children[0] || null; }
    get lastElementChild() { return this.children.at(-1) || null; }
    get parentElement() { return this.parentNode; }
    setAttribute(name, value) { this.attributes[name] = String(value); if (name === 'readonly') this.readOnly = true; else if (name === 'id') this.id = value; else if (name === 'class') this.className = value; else if (name === 'style') { for (const part of String(value).split(';')) { const split = part.indexOf(':'); if (split > 0) this.style[part.slice(0, split).trim().replace(/-([a-z])/g, (_, c) => c.toUpperCase())] = part.slice(split + 1).trim(); } } else if (name.startsWith('data-')) this.dataset[name.slice(5).replace(/-([a-z])/g, (_, c) => c.toUpperCase())] = String(value); else this[name] = value; }
    removeAttribute(name) { delete this.attributes[name]; if (name === 'readonly') this.readOnly = false; else if (name === 'id') elements.delete(this.id); else delete this[name]; }
    getAttribute(name) { return this.attributes[name] ?? this[name] ?? null; }
    appendChild(child) {
      if (child.nodeType === 11) { for (const node of [...child.childNodes]) this.appendChild(node); return child; }
      if (child.parentNode) child.parentNode.removeChild(child);
      this.childNodes.push(child); child.parentNode = this; notifyMutation(this, 'childList');
      if (child.tagName === 'SCRIPT' && child.src) {
        const filename = child.src.split('?')[0];
        if (!Object.hasOwn(source.sources, filename)) throw new Error(`Blocked script request: ${filename}`);
        evaluate(source.sources[filename], filename); child.onload?.();
      }
      return child;
    }
    append(...nodes) { for (const node of nodes) this.appendChild(typeof node === 'string' ? { nodeType: 3, textContent: node, nodeValue: node, parentNode: null } : node); }
    prepend(...nodes) { for (const node of nodes.reverse()) this.insertBefore(typeof node === 'string' ? { nodeType: 3, textContent: node, nodeValue: node, parentNode: null } : node, this.firstChild); }
    removeChild(child) { this.childNodes = this.childNodes.filter(x => x !== child); child.parentNode = null; notifyMutation(this, 'childList'); return child; }
    insertBefore(child, reference) { if (!reference) return this.appendChild(child); if (child.nodeType === 11) { for (const node of [...child.childNodes]) this.insertBefore(node, reference); return child; } if (child.parentNode) child.parentNode.removeChild(child); const index = this.childNodes.indexOf(reference); if (index < 0) throw new Error('insertBefore reference is not a child'); this.childNodes.splice(index, 0, child); child.parentNode = this; notifyMutation(this, 'childList'); return child; }
    insertAdjacentHTML(position, html) { this.innerHTML += html; }
    addEventListener(type, callback) { (this.listeners[type] ||= []).push(callback); }
    removeEventListener(type, callback) { this.listeners[type] = (this.listeners[type] || []).filter(f => f !== callback); }
    dispatchEvent(event) {
      event.target ||= this; event.currentTarget = this;
      event.preventDefault ||= () => { event.defaultPrevented = true; };
      event.stopPropagation ||= () => { event.cancelBubble = true; };
      this[`on${event.type}`]?.call(this, event);
      for (const f of [...(this.listeners[event.type] || [])]) f.call(this, event);
      if (event.bubbles && !event.cancelBubble && this.parentNode?.dispatchEvent) this.parentNode.dispatchEvent(event);
      return !event.defaultPrevented;
    }
    click() { return this.dispatchEvent({ type: 'click', target: this }); }
    focus() {} blur() {} select() {} remove() { this.parentNode?.removeChild(this); }
    getBoundingClientRect() { const geometry = box(this); const width = geometry ? geometry.width * layout.scale : this.width; const height = geometry ? geometry.height * layout.scale : this.height; return { x: 0, y: 0, top: 0, left: 0, right: width, bottom: height, width, height }; }
    getElementsByTagName(tag) { return this.children.flatMap(x => [...(tag === '*' || x.tagName === tag.toUpperCase() ? [x] : []), ...x.getElementsByTagName(tag)]); }
    getElementsByClassName(name) { return this.getElementsByTagName('*').filter(x => name.split(/\s+/).every(n => x.classList.contains(n))); }
    querySelectorAll(selector) { return this.getElementsByTagName('*').filter(x => selector.split(',').some(part => matches(x, part))); }
    querySelector(selector) { return this.querySelectorAll(selector)[0] ?? null; }
    toDataURL() { return 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVQIHWP4z8DwHwAFgAI/ScLbtAAAAABJRU5ErkJggg=='; }
    getContext() {
      return new Proxy({ canvas: this, measureText: text => ({ width: String(text).length * 8 }), createPattern: () => ({}),
        createLinearGradient: () => ({ addColorStop: noop }), createRadialGradient: () => ({ addColorStop: noop }),
        getImageData: () => ({ data: new Uint8ClampedArray(4) }),
      }, { get: (obj, key) => key in obj ? obj[key] : noop });
    }
  }
  const document = new Element('document');
  document.head = new Element('head'); document.body = new Element('body');
  document.documentElement = new Element('html');
  document.body.innerHTML = source.sources['index.html'];
  document.getElementById = id => {
    id = String(id);
    const cached = elements.get(id);
    let ancestor = cached; while (ancestor && ancestor !== document) ancestor = ancestor.parentNode;
    if (ancestor === document) return cached;
    // Native store rebuilds move an index ID between independently replaced containers.
    const found = document.getElementsByTagName('*').find(element => element.id === id) || null;
    if (found) elements.set(id, found); else elements.delete(id);
    return found;
  };
  document.createElement = tag => new Element(tag);
  document.createElementNS = (namespace, tag) => new Element(tag);
  document.createTextNode = text => ({ nodeType: 3, nodeValue: String(text), textContent: String(text), parentNode: null });
  document.createDocumentFragment = () => { const fragment = new Element('fragment'); fragment.nodeType = 11; return fragment; };
  document.createEvent = () => ({ initEvent(type) { this.type = type; } });
  document.getElementsByTagName = tag => tag === 'head' ? [document.head] : tag === 'body' ? [document.body] : Element.prototype.getElementsByTagName.call(document, tag);
  document.cookie = ''; document.title = ''; document.visibilityState = 'visible'; document.hasFocus = () => true;
  document.documentElement.appendChild(document.head); document.documentElement.appendChild(document.body); document.appendChild(document.documentElement);
  document.querySelector = selector => selector === 'head' ? document.head : selector === 'body' ? document.body : Element.prototype.querySelector.call(document, selector);
  class KeyboardEvent { constructor(type, options = {}) { this.type = type; Object.assign(this, options); this.preventDefault = noop; this.stopPropagation = noop; } }
  const localStorage = { getItem: key => storage.get(key) ?? null, setItem: (key, value) => storage.set(key, String(value)), removeItem: key => storage.delete(key), clear: () => storage.clear() };
  class Image extends Element {
    constructor() { super('img'); this.complete = true; this.naturalWidth = this.width = 64; this.naturalHeight = this.height = 64; }
    set src(value) { this._src = value; timers.add(() => this.onload?.({ target: this }), 0); }
    get src() { return this._src; }
  }
  class Audio { constructor() { this.volume = 0; this.currentTime = 0; } play() { return Promise.resolve(); } pause() {} load() {} addEventListener() {} }
  const windowListeners = {};
  const location = { href: 'https://localhost/cookieclicker/', hostname: 'localhost', host: 'localhost', pathname: '/cookieclicker/', protocol: 'https:', reload: noop };
  return { setViewport, KeyboardEvent, MutationObserver, Element, HTMLElement: Element, HTMLCanvasElement: Element, CanvasRenderingContext2D: function () {}, document, localStorage, Image, Audio, location,
    navigator: { userAgent: 'CookieClickerModel', language: 'en-US', appVersion: '5.0', plugins: [] }, screen: { width: 1200, height: 900 },
    innerWidth: 1200, innerHeight: 900, devicePixelRatio: 1,
    addEventListener: (type, callback) => { (windowListeners[type] ||= []).push(callback); },
    removeEventListener: (type, callback) => { windowListeners[type] = (windowListeners[type] || []).filter(f => f !== callback); },
    dispatchEvent: event => { for (const fn of [...(windowListeners[event.type] || [])]) fn(event); },
    getComputedStyle: el => new Proxy(el.style, { get: (obj, key) => obj[key] || '0px' }),
    setTimeout: (fn, delay = 0, ...args) => timers.html(fn, delay, false, args), clearTimeout: (id = 0) => timers.clearHtml((+id) | 0),
    setInterval: (fn, delay = 0, ...args) => timers.html(fn, delay, true, args), clearInterval: (id = 0) => timers.clearHtml((+id) | 0),
    requestAnimationFrame: fn => timers.add(fn, 1000 / 30), cancelAnimationFrame: id => timers.remove(id),
    performance: { now: () => clock.now }, alert: noop, confirm: () => false, prompt: () => null, open: noop,
  };
}

/** Unmodified JavaScript engine in a deterministic, isolated browser adapter. Not a Lean translation. */
export function createRuntime({ sourceDirectory, randomTape, randomSeed = 1, epochMs = Date.UTC(2026, 9, 29, 12), heralds = 100, initialize = true, diagnosticMode = false, onTransition, transitionAchievementGate, recordAudit = true, maintenanceReload = null } = {}) {
  if (typeof recordAudit !== 'boolean') throw new Error('recordAudit must be Boolean');
  if (!recordAudit && randomTape !== undefined) throw new Error('Summary-only recording requires the LCG sample stream, not an explicit random tape');
  const source = loadGameSource(sourceDirectory);
  const reloadSchedule = maintenanceSchedule(maintenanceReload);
  if (reloadSchedule && !initialize) throw new Error('Maintenance reloads require native initialized gameplay');
  const clock = { now: epochMs };
  let tapeIndex = 0; let seed = randomSeed >>> 0; let randomDrawCount = 0; let actionCount = 0;
  const consumedRandom = recordAudit ? [] : null;
  const random = () => {
    let value;
    if (randomTape) {
      if (tapeIndex >= randomTape.length) throw new Error(`Random tape exhausted at draw ${tapeIndex}`);
      value = randomTape[tapeIndex++];
    } else { seed = (Math.imul(1664525, seed) + 1013904223) >>> 0; value = seed / 2 ** 32; }
    if (!(value >= 0 && value < 1)) throw new Error('Random tape values must be in [0, 1)');
    randomDrawCount++; if (recordAudit) consumedRandom.push(value); return value;
  };
  const queue = new Map(); let lastHtmlTimer = 0; let nextHostTask = -1; let nextTimerOrder = 0;
  let runningTimerNesting = null;
  const timers = {
    // Image load, mutation delivery and animation-frame callbacks are host
    // tasks, not calls to the HTML timer initialization algorithm.
    add(fn, delay) { const id = nextHostTask--; queue.set(id, { fn, args: [], due: clock.now + Math.max(0, Number(delay) || 0), order: nextTimerOrder++, nesting: null, repeat: false }); return id; },
    html(fn, requestedDelay, repeat, args, previousId) {
      const timeout = (+requestedDelay) | 0;
      const parentNesting = runningTimerNesting ?? 0;
      const delay = chromium87TimerDelay(timeout, parentNesting);
      const id = previousId ?? (lastHtmlTimer = nextChromiumTimerId(lastHtmlTimer, id => queue.has(id)));
      queue.set(id, { fn, args, timeout, repeat, due: clock.now + delay, order: nextTimerOrder++, nesting: Math.min(0x7fffffff, parentNesting + 1) });
      return id;
    },
    remove(id) { queue.delete(id); },
    clearHtml(id) { if (id > 0) queue.delete(id); },
  };
  class ClockDate extends Date {
    constructor(...args) { super(...(args.length > 1 ? [Date.UTC(...args)] : args.length ? args : [clock.now])); }
    static now() { return Math.floor(clock.now); }
    getFullYear() { return this.getUTCFullYear(); } getMonth() { return this.getUTCMonth(); }
    getDate() { return this.getUTCDate(); } getDay() { return this.getUTCDay(); }
    getHours() { return this.getUTCHours(); } getMinutes() { return this.getUTCMinutes(); }
    getSeconds() { return this.getUTCSeconds(); } getTimezoneOffset() { return 0; }
    setFullYear(...args) { return this.setUTCFullYear(...args); } setMonth(...args) { return this.setUTCMonth(...args); }
    setDate(...args) { return this.setUTCDate(...args); } setHours(...args) { return this.setUTCHours(...args); }
  }
  let context; let Game; let setViewport; let engine;
  let reloadRequested = false; let reloadCount = 0; let maintenanceIndex = 0;
  let maintenancePending = false; let maintenanceIssued = false; let maintenanceSaveWritten = false; let saveLoadPending = false;
  const browserStorage = new Map();
  const evaluate = (code, filename = 'adapter') => vm.runInContext(code, context, { filename, timeout: 10000 });
  // Reuse the same source script; callbacks still run in the current realm,
  // with the original timeout, arguments, and native task order.
  const timerDispatch = new vm.Script('if (typeof __timerCallback === "function") __timerCallback.apply(window, __timerArguments); else throw new Error("String timer rejected");', { filename: 'adapter' });
  const runTimer = (id, timer) => {
    queue.delete(id);
    const previousNesting = runningTimerNesting;
    runningTimerNesting = timer.nesting;
    // TimerBase::RunInternal schedules a repeating timer before invoking its
    // action. DOMTimer::Fired adjusts the next interval at nesting level5;
    // callbacks created by that action still inherit the old nesting level.
    if (timer.repeat) timers.html(timer.fn, timer.timeout, true, timer.args, id);
    context.__timerCallback = timer.fn; context.__timerArguments = timer.args;
    try {
      timerDispatch.runInContext(context, { timeout: 10000 });
    } finally { runningTimerNesting = previousNesting; }
    if (reloadRequested) {
      reloadRequested = false; reloadCount++;
      // A navigation discards the old realm, its DOM and every old callback.
      // Only the just-written native save and browser storage survive.
      queue.clear(); lastHtmlTimer = 0; nextHostTask = -1; nextTimerOrder = 0; runningTimerNesting = null;
      app.saveData = isolatedSave;
      initializeRealm();
      installActions(engine, advance);
      installNextMaintenanceRequest();
      engine.notifyTransition('maintenance-reload', { reloadCount });
    }
    if (maintenancePending && !maintenanceIssued && canRequestMaintenance()) requestMaintenanceReload();
  };
  let isolatedSave = '';
  const app = { saveData: '', getMostRecentSave: callback => { callback(isolatedSave); saveLoadPending = false; }, save: value => {
      isolatedSave = value;
      if (maintenanceIssued) maintenanceSaveWritten = true;
      // The native Steam wrapper completes local/cloud writes asynchronously.
      // Zero host latency still completes after this JS task, before a later
      // Logic callback is allowed to request navigation.
      const savingGame = context.Game; savingGame.isSaving = true;
      timers.add(() => { savingGame.isSaving = false; }, 0);
    },
    grabData: callback => callback({ playersN: heralds * 100 }), gotAchiev() {}, registerMod() {}, justLoadedSave() { saveLoadPending = false; }, setFullscreen() {},
    onResize() {}, hardReset() { isolatedSave = ''; }, reload() {
      if (!maintenanceIssued) throw new Error('Unscheduled reload is outside the runtime action contract');
      // ExportSave calls WriteSave1 and can clear toSave without persisting.
      // Preserve that native effect, but do not accept a stale-save navigation
      // as the user-authorized current-save maintenance operation. This is an
      // admissibility failure of the trace, not a native game exception.
      if (!maintenanceSaveWritten) {
        const error = new Error('Inadmissible maintenance trace: native reload has no current save written after its scheduled request');
        error.name = 'AdmissibilityError'; error.code = 'STALE_MAINTENANCE_SAVE'; throw error;
      }
      maintenancePending = false; maintenanceIssued = false; maintenanceSaveWritten = false; reloadRequested = true;
    },
    quit() { throw new Error('Quit is outside the runtime action contract'); }, openLink() {},
  };
  const initializeRealm = () => {
  const browser = makeBrowser(source, clock, timers, evaluate, browserStorage);
  setViewport = browser.setViewport; delete browser.setViewport;
  const math = Object.create(Math); math.random = random;
  const globals = { ...browser, Math: math, Date: ClockDate, URL, VERSION: 2.053, BETA: 0, App: app, Steam: app,
    console: { log() {}, warn() {}, error() {} }, Uint8Array, Uint8ClampedArray,
    btoa: value => Buffer.from(value, 'binary').toString('base64'), atob: value => Buffer.from(value, 'base64').toString('binary'),
    crypto: { getRandomValues: array => { for (let i = 0; i < array.length; i++) array[i] = Math.floor(random() * 256); return array; } },
  };
  context = vm.createContext(globals);
  context.window = context; context.self = context; context.top = context;
  // The parsed DOM is inert. Execute the pinned page's active script elements
  // in their source order, including the hidden top-bar globe's random draw.
  // Steam's IPC/audio wrapper is supplied by the isolated app fixture above.
  const page = source.sources['index.html'].replace(/<!--[\s\S]*?-->/g, match => match.replace(/[^\r\n]/g, ' '));
  for (const match of page.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script\s*>/gi)) {
    const src = match[1].match(/\bsrc\s*=\s*(["'])(.*?)\1/i)?.[2]?.split('?')[0];
    if (src === '../steam/steam.js') continue;
    if (src && !['base64.js', 'main.js'].includes(src)) throw new Error(`Blocked page script request: ${src}`);
    const line = page.slice(0, match.index).split('\n').length;
    evaluate(src ? source.sources[src] : '\n'.repeat(line - 1) + match[2], src || 'index.html');
    if (src === 'main.js') {
      const seededRandom = context.Math.seedrandom;
      context.Math.seedrandom = function (seedValue, entropy) {
        if (arguments.length) return seededRandom.call(context.Math, seedValue, entropy);
        context.Math.random = random; return undefined;
      };
      context.Math.random = random;
    }
  }
  if (initialize) {
    saveLoadPending = true;
    // English is an environment setting, not a player save. Keep the native
    // load handler, locale callbacks, greeting, loader and image onload path.
    context.localStorage.setItem('CookieClickerLang', 'EN');
    evaluate('window.onload();');
    let calls = 0;
    for (;;) {
      const pending = Array.from(queue).find(([, timer]) => timer.due <= clock.now);
      if (!pending) break;
      if (++calls > 100000) throw new Error('Startup timer execution limit reached; no state has been skipped');
      const [id, timer] = pending; runTimer(id, timer);
    }
    if (!context.Game.ready) throw new Error('Native zero-latency startup did not initialize the game');
  }
  Game = context.Game;
  };
  initializeRealm();
  const canRequestMaintenance = () => !saveLoadPending && Game && !Game.OnAscend && !Game.AscendTimer && !Game.ReincarnateTimer && !(Game.promptOn && Game.promptNoClose);
  const requestMaintenanceReload = () => {
    // This macro uses the visible Options → Change language → English path.
    // The pinned callback requests a current save even for the same language.
    // Defer only for lifecycle guards, never for a random outcome.
    maintenanceIssued = true; maintenanceSaveWritten = false;
    if (Game.promptOn) context.document.getElementById('promptClose').click();
    if (Game.onMenu !== 'prefs') context.document.getElementById('prefsButton').click(); else Game.UpdateMenu();
    const option = context.document.getElementById('changeLanguageOption');
    if (!option) throw new Error('Native maintenance language control is unavailable');
    option.click();
    const english = context.document.getElementById('langSelect-EN');
    if (!english) throw new Error('Native English maintenance control is unavailable');
    english.click();
    engine.notifyTransition('maintenance-request', { requestIndex: maintenanceIndex - 1 });
  };
  const installNextMaintenanceRequest = () => {
    const next = maintenanceRequestTime(reloadSchedule, maintenanceIndex);
    if (!Number.isFinite(next)) return;
    const due = epochMs + next;
    if (due < clock.now) throw new Error('Maintenance schedule clock lost an unprocessed request');
    timers.add(() => {
      maintenanceIndex++; maintenancePending = true;
      installNextMaintenanceRequest();
      if (!maintenanceIssued && canRequestMaintenance()) requestMaintenanceReload();
    }, due - clock.now);
  };
  if (transitionAchievementGate !== undefined && (!Array.isArray(transitionAchievementGate)
    || transitionAchievementGate.some(name => typeof name !== 'string' || !Game.Achievements[name]))) {
    throw new Error('Transition achievement gate requires known achievement names');
  }
  const unquote = value => value.replace(/\\'/g, "'").replace(/\\\\/g, '\\');
  const cursorCounts = Array.from(Game.Objects.Cursor.buyFunction.toString().matchAll(/this\.amount>=(\d+)\) Game\.Win\('((?:\\.|[^'])*)'\)/g), match => ({ amount: Number(match[1]), name: unquote(match[2]) }));
  const handmadeTargets = Array.from(source.sources['main.js'].matchAll(/Game\.handmadeCookies>=(\d+)\) \{Game\.Win\('((?:\\.|[^'])*)'\)/g), match => ({ threshold: Number(match[1]), name: unquote(match[2]) }));
  if (cursorCounts.length !== 13 || handmadeTargets.length !== 15) throw new Error('Pinned production threshold extraction failed');
  const countTargets = Object.fromEntries(Object.values(Game.Objects).map(b => [b.id, b.id === 0 ? cursorCounts : Object.values(b.tieredAchievs).map(a => ({ name: a.name, amount: Game.Tiers[a.tier].achievUnlock }))]));
  const rawBuildingSums = new Map();
  const quotedSumPrice = (building, amount) => {
    const key = [building.id, building.basePrice, Game.priceIncrease, building.free, building.amount, amount];
    let cached = rawBuildingSums.get(building);
    if (!cached || !key.every((value, i) => Object.is(value, cached.key[i]))) {
      let raw = 0;
      // Same loop, operation order and free-copy floor as native getSumPrice.
      for (let i = Math.max(0, building.amount); i < Math.max(0, building.amount + amount); i++) {
        raw += building.basePrice * Math.pow(Game.priceIncrease, Math.max(0, i - building.free));
      }
      cached = { key, raw }; rawBuildingSums.set(building, cached);
    }
    // Discounts are intentionally not cached: buffs, auras, upgrades, Garden
    // effects and Pantheon slots can change while the raw sum stays the same.
    return Math.ceil(Game.modifyBuildingPrice(building, cached.raw));
  };
  const events = recordAudit ? [] : null;
  const accessedUpgrades = new Set();
  // The native numeric shimmer counter stops increasing at2^53. Its DOM
  // nodes and event handlers remain distinct. These opaque adapter tokens
  // identify only those public controls; they expose no RNG or heap address.
  // Keep ordinary safe numeric IDs for compatibility with existing traces.
  const shimmerNodeTokens = new WeakMap();
  let nextShimmerNodeToken = 0n;
  const shimmerControlId = shimmer => {
    if (Number.isSafeInteger(shimmer.id)) return shimmer.id;
    if (!shimmerNodeTokens.has(shimmer.l)) shimmerNodeTokens.set(shimmer.l, `shimmer-node:${nextShimmerNodeToken++}`);
    return shimmerNodeTokens.get(shimmer.l);
  };
  let historyTable = null, historyById = null, historyCount = null, unseenUpgrades = [];
  let historyCatalogueValid = false;
  const remember = () => {
    // The pinned vanilla constructor is the only writer of catalogue entries:
    // it updates UpgradesN. A fresh realm replaces the table. Ownership and
    // unlock fields remain live; already recorded names need no further read.
    if (historyTable !== Game.Upgrades || historyById !== Game.UpgradesById || historyCount !== Game.UpgradesN) {
      historyTable = Game.Upgrades; historyById = Game.UpgradesById; historyCount = Game.UpgradesN;
      const entries = Object.entries(Game.Upgrades || {});
      historyCatalogueValid = entries.length === historyCount && entries.every(([name, me]) =>
        me.name === name && Number.isSafeInteger(me.id) && historyById?.[me.id] === me);
      unseenUpgrades = entries.map(([, me]) => me).filter(me => !accessedUpgrades.has(me.name));
    }
    if (!historyCatalogueValid) unseenUpgrades = Object.values(Game.Upgrades || {});
    let remaining = 0;
    for (const me of unseenUpgrades) {
      if (me.unlocked || me.bought) accessedUpgrades.add(me.name);
      else unseenUpgrades[remaining++] = me;
    }
    unseenUpgrades.length = remaining;
    // Allocate at every timer/action boundary, even without a snapshot, so
    // observation frequency does not change recorded action identities.
    for (const shimmer of Game.shimmers || []) shimmerControlId(shimmer);
  };
  const snapshot = () => {
    remember();
    const objects = Object.values(Game.Objects);
    const garden = Game.Objects.Farm.minigame;
    const market = Game.Objects.Bank.minigame;
    const gardenObservation = garden ? { ready: !!Game.isMinigameReady(Game.Objects.Farm), level: Game.Objects.Farm.level, farmAmount: Game.Objects.Farm.amount, freeze: !!garden.freeze, frozen: !!garden.freeze, soil: garden.soilsById[garden.soil]?.key ?? garden.soil,
          nextStepMs: Math.max(0, garden.nextStep - clock.now), nextSoilMs: Math.max(0, garden.nextSoil - clock.now), stepSeconds: garden.stepT,
          plot: Array.from(garden.plot, row => Array.from(row, tile => [tile[0] > 0 ? garden.plantsById[tile[0] - 1].key : null, tile[1]])),
          plants: Object.fromEntries(Object.entries(garden.plants).map(([key, p]) => [key, { id: p.id, name: p.name, unlocked: !!p.unlocked, mature: p.mature, immortal: !!p.immortal, plantable: p.plantable !== false, cost: garden.getCost(p), ageTick: p.ageTick, ageTickR: p.ageTickR }])),
          harvestsTotal: garden.harvestsTotal, convertTimes: garden.convertTimes, seedless: !!Game.HasAchiev('Seedless to nay'),
        } : null;

    const marketControlVisible = id => { const element = context.document.getElementById(id); return !!element && element.style.display !== 'none'; };
    const marketObservation = market ? {
      ready: !!Game.isMinigameReady(Game.Objects.Bank), bankLevel: Game.Objects.Bank.level,
      open: !!Game.Objects.Bank.onMinigame, buildingId: Game.Objects.Bank.id,
      officeLevel: market.officeLevel,
      officeUpgradeVisible: marketControlVisible('bankOfficeUpgrade'),
      offices: Array.from(market.offices, (o, id) => ({ id, cursorAmount: o.cost?.[0] ?? null, cursorLevel: o.cost?.[1] ?? null })),
      brokers: market.brokers, maxBrokers: market.getMaxBrokers(), brokerPrice: market.getBrokerPrice(),
      brokerVisible: marketControlVisible('bankBrokersBuy'),
      overheadMultiplier: 1 + 0.01 * (20 * Math.pow(0.95, market.brokers)),
      goods: Array.from(market.goodsById, g => ({ id: g.id, key: g.key, buildingId: g.building.id, buildingLevel: g.building.level, active: g.building.highest > 0, visible: !!g.l && g.l.style.display !== 'none',
        price: market.getGoodPrice(g), restingPrice: market.getRestingVal(g.id), last: g.last, stock: g.stock, maxStock: market.getGoodMaxStock(g),
        buyCookiePrice: Game.cookiesPsRawHighest * market.getGoodPrice(g) * (1 + 0.01 * (20 * Math.pow(0.95, market.brokers))),
        sellCookiePrice: Game.cookiesPsRawHighest * market.getGoodPrice(g), canBuy: g.last !== 2, canSell: g.last !== 1,
      })),
      profit: market.profit, nextTickMs: Math.max(0, (Game.fps * market.secondsPerTick - market.tickT) * 1000 / Game.fps),
      loans: [1,2,3].map(id => ({ id, unlocked: market.officeLevel >= [2,4,5][id-1],
        visible: marketControlVisible(`bankLoan${id}`),
        activeFrames: Game.hasBuff(`Loan ${id}`)?.time ?? 0, interestFrames: Game.hasBuff(`Loan ${id} (interest)`)?.time ?? 0 })),
    } : null;
    const lumpAge = Math.floor(clock.now) - Game.lumpT;
    const nextDragon = Game.dragonLevels[Game.dragonLevel];
    const santaPrice = Math.pow(Game.santaLevel + 1, Game.santaLevel + 1);
    // Read the current rendered DOM, not the private ticker branch or a future
    // generated message. Public seeded text is legitimate evidence for inference.
    const tickerElement = context.document.getElementById('commentsText1');
    let tickerVisible = !!tickerElement && !Game.OnAscend && !Game.AscendTimer
      && !Game.ReincarnateTimer && !Game.promptOn;
    for (let node = tickerElement; node && tickerVisible; node = node.parentNode) {
      if (node.style?.display === 'none' || node.style?.visibility === 'hidden'
          || node.style?.opacity === '0' || node.style?.opacity === 0 || node.classList?.contains('toggledOff')) tickerVisible = false;
    }
    const ticker = { visible: tickerVisible, text: tickerVisible ? tickerElement.textContent : '' };

    return {
      schemaVersion: 1, gameVersion: String(Game.version), edition: 'steam', fps: Game.fps, elapsedMs: clock.now - epochMs, wallTimeMs: Math.floor(clock.now), frame: Game.T,
      viewport: { width: Game.windowW, height: Game.windowH },
      garden: gardenObservation, market: marketObservation,
      lump: { available: !!Game.canLumps() && Game.ascensionMode !== 1, type: lumpAge / Game.lumpOverripeAge * 7 >= 3 ? Game.lumpCurrentType : null,
        ageMs: lumpAge, matureAge: Game.lumpMatureAge, ripeAge: Game.lumpRipeAge, overripeAge: Game.lumpOverripeAge,
        nextRefill: Math.max(0, Game.lumpRefill) * 1000 / Game.fps },
      dragon: { level: Game.dragonLevel, aura: Game.dragonAura, aura2: Game.dragonAura2,
        auras: Object.values(Game.dragonAuras).map(a => ({ id: a.id, name: a.name, unlocked: !!Game.Has('A crumbly egg') && Game.dragonLevel >= a.id + 4 })),
        nextCanUpgrade: !!Game.Has('A crumbly egg') && Game.dragonLevel < Game.dragonLevels.length - 1 && !!nextDragon.cost(),
        nextCostDescription: nextDragon.costStr ? nextDragon.costStr() : null },
      santa: { level: Game.santaLevel, price: santaPrice, canUpgrade: !!Game.Has('A festive hat') && Game.santaLevel < 14 && Game.cookies > santaPrice },
      seasonal: { season: Game.season, remainingMs: Game.seasonT < 0 ? null : Game.seasonT * 1000 / Game.fps, uses: Game.seasonUses,
        reindeerClicked: Game.reindeerClicked, pledges: Game.pledges, pledgeRemainingMs: Game.pledgeT * 1000 / Game.fps, elderWrath: Game.elderWrath,
        researchRemainingMs: Game.researchT < 0 ? null : Game.researchT * 1000 / Game.fps,
        researchName: Game.nextResearch ? Game.UpgradesById[Game.nextResearch]?.name ?? null : null,
        ticker,
        fortuneVisible: tickerVisible && !!tickerElement.querySelector('.fortune') && Game.TickerEffect?.type === 'fortune',
        groups: { santa: Array.from(Game.santaDrops), reindeer: Array.from(Game.reindeerDrops), halloween: Array.from(Game.halloweenDrops), easter: Array.from(Game.easterEggs), valentines: Array.from(Game.heartDrops), fortunes: Array.from(Game.Tiers.fortune.upgrades, u => u.name) },
        helperGrandmas: Array.from(Game.Objects.Grandma.pics || []).filter(pic => pic.pic === 'elfGrandma.png'
          && pic.x + 32 >= 0 && pic.x + 32 < Game.Objects.Grandma.canvas.width
          && pic.y + 32 >= 0 && pic.y + 32 < Game.Objects.Grandma.canvas.height).map(pic => ({ x: pic.x + 32, y: pic.y + 32 })),
        grandmaDisplay: { width: Game.Objects.Grandma.canvas.width, height: Game.Objects.Grandma.canvas.height,
          capacity: Math.floor(Game.Objects.Grandma.canvas.width / ((Game.Objects.Grandma.art.w || 48) / (Game.Objects.Grandma.art.rows || 1)) + 1),
          drawn: Game.Objects.Grandma.pics.length, muted: !!Game.Objects.Grandma.muted },
      },
      ascension: {
        prestigeIfAscend: Math.max(0, Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned))),
        gainedIfAscend: Math.max(0, Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned))) - Game.prestige,
        gainedPrestige: Game.gainedPrestige, permanentSlots: Array.from(Game.permanentUpgrades),
        permanentCandidates: Object.values(Game.Upgrades).filter(u => u.bought && u.unlocked && !u.noPerm && ['', 'cookie'].includes(u.pool) && !Game.permanentUpgrades.includes(u.id)).map(u => ({ id: u.id, name: u.name, price: u.getPrice() })),
        heavenlyUpgrades: Object.values(Game.Upgrades).filter(u => u.pool === 'prestige').map(u => ({ id: u.id, name: u.name, price: u.getPrice(), parents: Array.from(u.parents || []).filter(p => p !== -1).map(p => p.id), bought: !!u.bought, visible: !u.showIf || !!u.showIf() })),
      },
      goldenClicks: Game.goldenClicks, wrinklersPopped: Game.wrinklersPopped, ascensions: Game.resets, resets: Game.resets,
      cookiesPsRawHighest: Game.cookiesPsRawHighest, cookiesPsRaw: Game.cookiesPsRaw,
      handmadeCookies: Game.handmadeCookies, cookiesPerClick: Game.computedMouseCps,
      production: {
        bankAchievements: Array.from(Game.BankAchievements, a => ({ name: a.name, threshold: a.threshold })),
        cpsAchievements: Array.from(Game.CpsAchievements, a => ({ name: a.name, threshold: a.threshold })),
        handmadeAchievements: handmadeTargets.map(a => ({ ...a })),
      },
      shop: {
        buildings: objects.map(b => {
          const countAchievements = countTargets[b.id];
          const goalAmount = Math.max(700, ...countAchievements.map(a => a.amount));
          const purchaseAmount = Math.min(1000, Math.max(0, goalAmount - b.amount));
          // Quote native unit transactions under the currently active price
          // modifiers. Recompute after an aura change or any other modifier.
          const priceAt = amount => Math.ceil(Game.modifyBuildingPrice(b, b.basePrice * Math.pow(Game.priceIncrease, Math.max(0, amount - b.free))));
          const cycleAmount = Game.isMinigameReady(Game.Objects.Temple) ? Math.min(100, Math.max(0, b.amount - 1)) : 0;
          let rebuy = 0; let refund = 0;
          for (let i = 0; i < cycleAmount; i++) {
            rebuy += priceAt(b.amount - cycleAmount + i);
            refund += Math.floor(priceAt(b.amount - i) * b.getSellMultiplier());
          }
          return { id: b.id, name: b.name, amount: b.amount, price: b.getPrice(), buy1price: b.getSumPrice(1), storedCps: b.storedCps, storedTotalCps: b.storedTotalCps, locked: !!b.locked, level: b.level,
            rebuyOnePrice: priceAt(Math.max(0, b.amount - 1)), godzamokCycle: { amount: cycleAmount, rebuy, refund, net: rebuy - refund },
            totalCookies: b.totalCookies, productionCps: b.storedTotalCps * Game.globalCpsMult,
            countAchievements: countAchievements.map(a => ({ ...a })),
            productionAchievements: Array.from(b.productionAchievs, a => ({ name: a.achiev.name, threshold: a.pow })),
            goalAmount, goalPurchase: { amount: purchaseAmount, price: purchaseAmount ? quotedSumPrice(b, purchaseAmount) : 0 },
          };
        }),
        upgrades: Object.values(Game.Upgrades).filter(u => !u.bought && !['debug','unused','dungeon','shadow'].includes(u.pool) && (u.unlocked || (u.pool === 'prestige' && Game.OnAscend && (u.parents || []).every(p => p === -1 || p.bought) && (!u.showIf || u.showIf())))).map(u => ({ id: u.id, name: u.name, pool: u.pool, price: u.getPrice(), canBuy: !!u.canBuy(), unlocked: !!u.unlocked, bought: !!u.bought })),
      },
      cookies: Game.cookies, cookiesEarned: Game.cookiesEarned, cookiesReset: Game.cookiesReset,
      cookiesPs: Game.cookiesPs, prestige: Game.prestige, heavenlyChips: Game.heavenlyChips,
      lumps: Game.lumps, lumpsTotal: Game.lumpsTotal, cookieClicks: Game.cookieClicks,
      // Only the currently rendered native export prompt grants this observation.
      saveExport: Game.promptOn && context.document.getElementById('promptContentExportSave')
        ? context.document.getElementById('textareaPrompt')?.value ?? null : null,
      giftCode: Game.promptOn && context.document.getElementById('promptContentGiftSendReady') ? context.document.getElementById('giftCode')?.value ?? null : null,
      achievements: Object.fromEntries(Object.values(Game.Achievements).map(x => [x.name, !!x.won])),
      upgrades: Object.fromEntries(Object.values(Game.Upgrades).map(x => [x.name, { id: x.id, bought: !!x.bought, unlocked: !!x.unlocked }])),
      history: { gameVersion: '2.053', edition: 'steam', accessedUpgrades: [...accessedUpgrades].sort() },
      progression: {
        achievementsOwned: Game.AchievementsOwned,
        dragonLevel: Game.dragonLevel, santaLevel: Game.santaLevel, ascensionMode: Game.ascensionMode,
        onAscend: !!Game.OnAscend,
        ascendTimer: Game.AscendTimer, reincarnateTimer: Game.ReincarnateTimer,
        buildingLevels: Object.fromEntries(objects.map(x => [x.name, x.level])),
        buildingAmounts: Object.fromEntries(objects.map(x => [x.name, x.amount])),
        buildingHighest: Object.fromEntries(objects.map(x => [x.name, x.highest])),
        minigames: Object.fromEntries(Object.keys(MINIGAMES).map(name => [name, !!Game.isMinigameReady(Game.Objects[name])])),
        gardenSeeds: garden?.plants ? Object.keys(garden.plants).filter(k => garden.plants[k].unlocked) : [],
        gardenSoils: garden?.soils ? Object.keys(garden.soils).filter(k => Game.Objects.Farm.amount >= garden.soils[k].req) : [],
        stockOfficeLevel: market?.officeLevel ?? 0,
        grimoireSpells: Object.keys(Game.Objects['Wizard tower'].minigame?.spells || {}),
        pantheonGods: Object.keys(Game.Objects.Temple.minigame?.gods || {}),
      },
      controls: { mouseDown: !!Game.mouseDown, cookieState: Game.BigCookieState, menu: Game.onMenu, promptOn: !!Game.promptOn, promptOptions: Game.promptOptionsN, promptFocus: Game.promptOptionFocus,
        tooltip: { visible: !!Game.tooltip.on && Game.tooltip.tta.style.display !== 'none' && Game.tooltip.tta.style.opacity !== '0',
          dynamic: !!Game.tooltip.dynamic, pendingHide: !!Game.tooltip.shouldHide,
          text: Game.tooltip.on && Game.tooltip.tta.style.display !== 'none' && Game.tooltip.tta.style.opacity !== '0' ? Game.tooltip.tt.textContent : '',
          crate: Game.onCrate ? { id: Game.onCrate.id || null,
            itemId: Game.onCrate.getAttribute('data-id') === null ? null : Number(Game.onCrate.getAttribute('data-id')),
            type: Game.onCrate.classList.contains('upgrade') ? 'upgrade' : Game.onCrate.classList.contains('achievement') ? 'achievement' : null } : null },
        notes: Array.from(Game.Notes.slice(0, 5), n => ({ id: n.id, title: n.title, description: n.desc })), jukeboxSound: Game.jukebox.onSound,
        keys: Array.from(Game.keys || [], (x, i) => x ? i : null).filter(x => x !== null), buyMode: Game.buyMode, buyBulk: Game.buyBulk,
        preferences: { ...Game.prefs }, volume: Game.volume, volumeMusic: Game.volumeMusic, cloneGenes: Array.from(Game.YouCustomizer.currentGenes),
        garden: gardenObservation,
        grimoire: Game.Objects['Wizard tower'].minigame ? { open: !!Game.Objects['Wizard tower'].onMinigame, spellsCastTotal: Game.Objects['Wizard tower'].minigame.spellsCastTotal, magic: Game.Objects['Wizard tower'].minigame.magic, magicMax: Game.Objects['Wizard tower'].minigame.magicM,
          spells: Object.fromEntries(Object.entries(Game.Objects['Wizard tower'].minigame.spells).map(([key, spell]) => [key, { cost: Game.Objects['Wizard tower'].minigame.getSpellCost(spell) }])) } : null,
        pantheon: Game.Objects.Temple.minigame ? { open: !!Game.Objects.Temple.onMinigame, swaps: Game.Objects.Temple.minigame.swaps, slots: Array.from(Game.Objects.Temple.minigame.slot) } : null,
        market: market ? { profit: market.profit, brokers: market.brokers, goods: Array.from(market.goodsById, g => ({ id: g.id, value: g.val, stock: g.stock, capacity: market.getGoodMaxStock(g), unlocked: g.building.highest > 0 })) } : null,
        wrinklers: Array.from(Game.wrinklers, w => ({ id: w.id, phase: w.phase, type: w.type, selected: !!w.selected, clicks: w.clicks, hp: w.hp, sucked: w.sucked })),
      },
      buffs: Object.fromEntries(Object.values(Game.buffs || {}).map(x => [x.name, { time: x.time, multCpS: x.multCpS, multClick: x.multClick }])),
      shimmers: Array.from(Game.shimmers || [], x => ({ id: shimmerControlId(x), type: x.type, wrath: x.wrath || 0, life: x.life, dur: x.dur, lifeSeconds: x.life / Game.fps })),
    };
  };
  const notifyTransition = (kind, details = {}) => {
    if (onTransition) {
      const gateSatisfied = !transitionAchievementGate || transitionAchievementGate.every(name => !!Game.Achievements[name].won);
      onTransition(immutable({ kind, elapsedMs: Math.floor(clock.now) - Math.floor(epochMs), ...details,
        ...(transitionAchievementGate ? { gateSatisfied } : {}), observation: gateSatisfied ? snapshot() : null }));
    }
  };
  const advance = milliseconds => {
    if (!Number.isFinite(milliseconds) || milliseconds < 0) throw new Error('Elapsed time must be finite and nonnegative');
    const target = clock.now + milliseconds;
    let calls = 0;
    for (;;) {
      let selected = null;
      for (const [id, timer] of queue) if (timer.due <= target && (!selected || timer.due < selected.timer.due || (timer.due === selected.timer.due && timer.order < selected.timer.order))) selected = { id, timer };
      if (!selected) break;
      if (++calls > 1e7) throw new Error('Timer execution limit reached; no state has been skipped');
      const { id, timer } = selected; clock.now = timer.due; runTimer(id, timer);
      remember(); notifyTransition('timer', { timerId: id });
    }
    clock.now = target;
  };
  engine = { source, get context() { return context; }, clock, evaluate, consumedRandom, timers: queue, get Game() { return Game; }, snapshot, advance, events, notifyTransition, remember, shimmerControlId,
    resizeViewport: (width, height) => { context.innerWidth = width; context.innerHeight = height; setViewport(width, height); context.dispatchEvent({ type: 'resize' }); },
    auditCounts: () => ({ recordingMode: recordAudit ? 'full' : 'summary-only', actionCount, randomDrawCount, reloadCount }),
    recordAction: action => { if (recordAudit) events.push(action); return actionCount++; },
    environment: { platform: 'Steam adapter', heralds, epochMs, timezone: 'UTC', randomSeed, randomMode: randomTape ? 'explicit tape' : 'LCG sample stream', verifiedLeanTranslation: false,
      policyMode: diagnosticMode ? 'diagnostic-only' : 'no-retry-no-rng-manipulation',
      saveReloadRetries: false, nativeRngManipulation: diagnosticMode,
      nativeSaveInspection: 'current-export-ui-only-v1',
      ...(reloadSchedule ? { maintenanceReload: reloadSchedule, maintenanceReloadSemantics: 'precommitted-clock-native-save-fresh-realm-v1' } : {}),
      timerSemantics: 'chromium-87-long-min1-preincrement5-zero-host-latency-v1' },
  };
  installActions(engine, advance);
  installNextMaintenanceRequest();
  engine.advance = milliseconds => engine.act({ type: 'wait', milliseconds });
  notifyTransition('initial');
  return engine;
}

/** The accepted actions are a reviewed subset, not an exhaustive full-game control space. */
export const ACTION_TYPES = Object.freeze([
  'wait', 'click', 'cookie-pointer', 'buy-building', 'sell-building', 'buy-upgrade', 'ascend', 'reincarnate',
  'level-building', 'harvest-lump', 'prompt', 'close-prompt', 'click-shimmer', 'click-news',
  'open-menu', 'export-save', 'preference', 'volume', 'key', 'visibility', 'tooltip-pointer', 'dismiss-note', 'jukebox-sound', 'customizer-gene', 'customizer-random',
  'building-mute', 'minigame-open', 'upgrade-vault', 'buy-all-upgrades', 'click-product', 'name-bakery', 'tiny-cookie', 'achievement-slot', 'forgotten-madeleine', 'resize', 'select-cosmetic',
  'gift-send', 'gift-redeem', 'permanent-slot', 'store-bulk', 'building-hover', 'building-press', 'wrinkler-hover', 'wrinkler-poke', 'minigame-refill',
  'upgrade-santa', 'upgrade-dragon', 'dragon-aura', 'pet-dragon',
  'garden-plant', 'garden-harvest', 'garden-harvest-all', 'garden-soil', 'garden-freeze', 'garden-sacrifice',
  'cast-spell', 'pantheon-slot', 'market-buy', 'market-sell', 'market-office', 'market-broker', 'market-loan',
]);

function installActions(runtime, advance) {
  const { Game, context } = runtime;
  const require = (condition, message) => { if (!condition) throw new Error(`Illegal action: ${message}`); };
  const active = () => require(!Game.OnAscend && !Game.AscendTimer && !Game.ReincarnateTimer, 'a normal run must be active');
  const integer = (x, low, high, field) => { require(Number.isInteger(x) && x >= low && x <= high, `${field} must be an integer in [${low}, ${high}]`); return x; };
  const building = id => { const b = Game.ObjectsById[integer(id, 0, Game.ObjectsN - 1, 'building id')]; require(!!b, 'unknown building'); return b; };
  const minigame = name => { active(); require(Game.ascensionMode !== 1, 'minigames are disabled in Born again'); const b = Game.Objects[name]; require(Game.isMinigameReady(b), `${name} minigame is locked`); return b.minigame; };
  const showMenu = name => { if (Game.onMenu !== name) Game.ShowMenu(name); else Game.UpdateMenu(); };
  const uiClick = id => { const element = context.document.getElementById(id); require(!!element, `control ${id} is unavailable`); element.click(); };
  // Source-controlled internal market visibility. This does not substitute for
  // the still-open general layout/hit-testing contract or outer-panel opening.
  const marketControl = id => { const element = context.document.getElementById(id);
    require(!!element && element.style.display !== 'none', `market control ${id} is hidden or unavailable`);
    return element;
  };
  const tile = (M, a) => { integer(a.x, 0, 5, 'x'); integer(a.y, 0, 5, 'y'); require(M.isTileUnlocked(a.x, a.y), 'garden tile is locked'); };
  const ancestors = element => { const chain = []; for (let node = element; node; node = node.parentNode) chain.push(node); return chain; };
  let tooltipPointerElement = null;
  const exitTooltipPointer = next => {
    if (tooltipPointerElement && tooltipPointerElement !== next) {
      const old = tooltipPointerElement;
      tooltipPointerElement = null;
      if (ancestors(old).includes(context.document)) old.dispatchEvent({ type: 'mouseout', target: old,
        relatedTarget: next, bubbles: true, button: 0, detail: 0 });
    }
  };
  const tooltipTarget = target => {
    require(target && typeof target === 'object', 'a native tooltip target is required');
    if (target.kind === 'control') {
      require(typeof target.id === 'string' && /^[A-Za-z][A-Za-z0-9_-]{0,99}$/.test(target.id), 'invalid native tooltip control id');
      // Building-canvas hover has a separate coordinate-sensitive contract.
      // In particular, a generic tooltip action must not bypass the You leak ban.
      require(!/^rowCanvas(?:Add)?\d+$/.test(target.id), 'building canvases require the guarded building-hover action');
      const element = context.document.getElementById(target.id);
      require(!!element, 'native tooltip control is absent'); return element;
    }
    require(target.kind === 'stats-crate' && ['upgrade','achievement'].includes(target.item), 'unknown native tooltip target');
    require(Game.onMenu === 'stats' && !Game.OnAscend, 'statistics crates require the visible statistics menu');
    integer(target.id, 0, target.item === 'upgrade' ? Game.UpgradesN - 1 : Game.AchievementsN - 1, 'crate item id');
    const element = context.document.getElementById('menu')?.querySelector(`.crate.${target.item}[data-id="${target.id}"]`);
    require(!!element, 'statistics crate is absent'); return element;
  };
  const dispatch = a => {
    switch (a.type) {
      case 'wait': advance(a.milliseconds); break;
      case 'click': active(); Game.ClickCookie(); break;
      case 'cookie-pointer': {
        active();
        const events = { enter: 'mouseover', leave: 'mouseout', down: 'mousedown', up: 'mouseup', click: 'click' };
        require(Object.hasOwn(events, a.phase), 'unknown cookie pointer phase');
        require(!Game.promptOn || a.phase === 'leave' || a.phase === 'up', 'the prompt covers the big cookie');
        const cookie = context.document.getElementById('bigCookie');
        require(cookie && !Game.touchEvents, 'desktop big-cookie pointer input is unavailable');
        if (a.phase === 'enter') {
          exitTooltipPointer(cookie);
          // Moving to the visible cookie is an ordinary input. Its native
          // sound and particle draws are incidental, not outcome selection.
          context.document.dispatchEvent({ type: 'mousemove', target: cookie,
            pageX: Game.cookieOriginX * Game.scale, pageY: Game.cookieOriginY * Game.scale + context.TopBarOffset });
        }
        cookie.dispatchEvent({ type: events[a.phase], target: cookie, bubbles: true, button: 0, detail: 1 });
        break;
      }
      case 'buy-building': {
        active(); const b = building(a.id); const n = integer(a.amount ?? 1, 1, 1000, 'amount');
        // The first two locked mystery rows remain clickable. Native
        // ClickProduct does not test locked; CSS hides only toggledOff rows.
        require(!b.l.classList.contains('toggledOff') && Game.cookies >= b.getSumPrice(n), 'building row is hidden or unaffordable');
        const mode = Game.buyMode; Game.buyMode = 1; try { b.buy(n); } finally { Game.buyMode = mode; } break;
      }
      case 'sell-building': { active(); const b = building(a.id); const n = integer(a.amount ?? 1, 1, b.amount, 'amount'); b.sell(n); break; }
      case 'buy-upgrade': {
        const u = Game.UpgradesById[integer(a.id, 0, Game.UpgradesN - 1, 'upgrade id')];
        require(u && !['debug', 'unused', 'dungeon', 'shadow'].includes(u.pool), 'excluded upgrade');
        require(!u.bought, 'upgrade already owned');
        if (u.pool === 'prestige') {
          require(Game.OnAscend && !Game.AscendTimer, 'heavenly purchases require the ascension screen');
          require((u.parents || []).every(p => p === -1 || p.bought) && (!u.showIf || u.showIf()) && Game.heavenlyChips >= u.getPrice(), 'heavenly upgrade is unavailable');
        } else { active(); require(u.unlocked && u.canBuy(), 'upgrade is locked or unaffordable'); }
        u.buy(); break;
      }
      case 'ascend': active(); Game.Ascend(1); break;
      case 'reincarnate': require(Game.OnAscend && !Game.AscendTimer && !Game.ReincarnateTimer, 'not ready to reincarnate'); Game.nextAscensionMode = integer(a.mode ?? 0, 0, 1, 'mode'); Game.Reincarnate(1); break;
      case 'level-building': { active(); const b = building(a.id); require(Game.canLumps() && b.amount > 0 && Game.lumps >= b.level + 1, 'building level is unavailable'); b.levelUp(); break; }
      case 'harvest-lump': active(); require(Game.canLumps(), 'sugar lumps are locked'); Game.clickLump(); break;
      case 'prompt': { require(Game.promptOn, 'no active prompt'); integer(a.option ?? 0, 0, Game.promptOptionsN - 1, 'option'); uiClick(`promptOption${a.option ?? 0}`); break; }
      case 'close-prompt': require(Game.promptOn && !Game.promptNoClose, 'prompt cannot close'); uiClick('promptClose'); break;
      case 'click-shimmer': {
        active();
        const matches = Game.shimmers.filter(x => runtime.shimmerControlId(x) === a.id);
        require(matches.length > 0, 'shimmer is absent');
        require(matches.length === 1, 'shimmer numeric ID is ambiguous');
        matches[0].l.click(); break;
      }
      case 'click-news': active(); uiClick('commentsText1'); break;
      case 'dismiss-note': {
        const note = a.all ? Game.noteL.querySelector('.sidenote') : Game.noteL.querySelector(`#note-${integer(a.id, 0, Number.MAX_SAFE_INTEGER, 'note id')} .close`);
        require(!!note, 'visible notification close control is absent'); note.click(); break;
      }
      case 'jukebox-sound': {
        active(); require(Game.Upgrades.Jukebox.unlocked, 'jukebox is locked');
        // The native sound callback is independent of the external Steam Music service.
        Game.jukebox.setSound(integer(a.id, 0, Game.jukebox.sounds.length - 1, 'sound id')); break;
      }
      case 'open-menu': {
        require(['', 'prefs', 'stats', 'log'].includes(a.menu), 'unknown menu'); Game.ShowMenu(a.menu); break;
      }
      case 'export-save': {
        require(!Game.promptOn, 'the prompt covers the Options export control');
        // The pinned .ascending rule removes sectionMiddle from layout. The
        // intro fade alone is opacity, so it does not add an artificial lock.
        require(!context.document.getElementById('game').classList.contains('ascending'), 'Options is hidden during ascension');
        if (Game.onMenu !== 'prefs') uiClick('prefsButton');
        const control = context.document.getElementById('menu')?.getElementsByTagName('a')
          .find(element => element.getAttribute('onclick')?.includes('Game.ExportSave();'));
        require(Game.onMenu === 'prefs' && !!control, 'the native Export save control is unavailable');
        control.click();
        require(Game.promptOn && !!context.document.getElementById('promptContentExportSave')
          && !!context.document.getElementById('textareaPrompt'), 'the native Export save prompt did not open');
        break;
      }
      case 'preference': {
        const allowed = ['bgMusic','fullscreen','fancy','filters','particles','numbers','milk','cursors','wobbly','cookiesound','crates','monospace','format','notifs','extraButtons','askLumps','notScary','timeout'];
        require(allowed.includes(a.name), 'preference is unavailable or requires an excluded reload');
        showMenu('prefs'); uiClick(`${a.name}Button`); break;
      }
      case 'volume': {
        require(['sound', 'music'].includes(a.channel), 'unknown volume channel'); integer(a.value, 0, 100, 'volume');
        showMenu('prefs'); const input = context.document.getElementById(a.channel === 'sound' ? 'volumeSlider' : 'volumeMusicSlider');
        input.value = a.value; input.dispatchEvent({ type: 'input' }); break;
      }
      case 'key': {
        const code = integer(a.code, 0, 255, 'key code'); require(typeof a.down === 'boolean', 'key down must be Boolean');
        const ctrl = !!Game.keys[17] || (code === 17 && a.down);
        require(!(ctrl && [79,82].includes(code)) && code !== 116, 'import and reload keyboard shortcuts are excluded');
        context.dispatchEvent({ type: a.down ? 'keydown' : 'keyup', keyCode: code,
          ctrlKey: ctrl, shiftKey: !!Game.keys[16] || (code === 16 && a.down), preventDefault() {}, stopPropagation() {} }); break;
      }
      case 'visibility': {
        require(typeof a.visible === 'boolean', 'visibility must be Boolean');
        context.document.visibilityState = a.visible ? 'visible' : 'hidden';
        context.document.dispatchEvent({ type: 'visibilitychange' }); context.dispatchEvent({ type: 'visibilitychange' }); break;
      }
      case 'tooltip-pointer': {
        require(['enter','leave'].includes(a.phase), 'unknown tooltip pointer phase');
        require(!Game.touchEvents, 'desktop tooltip pointer input is unavailable');
        const element = tooltipTarget(a.target);
        const eventType = a.phase === 'enter' ? 'mouseover' : 'mouseout';
        const callbacks = [element[`on${eventType}`], ...(element.listeners[eventType] || [])].filter(f => typeof f === 'function');
        const inline = element.attributes[`on${eventType}`];
        require(callbacks.some(f => /Game\.tooltip\./.test(String(f))) || typeof inline === 'string' && /Game\.tooltip\./.test(inline),
          'control has no native tooltip pointer handler');
        const chain = ancestors(element);
        require(chain.includes(context.document), 'tooltip control is detached');
        require(!chain.some(node => /^prompt(?:Import|Export)|^(?:textareaPrompt|textareaPromptCache|debug|debugLog)$/.test(node.id)), 'save and debug surfaces are excluded');
        if (a.phase === 'enter') {
          require(!chain.some(node => node.style?.display === 'none' || node.style?.visibility === 'hidden'
            || node.style?.opacity === '0' || node.style?.opacity === 0 || node.classList?.contains('toggledOff')), 'tooltip control is hidden');
          require(!chain.some(node => node.id === 'lumps' || node.classList?.contains('lumpsOnly'))
            || context.document.getElementById('game').classList.contains('lumpsOn'), 'sugar-lump tooltip control is hidden');
          require(!chain.some(node => node.id === 'topBar'), 'the Steam target hides the web top bar');
          require(!chain.some(node => node.id === 'menu') || !!Game.onMenu, 'menu tooltip control is hidden');
          require(!chain.some(node => ['rows','buildingsMaster','centerArea'].includes(node.id)) || !Game.onMenu || chain.some(node => node.id === 'menu'), 'the menu covers the building panel');
          require(!Game.promptOn || chain.some(node => ['prompt','tooltip','tooltipAnchor'].includes(node.id)), 'the prompt covers this tooltip control');
          require(!chain.some(node => node.id === 'ascend') || Game.OnAscend && !Game.AscendTimer, 'ascension tooltip control is hidden');
          require(!Game.OnAscend || chain.some(node => ['ascend','prompt','tooltip','tooltipAnchor'].includes(node.id)), 'the ascension screen covers this tooltip control');
          exitTooltipPointer(element);
          // Geometry remains the adapter's reviewed subset; native element and
          // document handlers receive the same ordinary pointer event sequence.
          const bounds = element.getBoundingClientRect();
          context.document.dispatchEvent({ type: 'mousemove', target: element,
            pageX: (bounds.left + bounds.right) / 2, pageY: (bounds.top + bounds.bottom) / 2 });
          tooltipPointerElement = element;
        } else {
          require(tooltipPointerElement === element || element.id === 'tooltip' && Game.tooltip.on,
            'pointer has not entered this tooltip control');
          if (tooltipPointerElement === element) tooltipPointerElement = null;
        }
        element.dispatchEvent({ type: eventType, target: element, bubbles: true, button: 0, detail: 0 });
        break;
      }
      case 'customizer-gene': case 'customizer-random': {
        active(); require(Game.Objects.You.amount > 0, 'clone customizer is unavailable');
        if (a.type === 'customizer-gene') { require(Object.hasOwn(Game.YouCustomizer.genesById, a.gene), 'unknown clone gene'); require(a.direction === -1 || a.direction === 1, 'gene direction must be -1 or 1'); }
        Game.YouCustomizer.prompt();
        if (a.type === 'customizer-gene') uiClick(`customizerSelect-${a.direction < 0 ? 'L' : 'R'}-${a.gene}`);
        else { const control = context.document.getElementById('promptContentCustomizeYou').getElementsByTagName('a').find(x => x.getAttribute('onclick')?.includes('YouCustomizer.randomize')); require(!!control, 'randomizer control unavailable'); control.click(); }
        break;
      }
      case 'building-mute': {
        active(); const b = building(a.id); require(b.id > 0 && b.amount > 0 && Game.prefs.extraButtons, 'building mute control is unavailable'); require(typeof a.muted === 'boolean', 'muted must be Boolean');
        if (!!b.muted !== a.muted) uiClick(a.muted ? `productMute${b.id}` : `mutedProduct${b.id}`); break;
      }
      case 'minigame-open': { const b = building(a.id); minigame(b.name); uiClick(`productMinigameButton${b.id}`); break; }
      case 'upgrade-vault': {
        active(); const u = Game.UpgradesById[integer(a.id, 0, Game.UpgradesN - 1, 'upgrade id')];
        require(Game.Has('Inspired checklist') && u.unlocked && !u.bought && !['toggle','tech','prestige','debug','unused','shadow','dungeon'].includes(u.pool), 'upgrade cannot be vaulted'); u.click({ shiftKey: true }); break;
      }
      case 'buy-all-upgrades': active(); require(Game.Has('Inspired checklist'), 'buy-all upgrades is locked'); Game.storeBuyAll(); break;
      case 'click-product': { active(); const b = building(a.id); require(!b.l.classList.contains('toggledOff'), 'building row is hidden'); Game.ClickProduct(b.id); break; }
      case 'name-bakery': {
        active(); require(typeof a.name === 'string' && a.name.length > 0 && a.name.length <= 28 && !/saysopensesame|restore backup/i.test(a.name), 'invalid or debug bakery name');
        Game.bakeryNamePrompt(); context.document.getElementById('bakeryNameInput').value = a.name; uiClick('promptOption0'); break;
      }
      case 'tiny-cookie': active(); Game.ShowMenu('stats'); Game.ClickTinyCookie(); break;
      case 'achievement-slot': {
        active(); const achievement = Game.AchievementsById[integer(a.id, 0, Game.AchievementsN - 1, 'achievement id')];
        require(typeof achievement?.clickFunction === 'function', 'achievement slot has no click action');
        Game.ShowMenu('stats'); achievement.clickFunction(); break;
      }
      case 'forgotten-madeleine': {
        active(); Game.ShowMenu('log');
        const target = context.document.getElementById('oldenDays')?.getElementsByTagName('div').find(x => x.onclick);
        require(!!target, 'forgotten madeleine is absent'); target.click(); break;
      }
      case 'resize': {
        // Resource bounds of this adapter, not a maximum imposed by the game.
        integer(a.width, 200, 16384, 'viewport width'); integer(a.height, 100, 16384, 'viewport height');
        runtime.resizeViewport(a.width, a.height); break;
      }
      case 'store-bulk': active(); Game.storeBulkButton(integer(a.id, 0, 5, 'bulk control id')); break;
      case 'building-hover': {
        active(); const b = building(a.id); require(b.amount > 0 && b.canvas && !b.muted, 'building display unavailable');
        require(b.id !== 19 || a.leave || runtime.environment.nativeRngManipulation, 'You hover changes the RNG state and is excluded by the no-manipulation policy');
        require(Number.isFinite(a.x) && Number.isFinite(a.y) && a.x >= 0 && a.y >= 0 && a.x < b.canvas.width && a.y < b.canvas.height, 'point outside building canvas');
        if (!a.leave) exitTooltipPointer(b.canvas);
        const bounds = b.canvas.getBounds();
        b.canvas.dispatchEvent({ type: a.leave ? 'mouseout' : 'mouseover', target: b.canvas });
        b.canvas.dispatchEvent({ type: 'mousemove', target: b.canvas, pageX: a.x + bounds.left, pageY: a.y + bounds.top }); break;
      }
      case 'building-press': {
        active(); const b = building(a.id); require(b.amount > 0 && b.canvas && !b.muted, 'building display unavailable');
        require(b.id !== 19 || a.release || runtime.environment.nativeRngManipulation, 'You pointer input is excluded by the no-manipulation policy');
        require(typeof a.release === 'boolean', 'release must be boolean');
        context.document.dispatchEvent({ type: a.release ? 'mouseup' : 'mousedown', target: b.canvas }); break;
      }
      case 'wrinkler-hover': case 'wrinkler-poke': {
        active(); const w = Game.wrinklers[integer(a.id, 0, Game.wrinklers.length - 1, 'wrinkler id')];
        require(w.phase > 0 && Game.LeftBackground && Game.CanClick, 'wrinkler unavailable');
        if (a.type === 'wrinkler-poke') require(w.selected, 'hover the wrinkler and wait for native hit testing before clicking');
        const x = w.x + Math.sin(w.r * Math.PI / 180) * 90;
        const y = w.y + Math.cos(w.r * Math.PI / 180) * 90;
        const canvas = context.document.getElementById('backgroundLeftCanvas');
        exitTooltipPointer(canvas);
        context.document.dispatchEvent({ type: 'mousemove', target: canvas, pageX: x * Game.scale, pageY: y * Game.scale + context.TopBarOffset });
        if (a.type === 'wrinkler-poke') {
          context.document.dispatchEvent({ type: 'click', target: canvas });
        }
        break;
      }
      case 'gift-send': {
        active(); require(Game.Has('Wrapping paper') && Game.ascensionMode === 0 && !Game.hasBuff('Gifted out') && Game.cookies >= 1e9, 'gift sending unavailable');
        integer(a.amount ?? 1, 1, 1000, 'gift amount'); require(typeof (a.message ?? '') === 'string' && (a.message ?? '').length <= 100, 'gift message is too long');
        Game.promptGiftSend(); context.document.getElementById('giftAmount').value = a.amount ?? 1;
        context.document.getElementById('giftMessage').value = a.message ?? ''; uiClick('promptOption0'); break;
      }
      case 'gift-redeem': {
        active(); require(Game.Has('Wrapping paper') && Game.ascensionMode === 0 && !Game.hasBuff('Gifted out') && Game.cookies >= 1e9, 'gift redemption unavailable');
        require(typeof a.code === 'string' && a.code.length > 5 && a.code.length <= 4096, 'invalid gift code');
        Game.promptGiftRedeem(); const input = context.document.getElementById('giftCode'); input.value = a.code; input.dispatchEvent({ type: 'change' });
        if (!context.document.getElementById('promptOption0').classList.contains('disabled')) uiClick('promptOption0'); break;
      }
      case 'permanent-slot': {
        require(Game.OnAscend && !Game.AscendTimer, 'permanent slots require the ascension screen');
        const slot = integer(a.slot, 0, 4, 'permanent slot');
        require(Game.Has('Permanent upgrade slot ' + ['I','II','III','IV','V'][slot]), 'permanent slot is locked');
        const u = Game.UpgradesById[integer(a.id, 0, Game.UpgradesN - 1, 'upgrade id')];
        require(u.bought && u.unlocked && !u.noPerm && ['', 'cookie'].includes(u.pool) && !Game.permanentUpgrades.includes(u.id), 'upgrade cannot occupy this permanent slot');
        Game.AssignPermanentSlot(slot); uiClick(`upgradeForPermanent${u.id}`); uiClick('promptOption0'); break;
      }
      case 'minigame-refill': {
        const controls = { Farm: 'gardenLumpRefill', Temple: 'templeLumpRefill', 'Wizard tower': 'grimoireLumpRefill' };
        require(Object.hasOwn(controls, a.building), 'minigame has no lump refill'); minigame(a.building);
        require(Game.canLumps() && Game.lumps >= 1 && Game.canRefillLump(), 'lump refill unavailable'); uiClick(controls[a.building]); break;
      }
      case 'select-cosmetic': {
        active(); require(['Milk selector', 'Background selector', 'Golden cookie sound selector'].includes(a.selector), 'unknown cosmetic selector');
        const u = Game.Upgrades[a.selector]; require(u?.unlocked && u.choicesFunction && u.choicesPick, 'selector is locked');
        const choices = u.choicesFunction(); integer(a.id, 0, choices.length - 1, 'choice id'); require(!!choices[a.id], 'cosmetic choice is locked'); u.choicesPick(a.id); break;
      }
      case 'upgrade-santa': active(); require(Game.Has('A festive hat') && Game.santaLevel < Game.santaLevels.length - 1, 'Santa is unavailable'); Game.UpgradeSanta(); break;
      case 'upgrade-dragon': active(); require(Game.Has('A crumbly egg') && Game.dragonLevel < Game.dragonLevels.length - 1 && Game.dragonLevels[Game.dragonLevel].cost(), 'dragon level is unavailable'); Game.UpgradeDragon(); break;
      case 'dragon-aura': {
        active(); integer(a.id, 0, Object.keys(Game.dragonAuras).length - 1, 'aura id'); integer(a.slot ?? 0, 0, 1, 'slot');
        require(Game.Has('A crumbly egg') && Game.dragonLevel >= a.id + 4 && (!(a.slot ?? 0) || Game.dragonLevel === Game.dragonLevels.length - 1), 'dragon aura is locked');
        require(a.id === 0 || a.id !== ((a.slot ?? 0) === 0 ? Game.dragonAura2 : Game.dragonAura), 'aura already occupies other slot');
        Game.SetDragonAura(a.id, a.slot ?? 0); break;
      }
      case 'pet-dragon': active(); require(Game.Has('Pet the dragon') && Game.dragonLevel >= 4, 'dragon cannot be petted'); Game.specialTab = 'dragon'; Game.ToggleSpecialMenu(1); Game.ClickSpecialPic(); break;
      case 'garden-plant': {
        const M = minigame('Farm'); tile(M, a); const p = M.plants[a.seed];
        require(!!p && p.unlocked && p.plantable !== false && M.canPlant(p), 'seed cannot be planted'); M.useTool(p.id, a.x, a.y); break;
      }
      case 'garden-harvest': { const M = minigame('Farm'); tile(M, a); M.harvest(a.x, a.y, 1); break; }
      case 'garden-harvest-all': { const M = minigame('Farm'); M.harvestAll(); break; }
      case 'garden-soil': { const M = minigame('Farm'); const soil = M.soils[a.soil]; require(soil && !M.freeze && M.nextSoil <= runtime.clock.now && M.parent.amount >= soil.req, 'soil is unavailable'); uiClick(`gardenSoil-${soil.id}`); break; }
      case 'garden-freeze': { const M = minigame('Farm'); uiClick(`gardenTool-${M.tools.freeze.id}`); break; }
      case 'garden-sacrifice': { const M = minigame('Farm'); require(M.plantsUnlockedN === M.plantsN, 'seed log is incomplete'); M.askConvert(); break; }
      case 'cast-spell': { const M = minigame('Wizard tower'); const spell = M.spells[a.spell]; require(spell && M.magic >= M.getSpellCost(spell), 'spell is unavailable'); M.castSpell(spell); break; }
      case 'pantheon-slot': {
        const M = minigame('Temple'); const god = M.gods[a.god]; integer(a.slot, -1, 2, 'slot');
        require(god && (a.slot === -1 || M.swaps > 0), 'god or worship swap unavailable');
        M.dragGod(god); M.hoverSlot(a.slot); M.dropGod(); break;
      }
      case 'market-buy': case 'market-sell': {
        const M = minigame('Bank'); const id = integer(a.id, 0, M.goodsById.length - 1, 'good id');
        const good = M.goodsById[id]; require(good.building.highest > 0, 'market good is locked');
        marketControl(`bankGood-${id}`);
        const n = integer(a.amount ?? 1, 1, 10000, 'amount');
        require(a.type === 'market-buy' ? M.buyGood(id, n) : M.sellGood(id, n), 'trade rejected'); break;
      }
      case 'market-office': { const M = minigame('Bank'); const cost = M.offices[M.officeLevel].cost; require(cost && Game.Objects.Cursor.amount >= cost[0] && Game.Objects.Cursor.level >= cost[1], 'office unavailable'); marketControl('bankOfficeUpgrade').click(); break; }
      case 'market-broker': { const M = minigame('Bank'); require(M.brokers < M.getMaxBrokers() && Game.cookies >= M.getBrokerPrice(), 'broker unavailable'); marketControl('bankBrokersBuy').click(); break; }
      case 'market-loan': { const M = minigame('Bank'); integer(a.id, 1, 3, 'loan id'); require(M.officeLevel >= [2, 4, 5][a.id - 1] && !Game.hasBuff(`Loan ${a.id}`) && !Game.hasBuff(`Loan ${a.id} (interest)`), 'loan unavailable'); marketControl(`bankLoan${a.id}`).click(); break; }
      default: throw new Error(`Unknown action type: ${a.type}`);
    }
  };
  runtime.act = (action, { observe = true } = {}) => {
    require(action && typeof action === 'object' && ACTION_TYPES.includes(action.type), 'unknown action type');
    require(typeof observe === 'boolean', 'observe must be Boolean');
    const clean = JSON.parse(JSON.stringify(action));
    dispatch(clean);
    // Intermediate precommitted inputs need no return snapshot. Keep the
    // historical-access union and every native observer boundary unchanged.
    const result = observe ? runtime.snapshot() : (runtime.remember(), undefined);
    const actionIndex = runtime.recordAction(clean);
    runtime.notifyTransition('action', { action: clean, actionIndex }); return result;
  };
  runtime.actions = () => {
    const actions = [{ type: 'wait', milliseconds: 1000 / Game.fps }];
    if (!Game.promptOn && !context.document.getElementById('game').classList.contains('ascending')) actions.push({ type: 'export-save' });
    if (!Game.OnAscend && !Game.AscendTimer && !Game.ReincarnateTimer) {
      actions.push({ type: 'click' }, { type: 'ascend' });
      for (const b of Object.values(Game.Objects)) if (!b.locked && Game.cookies >= b.getPrice()) actions.push({ type: 'buy-building', id: b.id, amount: 1 });
      for (const u of Object.values(Game.Upgrades)) if (u.pool !== 'prestige' && !['debug','unused','dungeon','shadow'].includes(u.pool) && u.unlocked && !u.bought && u.canBuy()) actions.push({ type: 'buy-upgrade', id: u.id });
      for (const s of Game.shimmers) actions.push({ type: 'click-shimmer', id: runtime.shimmerControlId(s) });
    }
    return actions;
  };
}

export function replayRuntime(events, options = {}) {
  if (!Array.isArray(events)) throw new Error('Replay requires a recorded action array; a summary is not a full replay');
  const runtime = createRuntime(options);
  for (const action of events) runtime.act(action);
  return runtime;
}

/** Build static identities in a separate engine instance. Forced minigame setup is catalogue-only. */
export function buildCatalogue(options = {}) {
  const runtime = createRuntime(options);
  const { Game, source } = runtime;
  for (const [name, filename] of Object.entries(MINIGAMES)) {
    runtime.evaluate(source.sources[filename], filename);
    Game.Objects[name].minigame.launch();
  }
  const garden = Game.Objects.Farm.minigame;
  const market = Game.Objects.Bank.minigame;
  const catalogue = {
    schemaVersion: 1, gameVersion: '2.053', edition: 'steam', environment: runtime.environment, sourceHashes: source.hashes,
    description: 'Runtime constructor catalogue from pinned unmodified engine. Forced minigame initialization only enumerates identities and does not represent legal new-save progress.',
    achievements: Object.values(Game.AchievementsById).map(x => ({ id: x.id, name: x.name, pool: x.pool, vanilla: !!x.vanilla, normal: !!Game.CountsAsAchievementOwned(x.pool) })),
    upgrades: Object.values(Game.UpgradesById).map(x => ({ id: x.id, name: x.name, pool: x.pool,
      parents: (x.parents || []).filter(p => p !== -1).map(p => p.id), toggleInto: x.toggleInto || null,
      season: x.season || null, vanilla: !!x.vanilla, noPerm: !!x.noPerm, priceLumps: x.priceLumps || 0,
    })),
    buildings: Object.values(Game.ObjectsById).map(x => ({ id: x.id, name: x.name, minigame: x.minigameName || null })),
    garden: {
      seeds: Object.values(garden.plants).map(x => ({ id: x.id, key: x.key, name: x.name, plantable: x.plantable !== false, mature: x.mature, ageTick: x.ageTick, ageTickR: x.ageTickR })),
      soils: Object.values(garden.soils).map(x => ({ id: x.id, key: x.key, name: x.name, req: x.req, tick: x.tick })),
      plotLimits: garden.plotLimits,
    },
    cosmetics: {
      milks: Array.from(Game.AllMilks, (x, id) => ({ id, name: x.bname, type: x.type, rank: x.rank ?? null })),
      backgrounds: Array.from(Game.AllBGs, (x, id) => ({ id, name: x.name, order: x.order || id })),
      chimes: Array.from(Game.Upgrades['Golden cookie sound selector'].choicesFunction(), (x, id) => ({ id, name: x.name })),
    },
    dragon: { levels: Game.dragonLevels.map((x, id) => ({ id, name: x.name, action: x.action })), auras: Object.values(Game.dragonAuras).map(x => ({ id: x.id, name: x.name })) },
    santa: { levels: Game.santaLevels.map((name, id) => ({ id, name })) },
    market: {
      offices: market.offices.map((x, id) => ({ id, name: x.name, cost: x.cost || null })),
      loans: market.loanTypes.map((x, i) => ({ id: i + 1, name: x[0], multiplier: x[1], durationMinutes: x[2], interestMultiplier: x[3], interestMinutes: x[4], downPayment: x[5], minOfficeLevel: [2, 4, 5][i] })),
      goods: Object.values(market.goods).map(x => ({ id: x.id, key: x.key, name: x.name, building: x.building.id })),
    },
    grimoire: { spells: Object.entries(Game.Objects['Wizard tower'].minigame.spells).map(([key, x]) => ({ id: x.id, key, name: x.name, costMin: x.costMin, costPercent: x.costPercent })) },
    pantheon: { gods: Object.entries(Game.Objects.Temple.minigame.gods).map(([key, x]) => ({ id: x.id, key, name: x.name })) },
  };
  return JSON.parse(JSON.stringify(catalogue));
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  if (process.argv[2] !== 'catalogue') throw new Error('Usage: node model/runtime.mjs catalogue [output.json] [game-source-directory]');
  const catalogue = buildCatalogue({ sourceDirectory: process.argv[4] });
  const output = resolve(process.argv[3] || 'model/catalogue.json');
  writeFileSync(output, `${JSON.stringify(catalogue, null, 2)}\n`);
  console.log(`Wrote ${catalogue.achievements.length} achievements, ${catalogue.upgrades.length} upgrades and four minigame catalogues to ${output}`);
}

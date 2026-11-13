import { writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { runNativeBrowser } from '../model/native-browser.mjs';
import { compilePinnedGameAst } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';

const roots = ['Element', 'Node', 'HTMLElement', 'CanvasRenderingContext2D', 'Document', 'HTMLDocument',
  'HTMLCanvasElement', 'HTMLImageElement', 'HTMLAudioElement', 'HTMLMediaElement', 'CSSStyleDeclaration',
  'DOMTokenList', 'Window', 'EventTarget', 'Text', 'Comment', 'DocumentFragment', 'DocumentType', 'HTMLCollection', 'NodeList',
  'NamedNodeMap', 'Attr', 'HTMLBodyElement', 'HTMLDivElement', 'HTMLInputElement', 'HTMLTextAreaElement',
  'HTMLSelectElement', 'HTMLOptionElement', 'HTMLAnchorElement', 'HTMLScriptElement', 'HTMLStyleElement',
  'DOMRect', 'DOMRectReadOnly', 'Event', 'UIEvent', 'MouseEvent', 'KeyboardEvent', 'TouchEvent', 'FocusEvent', 'InputDeviceCapabilities',
  'Screen', 'Navigator', 'Location', 'Performance', 'Storage', 'XMLHttpRequest', 'Image', 'Audio', 'HTMLUnknownElement'];

const ast = compilePinnedGameAst();
const source = loadGameSource();
const tags = new Set();
for (const node of ast.nodes) {
  if (node.tag === 'literal' && node.literalKind === 'string') {
    const text = String.fromCharCode(...node.units);
    for (const match of text.matchAll(/<\/?([A-Za-z][A-Za-z0-9:-]*)/g)) tags.add(match[1].toLowerCase());
  }
  if (node.tag === 'call') {
    const callee = ast.nodes[node.callee];
    const name = callee?.tag === 'member' ? ast.nodes[callee.property]?.name : null;
    if (name === 'createElement' || name === 'createElementNS') {
      const argument = ast.nodes[node.arguments[name === 'createElement' ? 0 : 1]];
      if (argument?.literalKind === 'string') {
        const value = String.fromCharCode(...argument.units);
        if (/^[A-Za-z][A-Za-z0-9:-]*$/.test(value)) tags.add(value.toLowerCase());
      }
    }
  }
}
for (const match of source.sources['index.html'].matchAll(/<\/?([A-Za-z][A-Za-z0-9:-]*)/g)) tags.add(match[1].toLowerCase());

const capture = function (request) {
  const rootNames = request.roots.slice();
  const identities = new WeakMap(), callableMetadata = new WeakMap(), symbolIdentities = new Map(), described = new Set(), queue = [], objects = [], roots = [];
  let nativeFunctionTextInspections = 0;
  let nextId = 0;
  const identity = value => { if (!identities.has(value)) identities.set(value, nextId++); return identities.get(value); };
  const symbol = value => { if (!symbolIdentities.has(value)) symbolIdentities.set(value, symbolIdentities.size); return { type: 'symbol', id: symbolIdentities.get(value), display: String(value) }; };
  const data = (object, name) => {
    const descriptor = Object.getOwnPropertyDescriptor(object, name);
    return descriptor && 'value' in descriptor ? descriptor.value : undefined;
  };
  const callable = value => {
    if (value === undefined) return null;
    if (callableMetadata.has(value)) return callableMetadata.get(value);
    enqueue(value, 'native callable ' + data(value, 'name'));
    // Explicit native introspection, independent of mutable name properties.
    // The temporary page contains no source game or policy callbacks.
    const sourceText = Function.prototype.toString.call(value);
    nativeFunctionTextInspections++;
    const metadata = { id: identity(value), name: data(value, 'name'), length: data(value, 'length'),
      sourceText: Array.from({length:sourceText.length},(_,index)=>sourceText.charCodeAt(index)) };
    callableMetadata.set(value,metadata);
    return metadata;
  };
  const value = item => {
    if (item === null) return { type: 'null' };
    if (item === undefined) return { type: 'undefined' };
    if (typeof item === 'function') return { type: 'function', ...callable(item) };
    if (typeof item === 'object') return { type: 'object', id: identity(item) };
    if (typeof item === 'number') {
      const bytes = new ArrayBuffer(8), view = new DataView(bytes); view.setFloat64(0, item, false);
      return { type: 'number', bits: view.getBigUint64(0, false).toString() };
    }
    if (typeof item === 'string') return { type: 'string', units: Array.from({ length: item.length }, (_, i) => item.charCodeAt(i)) };
    if (typeof item === 'boolean') return { type: 'boolean', value: item };
    if (typeof item === 'symbol') return symbol(item);
    return { type: typeof item };
  };
  const enqueue = (object, label) => {
    if (object === null) return null;
    const id = identity(object);
    if (!described.has(id)) { described.add(id); queue.push({ object, id, label }); }
    return id;
  };
  const intrinsics = [];
  for (const name of ['Object', 'Function', 'Array', 'String', 'Number', 'Boolean', 'RegExp', 'Math', 'JSON', 'Date',
    'Error', 'EvalError', 'RangeError', 'ReferenceError', 'SyntaxError', 'TypeError', 'URIError', 'Symbol', 'Promise']) {
    const native = data(globalThis, name);
    if (native && (typeof native === 'object' || typeof native === 'function')) {
      const prototype = data(native, 'prototype');
      intrinsics.push({ name, id: identity(native), prototype: prototype ? identity(prototype) : null });
      if (typeof native === 'function') enqueue(native, name);
      if (prototype) enqueue(prototype, name + '.prototype');
    }
  }
  const elementTypes = request.tags.map(tag => {
    const element = document.createElement(tag);
    const prototype = Object.getPrototypeOf(element);
    const constructor = data(prototype, 'constructor');
    const name = data(constructor, 'name');
    if (!rootNames.includes(name)) rootNames.push(name);
    return { tag, constructor: enqueue(constructor, name), prototype: enqueue(prototype, name + '.prototype') };
  });
  for (const name of rootNames) {
    const descriptor = Object.getOwnPropertyDescriptor(globalThis, name);
    if (!descriptor || !('value' in descriptor) || typeof descriptor.value !== 'function') {
      roots.push({ name, unavailableWithoutGetter: true }); continue;
    }
    const constructor = descriptor.value;
    roots.push({ name, constructor: enqueue(constructor, name),
      prototype: enqueue(data(constructor, 'prototype'), name + '.prototype') });
  }
  // These known Window values are acquired explicitly. Descriptor
  // traversal below does not invoke any accessor found on these objects.
  const instances = [['navigator', 'Navigator'], ['screen', 'Screen'], ['location', 'Location'], ['document', 'Document'], ['console', 'Console']]
    .map(([name, label]) => ({ name, id: enqueue(globalThis[name], label) }));
  enqueue(globalThis, 'globalThis');
  for (let i = 0; i < queue.length; i += 1) {
    const { object, id, label } = queue[i];
    const properties = Reflect.ownKeys(object).map(name => {
      const descriptor = Object.getOwnPropertyDescriptor(object, name);
      const key = typeof name === 'string' ? { type: 'string', name } : symbol(name);
      const common = { key, enumerable: descriptor.enumerable, configurable: descriptor.configurable };
      return 'value' in descriptor ? { ...common, kind: 'data', writable: descriptor.writable, value: value(descriptor.value) }
        : { ...common, kind: 'accessor', getter: callable(descriptor.get), setter: callable(descriptor.set) };
    });
    objects.push({ id, label, objectType: typeof object, callable: typeof object === 'function' ? callable(object) : null,
      prototype: enqueue(Object.getPrototypeOf(object), label + '.[[Prototype]]'), properties });
  }
  return { roots, objects, intrinsics, elementTypes, instances, referencedIdentities: nextId, referencedSymbols: symbolIdentities.size,
    descriptorTraversalGetterInvocations: 0, explicitInstanceAcquisitions: instances.length, nativeFunctionTextInspections };
};

const report = runNativeBrowser(capture.toString(), { roots, tags: [...tags].sort() }, { documentMode: 'file' });
const catalogueText = JSON.stringify(report.result);
const output = {
  schema: 2,
  purpose: 'Observed native property identities and descriptors. Unimplemented host operations must stay explicit; this catalogue does not define their semantics.',
  inspection: 'The named Window values navigator/screen/location/document/console are acquired explicitly. Descriptor traversal invokes no captured accessor. Each known native callable is inspected with the native Function.prototype.toString. Element type probes call native createElement for source literal tag candidates; this does not assert that every candidate is active markup.',
  versions: report.versions, architecture: report.identity.arch, platform: report.identity.platform,
  renderer: report.renderer, executableSha256: report.executableHash,
  auditConfiguration: report.auditConfiguration,
  gameEntryPointExecuted: report.gameEntryPointExecuted, externalNetworking: report.externalNetworking,
  descriptorSha256: createHash('sha256').update(catalogueText).digest('hex'),
  ...report.result,
};
writeFileSync(new URL('../model/browser-host-catalogue.json', import.meta.url), JSON.stringify(output, null, 2) + '\n');
console.log(JSON.stringify({ roots: output.roots.length, instances: output.instances.length, elementTypes: output.elementTypes.length, describedObjects: output.objects.length,
  properties: output.objects.reduce((total, object) => total + object.properties.length, 0),
  descriptorTraversalGetterInvocations: output.descriptorTraversalGetterInvocations,
  explicitInstanceAcquisitions: output.explicitInstanceAcquisitions, descriptorSha256: output.descriptorSha256 }));

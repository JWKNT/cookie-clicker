import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { loadGameSource } from './game-source.mjs';
import { clockAnnotations } from './clock-annotations.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const eslintScope = require('eslint-scope');
export const AST_SCHEMA = 'cookie-clicker-es5-ast-v2';
export const AST_OPERATORS = Object.freeze({
  unary: { delete: 'delete', void: 'void', typeof: 'typeOf', '+': 'plus', '-': 'minus', '~': 'bitNot', '!': 'not' },
  update: { '++': 'increment', '--': 'decrement' },
  binary: { '==': 'equal', '!=': 'notEqual', '===': 'strictEqual', '!==': 'strictNotEqual', '<': 'less', '<=': 'lessEqual', '>': 'greater', '>=': 'greaterEqual', '<<': 'shiftLeft', '>>': 'shiftRight', '>>>': 'unsignedShiftRight', '+': 'add', '-': 'subtract', '*': 'multiply', '/': 'divide', '%': 'remainder', '|': 'bitOr', '^': 'bitXor', '&': 'bitAnd', in: 'inOp', instanceof: 'instanceOf' },
  logical: { '&&': 'and', '||': 'or' },
  assignment: { '=': 'assign', '+=': 'add', '-=': 'subtract', '*=': 'multiply', '/=': 'divide', '%=': 'remainder', '<<=': 'shiftLeft', '>>=': 'shiftRight', '>>>=': 'unsignedShiftRight', '|=': 'bitOr', '^=': 'bitXor', '&=': 'bitAnd' },
});
const sha256 = text => createHash('sha256').update(text).digest('hex');
const utf16 = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
export function numberLiteralBits(value) {
  const bytes = Buffer.alloc(8); bytes.writeDoubleBE(value); return bytes.readBigUInt64BE().toString();
}
const ownStrict = body => body.some((node, i) => node.directive === 'use strict'
  && body.slice(0, i).every(prior => typeof prior.directive === 'string'));
const walk = (root, callback) => {
  const pending = [{ node: root, parent: null }];
  while (pending.length) {
    const { node, parent } = pending.pop(); callback(node, parent);
    const children = [];
    for (const [key, value] of Object.entries(node)) {
      if (key === 'loc' || key === 'range') continue;
      if (Array.isArray(value)) children.push(...value.filter(child => child?.type));
      else if (value?.type) children.push(value);
    }
    for (let i = children.length - 1; i >= 0; i--) pending.push({ node: children[i], parent: node });
  }
};

/** Explicit ES5 syntax translation. It does not establish JavaScript semantics. */
class Compiler {
  constructor() {
    this.nodes = []; this.units = []; this.sourceTexts = []; this.functions = []; this.generatedHandlers = [];
    this.literalCandidates = []; this.nodeTypes = new Map(); this.operators = new Map();
    this.globalReferences = []; this.globalDeclarations = []; this.globalMemberUses = [];
    this.dynamicCode = []; this.regexLiterals = []; this.numericCalls = []; this.clockMaps = []; this.selectedClock = false;
  }
  fail(unit, node, reason) {
    throw new Error(`Unsupported JavaScript syntax in ${unit.name}:${node?.loc?.start.line ?? 1}:${node?.loc?.start.column ?? 0}: ${reason}`);
  }
  span(unit, node) { return { unit: unit.id, start: node.start, end: node.end, line: node.loc.start.line, column: node.loc.start.column, endLine: node.loc.end.line, endColumn: node.loc.end.column }; }
  emit(unit, original, kind, tag, fields = {}) {
    const id = this.nodes.length;
    this.nodes.push({ id, kind, tag, ...fields, source: this.span(unit, original) });
    return id;
  }
  identifier(unit, node) {
    if (node?.type !== 'Identifier') this.fail(unit, node, 'binding must be an ES5 identifier');
    return node.name;
  }
  operator(unit, node, kind) {
    if (!Object.hasOwn(AST_OPERATORS[kind], node.operator)) this.fail(unit, node, `operator ${node.operator}`);
    return AST_OPERATORS[kind][node.operator];
  }
  declarations(unit, node, strict) {
    if (node.kind !== 'var') this.fail(unit, node, `declaration kind ${node.kind}`);
    return node.declarations.map(d => ({ name: this.identifier(unit, d.id), value: d.init ? this.expr(unit, d.init, strict) : null }));
  }
  propertyName(unit, node) {
    if (node.type === 'Identifier') return { kind: 'identifier', name: node.name };
    if (node.type === 'Literal' && typeof node.value === 'string') return { kind: 'string', units: utf16(node.value), raw: node.raw };
    if (node.type === 'Literal' && typeof node.value === 'number') return { kind: 'number', bits: numberLiteralBits(node.value), raw: node.raw };
    this.fail(unit, node, 'computed or unsupported property name');
  }
  functionFields(unit, node, inheritedStrict) {
    if (node.generator || node.async || node.expression) this.fail(unit, node, 'non-ES5 function');
    const strict = inheritedStrict || ownStrict(node.body.body);
    const fields = { name: node.id ? this.identifier(unit, node.id) : null,
      parameters: node.params.map(p => this.identifier(unit, p)),
      body: node.body.body.map(statement => this.stmt(unit, statement, strict)), strict,
      sourceText: utf16(this.sourceTexts[unit.id].slice(node.start, node.end)) };
    return fields;
  }
  expr(unit, node, strict) {
    let tag; let fields = {};
    const clock = this.clockMaps[unit.id]?.get(node.start + ':' + node.end);
    if (clock?.kind === 'zero') {
      if (node.type !== 'Literal' || node.value !== 0) this.fail(unit,node,'clock zero certificate mismatch');
      return this.emit(unit,node,'expr','clockZero');
    }
    if (clock?.kind === 'read') {
      if (node.type !== 'CallExpression' || node.arguments.length !== 1 || node.callee.type !== 'Identifier' || node.callee.name !== (clock.integer?'parseInt':'parseFloat')) this.fail(unit,node,'clock reader certificate mismatch');
      return this.emit(unit,node,'expr','clockRead',{integer:clock.integer,callee:this.expr(unit,node.callee,strict),argument:this.expr(unit,node.arguments[0],strict)});
    }
    switch (node.type) {
      case 'Identifier': tag = 'identifier'; fields = { name: node.name }; break;
      case 'ThisExpression': tag = 'this'; break;
      case 'Literal':
        if (node.regex) { tag = 'regexp'; fields = { pattern: utf16(node.regex.pattern), flags: node.regex.flags, raw: node.raw }; }
        else if (node.value === null) { tag = 'literal'; fields = { literalKind: 'null' }; }
        else if (typeof node.value === 'boolean') { tag = 'literal'; fields = { literalKind: 'boolean', value: node.value }; }
        else if (typeof node.value === 'number') { tag = 'literal'; fields = { literalKind: 'number', bits: numberLiteralBits(node.value), raw: node.raw }; }
        else if (typeof node.value === 'string') { tag = 'literal'; fields = { literalKind: 'string', units: utf16(node.value), raw: node.raw }; }
        else this.fail(unit, node, 'unsupported literal');
        break;
      case 'ArrayExpression': tag = 'array'; fields = { elements: node.elements.map(e => e ? this.expr(unit, e, strict) : null) }; break;
      case 'ObjectExpression':
        tag = 'object'; fields = { properties: node.properties.map(p => {
          if (p.computed || p.method || p.shorthand || !['init', 'get', 'set'].includes(p.kind)) this.fail(unit, p, 'unsupported property semantics');
          const value = this.expr(unit, p.value, strict);
          // ES2018 Function#toString retains accessor introducer and key;
          // Acorn's FunctionExpression range starts after that property key.
          if (p.kind === 'get' || p.kind === 'set') {
            this.nodes[value].sourceText = utf16(this.sourceTexts[unit.id].slice(p.start, p.end));
          }
          return { key: this.propertyName(unit, p.key), kind: p.kind, value, source: this.span(unit, p) };
        }) }; break;
      case 'FunctionExpression': tag = 'function'; fields = this.functionFields(unit, node, strict); break;
      case 'SequenceExpression': tag = 'sequence'; fields = { expressions: node.expressions.map(e => this.expr(unit, e, strict)) }; break;
      case 'UnaryExpression': tag = 'unary'; fields = { operator: this.operator(unit, node, 'unary'), argument: this.expr(unit, node.argument, strict) }; break;
      case 'UpdateExpression': tag = 'update'; fields = { operator: this.operator(unit, node, 'update'), argument: this.expr(unit, node.argument, strict), isPrefix: node.prefix }; break;
      case 'BinaryExpression': case 'LogicalExpression': case 'AssignmentExpression':
        tag = { BinaryExpression: 'binary', LogicalExpression: 'logical', AssignmentExpression: 'assignment' }[node.type];
        fields = { operator: this.operator(unit, node, tag), left: this.expr(unit, node.left, strict), right: this.expr(unit, node.right, strict) }; break;
      case 'ConditionalExpression': tag = 'conditional'; fields = { test: this.expr(unit, node.test, strict), consequent: this.expr(unit, node.consequent, strict), alternate: this.expr(unit, node.alternate, strict) }; break;
      case 'MemberExpression': tag = 'member'; fields = { object: this.expr(unit, node.object, strict), property: this.expr(unit, node.property, strict), computed: node.computed }; break;
      case 'CallExpression': case 'NewExpression':
        tag = node.type === 'CallExpression' ? 'call' : 'construct';
        fields = { callee: this.expr(unit, node.callee, strict), arguments: node.arguments.map(a => this.expr(unit, a, strict)) }; break;
      default: this.fail(unit, node, node.type);
    }
    const id = this.emit(unit, node, 'expr', tag, fields);
    if (tag === 'function') this.functions.push({ node: id, ...this.span(unit, node), name: fields.name, parameters: fields.parameters, strict: fields.strict, bodySource: this.span(unit, node.body) });
    if (node.type === 'Literal' && typeof node.value === 'string' && /\bon[a-z]+\s*=/i.test(node.value)) this.literalCandidates.push({ node: id, unit: unit.id, source: this.span(unit, node), text: node.value });
    return id;
  }
  stmt(unit, node, strict) {
    let tag; let fields = {};
    const expr = n => this.expr(unit, n, strict);
    const stmt = n => this.stmt(unit, n, strict);
    switch (node.type) {
      case 'EmptyStatement': tag = 'empty'; break;
      case 'ExpressionStatement': tag = 'expression'; fields = { expression: expr(node.expression), directive: node.directive ?? null }; break;
      case 'BlockStatement': tag = 'block'; fields = { body: node.body.map(stmt) }; break;
      case 'VariableDeclaration': tag = 'variable'; fields = { declarations: this.declarations(unit, node, strict) }; break;
      case 'FunctionDeclaration': tag = 'functionDeclaration'; fields = this.functionFields(unit, node, strict); if (fields.name === null) this.fail(unit, node, 'anonymous declaration'); break;
      case 'IfStatement': tag = 'ifThenElse'; fields = { test: expr(node.test), consequent: stmt(node.consequent), alternate: node.alternate ? stmt(node.alternate) : null }; break;
      case 'WhileStatement': tag = 'while'; fields = { test: expr(node.test), body: stmt(node.body) }; break;
      case 'DoWhileStatement': tag = 'doWhile'; fields = { body: stmt(node.body), test: expr(node.test) }; break;
      case 'ForStatement':
        tag = 'forLoop'; fields = { initial: node.init ? node.init.type === 'VariableDeclaration'
          ? { kind: 'variables', declarations: this.declarations(unit, node.init, strict) }
          : { kind: 'expression', value: expr(node.init) } : null,
        test: node.test ? expr(node.test) : null, update: node.update ? expr(node.update) : null, body: stmt(node.body) }; break;
      case 'ForInStatement':
        tag = 'forIn';
        if (node.left.type === 'VariableDeclaration' && (node.left.kind !== 'var' || node.left.declarations.length !== 1 || node.left.declarations[0].init)) this.fail(unit, node.left, 'for-in initializer or multiple bindings');
        fields = { binding: node.left.type === 'VariableDeclaration'
          ? { kind: 'variable', name: this.identifier(unit, node.left.declarations[0].id) }
          : { kind: 'reference', value: expr(node.left) }, object: expr(node.right), body: stmt(node.body) }; break;
      case 'ReturnStatement': tag = 'return'; fields = { value: node.argument ? expr(node.argument) : null }; break;
      case 'ThrowStatement': tag = 'throw'; fields = { value: expr(node.argument) }; break;
      case 'BreakStatement': case 'ContinueStatement': tag = node.type === 'BreakStatement' ? 'break' : 'continue'; fields = { label: node.label?.name ?? null }; break;
      case 'LabeledStatement': tag = 'labeled'; fields = { label: this.identifier(unit, node.label), body: stmt(node.body) }; break;
      case 'TryStatement': tag = 'tryCatchFinally'; fields = { body: stmt(node.block), handler: node.handler ? { name: this.identifier(unit, node.handler.param), body: stmt(node.handler.body) } : null, finalizer: node.finalizer ? stmt(node.finalizer) : null }; break;
      default: this.fail(unit, node, node.type);
    }
    const id = this.emit(unit, node, 'stmt', tag, fields);
    if (tag === 'functionDeclaration') this.functions.push({ node: id, ...this.span(unit, node), name: fields.name, parameters: fields.parameters, strict: fields.strict, bodySource: this.span(unit, node.body) });
    return id;
  }
  addUnit(text, { name, kind = 'script', origin = null, inheritedStrict = false, unboundedClock = false, clockFragments = [] } = {}) {
    const unit = { id: this.units.length, name, kind, origin, textSha256: sha256(text), lengthUtf16: text.length, root: null };
    let ast;
    try {
      const options = { ecmaVersion: 5, sourceType: 'script', locations: true, ranges: true, allowReturnOutsideFunction: kind.endsWith('handler') };
      // Acorn's top-level parse otherwise starts in sloppy mode. A separate
      // strict validation parse preserves the original source offsets below.
      if (inheritedStrict) acorn.parse(`"use strict";\n${text}`, options);
      ast = acorn.parse(text, options);
    }
    catch (error) { const failure = new Error(`Unsupported JavaScript syntax in ${name}: ${error.message}`); failure.syntaxPhase = 'parse'; throw failure; }
    this.units.push(unit);
    this.sourceTexts.push(text);
    this.clockMaps.push(clockAnnotations(text,{unboundedClock,clockFragments}));
    this.selectedClock ||= unboundedClock;
    const strict = inheritedStrict || ownStrict(ast.body);
    const body = ast.body.map(node => this.stmt(unit, node, strict));
    unit.root = this.emit(unit, ast, 'program', 'program', { body, strict });
    unit.directivePrologue = ast.body.slice(0, ast.body.findIndex(n => typeof n.directive !== 'string') < 0 ? ast.body.length : ast.body.findIndex(n => typeof n.directive !== 'string')).map(n => ({ directive: n.directive, source: this.span(unit, n) }));
    const scope = eslintScope.analyze(ast, { ecmaVersion: 5, sourceType: 'script', impliedStrict: inheritedStrict, optimistic: false, ignoreEval: false });
    const free = new Set(scope.globalScope.through.map(r => r.identifier));
    for (const variable of scope.globalScope.variables) this.globalDeclarations.push({ name: variable.name, unit: unit.id, sources: variable.identifiers.map(n => this.span(unit, n)) });
    for (const ref of scope.globalScope.through) this.globalReferences.push({ name: ref.identifier.name, read: ref.isRead(), write: ref.isWrite(), source: this.span(unit, ref.identifier), handlerParameter: kind.endsWith('handler') && ref.identifier.name === 'event' });
    const path = node => node.type === 'Identifier' && free.has(node) ? [node.name] : node.type === 'MemberExpression' ? (() => { const base = path(node.object); if (!base) return null; return [...base, node.computed ? node.property.type === 'Literal' && ['string', 'number'].includes(typeof node.property.value) ? String(node.property.value) : null : node.property.name]; })() : null;
    walk(ast, (node, parent) => {
      this.nodeTypes.set(node.type, (this.nodeTypes.get(node.type) || 0) + 1);
      if (node.operator) this.operators.set(node.operator, (this.operators.get(node.operator) || 0) + 1);
      if (node.type === 'MemberExpression' && !(parent?.type === 'MemberExpression' && parent.object === node)) { const parts = path(node); if (parts) this.globalMemberUses.push({ path: parts, source: this.span(unit, node) }); }
      if (node.type === 'Literal' && node.regex) this.regexLiterals.push({ pattern: utf16(node.regex.pattern), flags: node.regex.flags, source: this.span(unit, node) });
      if (['CallExpression', 'NewExpression'].includes(node.type) && node.callee.type === 'Identifier' && ['eval', 'Function'].includes(node.callee.name)) this.dynamicCode.push({ operation: node.callee.name, source: this.span(unit, node), argumentCount: node.arguments.length });
      if (['CallExpression', 'NewExpression'].includes(node.type)) {
        const callee = node.callee;
        const method = callee.type === 'Identifier' ? callee.name : callee.type === 'MemberExpression' && !callee.computed ? callee.property.name : null;
        if (['toString', 'toFixed', 'toPrecision', 'toExponential', 'parseInt', 'parseFloat', 'Number'].includes(method)
          || callee.type === 'MemberExpression' && callee.object.type === 'Identifier' && callee.object.name === 'Math') {
          this.numericCalls.push({ source: this.span(unit, node), callKind: callee.type === 'Identifier' ? 'global' : 'member',
            callee: text.slice(callee.start, callee.end), method, arguments: node.arguments.map(a => text.slice(a.start, a.end)) });
        }
      }
    });
    return unit.id;
  }
  result(extra = {}) {
    return { schemaVersion: 2, schema: AST_SCHEMA, parser: { name: 'acorn', version: acorn.version, ecmaVersion: 5, scopeAnalyzer: 'eslint-scope', scopeAnalyzerVersion: require('eslint-scope/package.json').version },
      sourceCorrespondenceVerified: false, javascriptSemanticsVerified: false,
      ...(this.selectedClock ? { clockModel: 'selected-unbounded-v1' } : {}),
      representation: { references: 'zero-based node IDs; every child ID is less than its parent ID', strings: 'UTF-16 code unit arrays', numbers: 'binary64 bits as unsigned decimal strings; raw numeric spelling retained', sourceOffsets: 'UTF-16 offsets in the named compilation unit', evaluationOrder: 'source operand, statement, argument and property order; no callback execution or substitution' },
      ...extra, units: this.units, nodes: this.nodes, functions: this.functions, generatedHandlers: this.generatedHandlers,
      inventory: { nodeTypes: Object.fromEntries([...this.nodeTypes].sort()), operators: Object.fromEntries([...this.operators].sort()), functions: this.functions.length, strictFunctions: this.functions.filter(f => f.strict).length, regexLiterals: this.regexLiterals.length },
      hostRequirements: { interpretation: 'Exact syntactic unresolved references and uses in these units; aliases, dynamic properties, generated code and browser behavior require execution semantics, not a finite static whitelist.', globalDeclarations: this.globalDeclarations, globalReferences: this.globalReferences, globalMemberUses: this.globalMemberUses, dynamicCode: this.dynamicCode, regexLiterals: this.regexLiterals, numericCalls: this.numericCalls,
        unresolved: ['ECMAScript built-ins and prototypes, property descriptors/enumeration and coercions', 'RegExp and dynamic eval/Function compilation', 'DOM/HTML parsing, inline-handler scope, event dispatch, layout, canvas, audio and image loading', 'Clock/calendar, timer ordering, locale loading, storage and isolated Steam services', 'Free-draw probability law and native explicitly seeded generator execution'] } };
  }
}

export function compileJavaScript(text, options = {}) {
  const compiler = new Compiler(); compiler.addUnit(text, { name: 'input.js', ...options }); return compiler.result();
}

function decodeAttribute(text) {
  return text.replace(/&(#x[0-9a-f]+|#\d+|amp|quot|apos|lt|gt|nbsp);/gi, (_, entity) => {
    if (entity[0] === '#') {
      let point = entity[1].toLowerCase() === 'x' ? parseInt(entity.slice(2), 16) : Number(entity.slice(1));
      if (!point || point > 0x10ffff || point >= 0xd800 && point <= 0xdfff) point = 0xfffd;
      return String.fromCodePoint(point);
    }
    return { amp: '&', quot: '"', apos: "'", lt: '<', gt: '>', nbsp: '\u00a0' }[entity.toLowerCase()];
  });
}

/** Scan quoted event attributes. Incomplete string fragments stay explicit. */
function handlerAttributes(text) {
  const handlers = [];
  for (const match of text.matchAll(/\b(on[a-z]+)\s*=\s*(["'])/gi)) {
    const start = match.index + match[0].length; const end = text.indexOf(match[2], start);
    handlers.push({ event: match[1].toLowerCase(), start, end: end < 0 ? text.length : end, complete: end >= 0, text: text.slice(start, end < 0 ? text.length : end) });
  }
  return handlers;
}

export function compilePinnedGameAst({ sourceDirectory, unboundedClock = false } = {}) {
  const source = loadGameSource(sourceDirectory); const compiler = new Compiler();
  const scriptUnits = new Map();
  for (const [file, text] of Object.entries(source.sources)) if (file.endsWith('.js')) scriptUnits.set(file, compiler.addUnit(text, { name: file, origin: { kind: 'pinned-file', file }, unboundedClock }));
  const html = source.sources['index.html'];
  const active = html.replace(/<!--[\s\S]*?-->/g, comment => comment.replace(/[^\r\n]/g, ' '));
  const pageScripts = []; const pageHandlers = [];
  // Script text is raw text in HTML. Remove it before scanning tag attributes.
  const scriptsRemoved = active.replace(/<script\b([^>]*)>([\s\S]*?)<\/script\s*>/gi, (whole, attributes, text, offset) => {
    const src = attributes.match(/\bsrc\s*=\s*(["'])(.*?)\1/i)?.[2];
    const start = offset + whole.indexOf('>') + 1;
    if (src) {
      const filename = src.split('?')[0];
      pageScripts.push(scriptUnits.has(filename) ? { kind: 'pinned-script', src, unit: scriptUnits.get(filename), start: offset, end: offset + whole.length }
        : { kind: 'external-host-script', src, start: offset, end: offset + whole.length });
    } else {
      const unit = compiler.addUnit(text, { name: `index.html:inline:${start}`, kind: 'inline-script', origin: { kind: 'html-script', file: 'index.html', start, end: start + text.length } });
      pageScripts.push({ kind: 'inline-script', unit, start: offset, end: offset + whole.length });
    }
    return whole.replace(/[^\r\n]/g, ' ');
  });
  for (const tag of scriptsRemoved.matchAll(/<[a-z][\w:-]*\b(?:[^>"']|"[^"]*"|'[^']*')*>/gi)) {
    for (const attr of handlerAttributes(tag[0])) {
      if (!attr.complete) throw new Error(`Incomplete pinned HTML handler at ${tag.index + attr.start}`);
      const start = tag.index + attr.start; const end = tag.index + attr.end;
      const unit = compiler.addUnit(decodeAttribute(attr.text), { name: `index.html:${attr.event}:${start}`, kind: 'html-handler', origin: { kind: 'html-attribute', file: 'index.html', start, end, event: attr.event } });
      pageHandlers.push({ event: attr.event, unit, start, end });
    }
  }
  // Literal fragments are retained even when a concatenation supplies the rest
  // of the handler. Runtime strings must be parsed by the eventual DOM host.
  for (const candidate of [...compiler.literalCandidates]) {
    for (const attr of handlerAttributes(candidate.text.replace(/<!--[\s\S]*?-->/g, comment => comment.replace(/[^\r\n]/g, ' ')))) {
      const metadata = { literalNode: candidate.node, event: attr.event, startInValue: attr.start, endInValue: attr.end, source: candidate.source, text: attr.text, status: 'fragment', unit: null, activation: 'Requires runtime HTML parsing; a complete literal may be inside a comment formed by concatenation.' };
      if (attr.complete) {
        try {
          metadata.unit = compiler.addUnit(decodeAttribute(attr.text), { name: `${compiler.units[candidate.unit].name}:literal-handler:${candidate.node}:${attr.start}`, kind: 'literal-handler', origin: { kind: 'string-literal-attribute', literalNode: candidate.node, startInValue: attr.start, endInValue: attr.end, event: attr.event } });
          metadata.status = 'compiled';
        } catch (error) {
          if (error.syntaxPhase !== 'parse') throw error;
          // Some native strings contain substitution tokens such as
          // ==CLOSETHIS()==. They are data, not executable handler source yet.
          metadata.status = 'template'; metadata.parseError = error.message;
        }
      }
      compiler.generatedHandlers.push(metadata);
    }
  }
  return compiler.result({ gameVersion: source.version, edition: 'steam', sourceHashes: source.hashes, pageScripts, pageHandlers,
    coverage: { pinnedFiles: Object.keys(source.hashes).length, sourceScripts: scriptUnits.size, generatedStringLimit: 'Complete handler bodies within one string literal are compiled as candidates, not asserted active. Concatenation can form HTML comments around them. Incomplete fragments remain in the executable expression AST and in fragment metadata; they are not replaced by guessed handlers.' } });
}

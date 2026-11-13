import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';

const catalogue = JSON.parse(readFileSync(new URL('../model/browser-host-catalogue.json', import.meta.url)));
const observed = { roots: catalogue.roots, objects: catalogue.objects, intrinsics: catalogue.intrinsics,
  elementTypes: catalogue.elementTypes, instances: catalogue.instances,
  referencedIdentities: catalogue.referencedIdentities, referencedSymbols: catalogue.referencedSymbols,
  descriptorTraversalGetterInvocations: catalogue.descriptorTraversalGetterInvocations,
  explicitInstanceAcquisitions: catalogue.explicitInstanceAcquisitions,
  nativeFunctionTextInspections: catalogue.nativeFunctionTextInspections };
assert.equal(createHash('sha256').update(JSON.stringify(observed)).digest('hex'), catalogue.descriptorSha256);
const str = value => {
  if (typeof value !== 'string' || /[^\x20-\x7e]/.test(value)) throw new Error('Catalogue label needs an explicit non-ASCII encoding');
  return JSON.stringify(value);
};
const nat = value => { assert(Number.isSafeInteger(value) && value >= 0); return String(value); };
const bool = value => { assert.equal(typeof value, 'boolean'); return String(value); };
const optional = value => value == null ? 'none' : `(some ${nat(value)})`;
const functions = new Map();
const addFunction = value => {
  if (!value) return;
  assert(value.sourceText.every(n=>Number.isInteger(n) && n>=0 && n<=65535));
  const normalized = { id: value.id, name: value.name, length: value.length, sourceText: value.sourceText };
  if (functions.has(value.id)) assert.deepEqual(functions.get(value.id), normalized);
  else functions.set(value.id, normalized);
};
const encodeValue = value => {
  switch (value.type) {
    case 'undefined': return '.undefined';
    case 'null': return '.null';
    case 'boolean': return `(.boolean ${bool(value.value)})`;
    case 'number': assert(BigInt(value.bits) >= 0n && BigInt(value.bits) < 2n ** 64n); return `(.number ${value.bits})`;
    case 'string': assert(value.units.every(n => Number.isInteger(n) && n >= 0 && n <= 65535)); return `(.string [${value.units.join(', ')}])`;
    case 'object': return `(.object ${nat(value.id)})`;
    case 'function': addFunction(value); return `(.function ${nat(value.id)})`;
    case 'symbol': return `(.symbol ${nat(value.id)} ${str(value.display)})`;
    default: throw new Error(`Unsupported native catalogue value ${value.type}`);
  }
};
const encodeProperty = property => {
  const key = property.key.type === 'string' ? `(.name ${str(property.key.name)})`
    : `(.symbol ${nat(property.key.id)} ${str(property.key.display)})`;
  let descriptor;
  if (property.kind === 'data') descriptor = `(.data ${encodeValue(property.value)} ${bool(property.writable)} ${bool(property.enumerable)} ${bool(property.configurable)})`;
  else {
    assert.equal(property.kind, 'accessor'); addFunction(property.getter); addFunction(property.setter);
    descriptor = `(.accessor ${optional(property.getter?.id)} ${optional(property.setter?.id)} ${bool(property.enumerable)} ${bool(property.configurable)})`;
  }
  return `  ⟨${key}, ${descriptor}⟩`;
};
const definitions = [];
const array = (name, type, rows) => {
  const names = [];
  for (let start = 0; start < rows.length; start += 80) {
    const chunkName = `${name}Chunk${names.length}`; names.push(chunkName);
    definitions.push(`private def ${chunkName} : Array ${type} := #[\n${rows.slice(start, start + 80).join(',\n')}\n]\n`);
  }
  definitions.push(`def ${name} : Array ${type} := ${names.length ? names.join(' ++ ') : '#[]'}\n`);
};
for (const object of catalogue.objects) {
  addFunction(object.callable);
  array(`properties${object.id}`, 'NativeProperty', object.properties.map(encodeProperty));
}
array('objects', 'NativeObject', catalogue.objects.map(object =>
  `  ⟨${nat(object.id)}, ${str(object.label)}, ${optional(object.prototype)}, ${optional(object.callable?.id)}, properties${object.id}⟩`));
array('callables', 'NativeCallable', [...functions.values()].sort((a, b) => a.id - b.id).map(value =>
  `  ⟨${nat(value.id)}, ${str(value.name)}, ${nat(value.length)}, [${value.sourceText.join(', ')}]⟩`));
array('roots', 'Root', catalogue.roots.map(root => `  ⟨${str(root.name)}, ${optional(Object.hasOwn(root, 'constructor') ? root.constructor : undefined)}, ${optional(root.prototype)}⟩`));
array('intrinsics', 'Intrinsic', catalogue.intrinsics.map(value => `  ⟨${str(value.name)}, ${nat(value.id)}, ${optional(value.prototype)}⟩`));
array('elementTypes', 'ElementType', catalogue.elementTypes.map(value => `  ⟨${str(value.tag)}, ${nat(value.constructor)}, ${nat(value.prototype)}⟩`));
array('instances', 'NativeInstance', catalogue.instances.map(value => `  ⟨${str(value.name)}, ${nat(value.id)}⟩`));
const header = `import CookieClicker.JavaScriptSyntax

/-! Generated observed browser descriptor data, not native operation semantics.
Source: model/browser-host-catalogue.json
Descriptor SHA-256: ${catalogue.descriptorSha256}
Reproduce with node tools/generate-browser-catalogue.mjs.
Uninspected identities and symbol semantics must remain explicit host requests.
-/
namespace CookieClicker.JavaScript.BrowserCatalogue

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

inductive PropertyKey where
  | name (value : String)
  | symbol (id : Nat) (display : String)
  deriving Repr, DecidableEq

inductive NativeValue where
  | undefined | null
  | boolean (value : Bool)
  | number (bits : UInt64)
  | string (value : JSString)
  | object (id : Nat)
  | function (id : Nat)
  | symbol (id : Nat) (display : String)
  deriving Repr, DecidableEq

inductive Descriptor where
  | data (value : NativeValue) (writable enumerable configurable : Bool)
  | accessor (getter setter : Option Nat) (enumerable configurable : Bool)
  deriving Repr, DecidableEq

structure NativeProperty where
  key : PropertyKey
  descriptor : Descriptor
  deriving Repr, DecidableEq

structure NativeObject where
  id : Nat
  label : String
  prototype : Option Nat
  callable : Option Nat
  properties : Array NativeProperty
  deriving Repr

structure NativeCallable where
  id : Nat
  name : String
  length : Nat
  sourceText : JSString
  deriving Repr, DecidableEq

structure Root where
  name : String
  constructorId : Option Nat
  prototype : Option Nat
  deriving Repr, DecidableEq

structure Intrinsic where
  name : String
  id : Nat
  prototype : Option Nat
  deriving Repr, DecidableEq

structure ElementType where
  tag : String
  constructorId : Nat
  prototype : Nat
  deriving Repr, DecidableEq

structure NativeInstance where
  name : String
  id : Nat
  deriving Repr, DecidableEq

def referencedIdentities : Nat := ${nat(catalogue.referencedIdentities)}
def referencedSymbols : Nat := ${nat(catalogue.referencedSymbols)}
def descriptorSha256 : String := ${str(catalogue.descriptorSha256)}

`;
const output = header + definitions.join('\n') + '\nend CookieClicker.JavaScript.BrowserCatalogue\n';
const target = new URL('../lean/CookieClicker/JavaScriptBrowserCatalogue.lean', import.meta.url);
if (process.argv.includes('--check')) assert.equal(readFileSync(target, 'utf8'), output, 'Generated browser catalogue is stale');
else writeFileSync(target, output);
console.log(JSON.stringify({ objects: catalogue.objects.length, callables: functions.size, roots: catalogue.roots.length,
  properties: catalogue.objects.reduce((sum, object) => sum + object.properties.length, 0), descriptorSha256: catalogue.descriptorSha256 }));

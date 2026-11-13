/** Function metadata and descriptor boundaries in the pinned V8 engine. */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { spawnSyncWithFileInput } from './process-input.mjs';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { runNativeEngine } from '../model/native-engine.mjs';

const cases = [];
const add = (name, source, expectedStatus) => cases.push({ name, source, expectedStatus });
add('declaration name and arity', 'function declared(a,b){};declared.name+":"+declared.length;');
add('named expression keeps explicit name', 'var f=function internal(a){};f.name+":"+f.length;');
add('variable initializer infers only metadata', 'var f=function(){return typeof f;};var g=f;f=3;g.name+":"+g();');
add('parenthesized anonymous initializer gets name', 'var f=(function(){});f.name;');
add('assignment to identifier infers name', 'var f;f=function(){};f.name;');
add('unbound identifier assignment infers name', 'unbound=function(){};unbound.name;');
add('property assignment does not infer a name', 'var o={};o.f=function(){};o.f.name;');
add('computed property assignment does not infer a name', 'var o={};o["f"]=function(){};o.f.name;');
add('sequence initializer does not infer a name', 'var f=(0,function(){});f.name;');
add('conditional initializer does not infer a name', 'var f=true?function(){}:function(){};f.name;');
add('logical initializer does not infer a name', 'var f=false||function(){};f.name;');
add('returned anonymous function has empty name', 'function factory(){return function(){};}factory().name;');
add('array anonymous element has empty name', '[function(){}][0].name;');
add('object literal key infers name', '({someKey:function(){}}).someKey.name;');
add('object literal string key retains UTF-16', '({"🍪":function(){}})["🍪"].name;');
add('numeric object key infers decimal spelling', '({12.5:function(){}})[12.5].name;');
add('named object function keeps explicit name', '({p:function inner(){}}).p.name;');
add('getter name and arity', 'var f=Object.getOwnPropertyDescriptor({get p(){return 1;}},"p").get;f.name+":"+f.length;');
add('setter name and arity', 'var f=Object.getOwnPropertyDescriptor({set p(x){}},"p").set;f.name+":"+f.length;');
add('getter has no own constructor prototype', 'var f=Object.getOwnPropertyDescriptor({get p(){return 1;}},"p").get;Object.getOwnPropertyNames(f).join(":");');
add('getter is not a constructor', 'var f=Object.getOwnPropertyDescriptor({get p(){return 1;}},"p").get;try{new f();}catch(e){e.name;}');
add('adding getter prototype cannot make it constructable', 'var f=Object.getOwnPropertyDescriptor({get p(){return 1;}},"p").get;f.prototype={};try{new f();}catch(e){e.name;}');
add('getter inherits restricted caller accessor', 'var f=Object.getOwnPropertyDescriptor({get p(){return 1;}},"p").get;try{f.caller;}catch(e){e.name;}');
add('inferred names are configurable readonly nonenumerable', 'var f=function(){};var d=Object.getOwnPropertyDescriptor(f,"name");d.value+":"+d.writable+":"+d.enumerable+":"+d.configurable;');
add('source length is configurable readonly nonenumerable', 'function f(a,b){};var d=Object.getOwnPropertyDescriptor(f,"length");d.value+":"+d.writable+":"+d.enumerable+":"+d.configurable;');
add('source length can be redefined', 'function f(a,b){};Object.defineProperty(f,"length",{value:7});f.length+"";');
add('source name delete exposes prototype name', 'function f(){};delete f.name;f.name;');
add('source name direct write is ignored', 'function f(){};f.name="other";f.name;');
add('strict name write throws', '"use strict";function f(){};try{f.name="other";}catch(e){e.name;}');
add('source function inherits call and apply', 'function f(a){return this.x+a;}f.call({x:3},4)+":"+f.apply({x:5},[6]);');
add('missing function property is known absent', 'function f(){};typeof f.notPresent;');
add('strict function own names exclude legacy fields', 'function f(){"use strict";}Object.getOwnPropertyNames(f).join(":");');
add('strict function caller read throws', 'function f(){"use strict";}try{f.caller;}catch(e){e.name;}');
add('strict function arguments read throws', 'function f(){"use strict";}try{f.arguments;}catch(e){e.name;}');
add('strict function caller assignment throws', 'function f(){"use strict";}try{f.caller=1;}catch(e){e.name;}');
add('strict function has no own caller descriptor', 'function f(){"use strict";}f.hasOwnProperty("caller")+":"+Object.getOwnPropertyDescriptor(f,"caller");');
add('strict function may shadow inherited caller', 'function f(){"use strict";}Object.defineProperty(f,"caller",{value:7});f.caller+"";');
add('strict function caller delete does not delete prototype property', 'function f(){"use strict";}var removed=delete f.caller;try{f.caller;}catch(e){removed+":"+e.name;}');
add('restricted getters and setters share identity', 'var a=Object.getOwnPropertyDescriptor(Function.prototype,"arguments"),c=Object.getOwnPropertyDescriptor(Function.prototype,"caller");(a.get===a.set)+":"+(a.get===c.get)+":"+(c.get===c.set);');
add('restricted intrinsic descriptors and extensibility', 'var f=Object.getOwnPropertyDescriptor(Function.prototype,"caller").get;var n=Object.getOwnPropertyDescriptor(f,"name"),l=Object.getOwnPropertyDescriptor(f,"length");n.value+":"+n.configurable+":"+l.value+":"+l.configurable+":"+Object.isExtensible(f);');
add('restricted intrinsic source text', 'Object.getOwnPropertyDescriptor(Function.prototype,"caller").get.toString();');
add('strict dynamic function shares source metadata rules', String.raw`var f=Function("a","\"use strict\";return a;");Object.getOwnPropertyNames(f).join(":")+":"+f.name+":"+f.call(null,3);`);
add('sloppy dynamic function call works without legacy reflection', 'var f=Function("a","return a+1;");f.call(null,3)+":"+f.apply(null,[4])+":"+typeof f.notPresent;');
for (const [name, expression] of [
  ['caller read', 'f.caller'], ['arguments read', 'f.arguments'],
  ['caller write', 'f.caller=7'], ['caller delete', 'delete f.caller'],
  ['arguments delete', 'delete f.arguments'], ['caller membership', '"caller" in f'],
  ['caller own test', 'f.hasOwnProperty("caller")'],
  ['caller descriptor', 'Object.getOwnPropertyDescriptor(f,"caller")'],
  ['caller redefinition', 'Object.defineProperty(f,"caller",{value:7})'],
  ['own enumeration', 'Object.getOwnPropertyNames(f)'],
]) add(`sloppy active reflection remains explicit: ${name}`, `function f(){};${expression};`, 'unresolved');

add('sloppy arguments callee is exact function', 'function f(a){return arguments.callee===f;}String(f(7));');
add('sloppy arguments callee descriptor and own order', 'function f(a){var d=Object.getOwnPropertyDescriptor(arguments,"callee");return (d.value===f)+":"+d.writable+":"+d.enumerable+":"+d.configurable+":"+Object.getOwnPropertyNames(arguments).join(",");}f(1);');
add('arguments callee supports anonymous recursion', 'var f=function(n){return n?arguments.callee(n-1)+1:0;};String(f(4));');
add('arguments callee keeps constructor identity', 'function C(){this.ok=arguments.callee===C;}String(new C().ok);');
add('arguments callee remains exact through call and apply', 'function f(){return arguments.callee===f;}f.call(null)+":"+f.apply({},[]);');
add('arguments callee survives unrelated function name change', 'function f(){return arguments.callee===f;}Object.defineProperty(f,"name",{value:"changed"});String(f());');
add('arguments callee may be written and deleted', 'function f(){arguments.callee=17;var a=arguments.callee,b=delete arguments.callee;return a+":"+b+":"+arguments.callee+":"+typeof f;}f();');
add('arguments callee does not join parameter map', 'function f(callee){arguments.callee=9;arguments[0]=7;return callee+":"+arguments.callee;}f(3);');
add('arguments callee can be redefined independently', 'function f(){Object.defineProperty(arguments,"callee",{value:23,writable:false});arguments.callee=7;return arguments.callee+":"+Object.keys(arguments).length;}f();');
add('arguments caller is absent in sloppy and strict functions', 'function f(){return arguments.caller+":"+arguments.hasOwnProperty("caller");}function g(){"use strict";return arguments.caller+":"+arguments.hasOwnProperty("caller");}f()+":"+g();');
add('strict arguments callee read throws', 'function f(){"use strict";try{arguments.callee;}catch(e){return e.name;}}f();');
add('strict arguments callee write throws', 'function f(){"use strict";try{arguments.callee=7;}catch(e){return e.name;}}f();');
add('strict arguments callee delete throws', 'function f(){"use strict";try{delete arguments.callee;}catch(e){return e.name;}}f();');
add('strict arguments callee descriptor retains captured poison', 'var poison=Object.getOwnPropertyDescriptor(Function.prototype,"caller").get;function f(a){"use strict";var d=Object.getOwnPropertyDescriptor(arguments,"callee");return (d.get===poison)+":"+(d.set===poison)+":"+d.enumerable+":"+d.configurable+":"+Object.getOwnPropertyNames(arguments).join(",");}f(1);');
add('strict arguments callee intrinsic is independent of mutable prototype', 'var poison=Object.getOwnPropertyDescriptor(Function.prototype,"caller").get;Object.defineProperty(Function.prototype,"caller",{value:17});function f(){"use strict";return Object.getOwnPropertyDescriptor(arguments,"callee").get===poison;}String(f());');
add('strict arguments callee getter throws on arbitrary receiver', 'function f(){"use strict";return Object.getOwnPropertyDescriptor(arguments,"callee").get;}try{f().call(17);}catch(e){e.name;}');
add('strict arguments callee cannot be changed to data descriptor', 'function f(){"use strict";try{Object.defineProperty(arguments,"callee",{value:7});}catch(e){return e.name;}}f();');
add('strict arguments poison persists after source function return', 'function f(){"use strict";return arguments;}var a=f();try{a.callee;}catch(e){e.name;}');
add('sloppy returned arguments retain original callee after rebinding', 'function f(){return arguments;}var old=f,a=f();f=17;String(a.callee===old);');
add('distinct source closures retain distinct callee identities', 'function make(){return function(){return arguments.callee;};}var a=make(),b=make();(a()===a)+":"+(b()===b)+":"+(a()===b());');
add('strict arguments poison getter remains nonconstructable', 'function f(){"use strict";return Object.getOwnPropertyDescriptor(arguments,"callee").get;}var g=f();try{new g();}catch(e){e.name;}');

const requests = cases.map(c => ({ ast: compileJavaScript(c.source, { name: c.name }), standardLibrary: true, fuel: 100000 }));
const result = spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck', import.meta.url)), ['--execute'], {
  input: JSON.stringify(requests), encoding: 'utf8', timeout: 60000, maxBuffer: 8 * 1024 * 1024,
});
assert.equal(result.status, 0, result.stderr || result.error?.message);
const actual = JSON.parse(result.stdout);
const comparable = cases.filter(c => !c.expectedStatus);
const expected = runNativeEngine('const vm=require("vm"),fs=require("fs");const input=JSON.parse(fs.readFileSync(0,"utf8"));process.stdout.write(JSON.stringify(input.map(c=>{const v=vm.runInNewContext(c.source);if(typeof v!=="string")throw Error(c.name);return Array.from({length:v.length},(_,i)=>v.charCodeAt(i));})));', comparable);
let index = 0;
for (let i = 0; i < cases.length; i++) {
  assert.equal(actual[i].status, cases[i].expectedStatus ?? 'complete', cases[i].name + ': ' + JSON.stringify(actual[i]));
  if (!cases[i].expectedStatus) assert.deepEqual(actual[i].value, { type: 'string', units: expected[index++] }, cases[i].name);
}
console.log(JSON.stringify({ functionMetadataCases: cases.length, nativeComparisons: comparable.length, activeSloppyReflectionVerified: false }));

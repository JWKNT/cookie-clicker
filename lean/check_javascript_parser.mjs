/** Finite direct-source parser checks; not a universal parser refinement proof. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript, compilePinnedGameAst } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { runNativeEngine } from '../model/native-engine.mjs';

if (!process.argv.includes('--engine')) throw new Error('Parser comparisons require the pinned native engine');
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index));
const cases = [];
const add = (name, source, extra = {}) => cases.push({ name, source, ...extra });
const source = loadGameSource();
const artifact = compilePinnedGameAst();
const decodeAttribute = text => text.replace(/&(#x[0-9a-f]+|#\d+|amp|quot|apos|lt|gt|nbsp);/gi, (_, entity) => {
  if (entity[0] === '#') {
    let point = entity[1].toLowerCase() === 'x' ? parseInt(entity.slice(2), 16) : Number(entity.slice(1));
    if (!point || point > 0x10ffff || (point >= 0xd800 && point <= 0xdfff)) point = 0xfffd;
    return String.fromCodePoint(point);
  }
  return { amp: '&', quot: '"', apos: "'", lt: '<', gt: '>', nbsp: '\u00a0' }[entity.toLowerCase()];
});
for (const unit of artifact.units) {
  let text;
  if (unit.origin.kind === 'pinned-file') text = source.sources[unit.origin.file];
  else if (unit.origin.kind === 'html-script') text = source.sources[unit.origin.file].slice(unit.origin.start, unit.origin.end);
  else if (unit.origin.kind === 'html-attribute') text = decodeAttribute(source.sources[unit.origin.file].slice(unit.origin.start, unit.origin.end));
  else if (unit.origin.kind === 'string-literal-attribute') {
    const literal = artifact.nodes[unit.origin.literalNode];
    const value = String.fromCharCode(...literal.units);
    text = decodeAttribute(value.slice(unit.origin.startInValue, unit.origin.endInValue));
  } else throw new Error(`Unknown source-unit origin ${JSON.stringify(unit.origin)}`);
  assert.equal(createHash('sha256').update(text).digest('hex'), unit.textSha256, `Exact source reconstruction: ${unit.name}`);
  add(unit.name, text, { kind: unit.kind, functionBody: unit.kind.endsWith('handler'), pinned: true });
}

for (const [name, text] of [
  ['precedence', '1+2*3<<1==14&&4|2;'],
  ['assignment associativity', 'var a=0,b=0,c=3;a=b=c+2;a*10+b;'],
  ['conditional assignment comma', 'var a=0,b=3;a=b?1:2,4;'],
  ['array holes trailing comma', 'var a=[,1,,];a.length*10+(0 in a?1:0);'],
  ['accessor function text', 'var x={get a(){return 3;},set a(v){this.b=v;}};Object.getOwnPropertyDescriptor(x,"a").get.toString();'],
  ['nested closure and declaration', 'function f(a){return function(b){return a+b;};}f(3)(4);'],
  ['strict directive', 'function f(a,b){"use strict";return this===undefined?a+b:0;}f(2,3);'],
  ['escaped non-directive', 'function f(){"use\\x20strict";return this!==undefined;}f();'],
  ['directive continuation', '"use strict"\n+"not a directive";'],
  ['strict label permits eval name', '"use strict";eval:while(false){break eval;}1;'],
  ['for loop', 'var s=0;for(var i=0;i<5;i++)s+=i;s;'],
  ['for-in', 'var s="";for(var x in {a:1,b:2})s+=x;s;'],
  ['for-in reference', 'var o={},s="";for(o.x in {a:1,b:2})s+=o.x;s;'],
  ['do while', 'var x=0;do{x++;}while(x<3);x;'],
  ['labels', 'var n=0;outer:for(var i=0;i<3;i++){for(var j=0;j<3;j++){if(j===1)continue outer;n++;}}n;'],
  ['try catch finally', 'var s="";try{throw 7;}catch(e){s+=e;}finally{s+="f";}s;'],
  ['return automatic semicolon', 'function f(){return\n/x/;}typeof f();'],
  ['postfix automatic semicolon', 'var x=1;x++\n(function(){x+=3;})();x;'],
  ['parenthesized postfix member', 'var x=1;(x++).toString()+":"+x;'],
  ['postfix binary', 'var a=1,b=2;a+++b;'],
  ['regexp slash character class', 'var r=/[\\/\\]]+/gi;r.source;'],
  ['division versus regexp', 'var x=12/3/2;/a/.test("a")+":"+x;'],
  ['regexp after return', 'function f(){return /x/g;}f().source;'],
  ['new member call', 'new Date(0).getTime();'],
  ['nested new', 'function F(){return Number;}new new F()(3).valueOf();'],
  ['comments and newlines', 'var x=1;/*a\nb*/x\n++x;x;'],
  ['HTML line comments', '<!-- hidden\nvar x=1;\n-->hidden\nx;'],
  ['identifier escape', 'var \\u0061=3;a;'],
  ['UTF16 strings', '"a\\uD800\\x00\\n\\t\\v\\b\\f\\r";'],
  ['string line continuation', '"a\\\r\nb";'],
  ['legacy string octal', '"\\377\\400\\08\\9";'],
  ['numeric literal forms', '[.5,1.,1e-2,0xff,077,08,08.5].join(":");'],
  ['non-ASCII whitespace after numeric', '1\u00a0+2;'],
  ['non-ASCII whitespace after regexp', '/x/g\u00a0.source;'],
  ['negative zero', '-0;'],
  ['numeric rounding boundary', '9007199254740993;'],
  ['numeric underflow', '2.4703282292062327e-324;'],
  ['numeric overflow', '1e309;'],
  ['function comment provenance', '(function /* a */ f(x){return x;}).toString();'],
  ['getter quoted name provenance', 'var o={get "x y"(){return 1;}};Object.getOwnPropertyDescriptor(o,"x y").get.toString();'],
]) add(name, text, { execute: true });

let seed = 0x4f52a19b;
const draw = n => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed % n; };
const binary = ['+','-','*','/','%','<<','>>','>>>','&','|','^','==','!=','===','!==','<','<=','>','>=','&&','||'];
const atoms = ['0','1','2','-3','0x11','0.25','true','false','null','"3"'];
for (let index = 0; index < 240; index += 1) {
  let text = atoms[draw(atoms.length)];
  for (let item = 0, count = 2 + draw(9); item < count; item += 1) text += ` ${binary[draw(binary.length)]} ${atoms[draw(atoms.length)]}`;
  add(`precedence generated ${index}`, `${text};`, { execute: true });
}
for (const text of [
  'var x=;', 'var x="a\nb";', '/* unterminated', '"unterminated', '0x;', '1e+;',
  'var if=1;', '\\u0069f(true){}', '++(1);', 'new !x;', 'x++();', 'x++[0];',
  'return 1;', 'throw\n1;', 'break;', 'continue;', 'a:{continue a;}', 'a:a:while(false){}',
  'function f(){"use strict";var eval=1;}', 'function f(a,a){"use strict";}',
  '"use strict";077;', '"use strict";"\\1";', 'function f(){"\\1";"use strict";}',
  '"use strict";delete x;', '"use strict";eval=1;', 'var x={get a(x){}};', 'try{}',
]) add(`invalid ${JSON.stringify(text)}`, text, { invalid: true });
for (const text of ['var π=1;π;', 'var \\u03c0=1;', 'var x=1n;', 'var x=0x1n;', 'var x=1_000;',
  'var x=`a`;', 'var f=(x)=>x;', 'let x=1;', 'class X{}', 'with({x:1}){x;}', 'switch(1){case 1:break;}']) {
  add(`unsupported ${JSON.stringify(text)}`, text, { unsupported: true });
}

const requests = cases.map(c => {
  let expectedAst;
  if (!c.invalid && !c.unsupported) expectedAst = compileJavaScript(c.source, { name: c.name, kind: c.kind || 'script' });
  return { sourceUnits: units(c.source), functionBody: !!c.functionBody, expectedAst, execute: !!c.execute };
});
const child = spawnSync(fileURLToPath(new URL('.lake/build/bin/jsparsercheck', import.meta.url)), [], {
  input: JSON.stringify(requests), encoding: 'utf8', timeout: 300000, maxBuffer: 32 * 1024 * 1024,
});
if (child.error) throw child.error;
assert.equal(child.status, 0, child.stderr);
const actual = JSON.parse(child.stdout);
const native = runNativeEngine(String.raw`const vm=require('vm');const input=JSON.parse(require('fs').readFileSync(0,'utf8'));
function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='number'){const b=Buffer.alloc(8);b.writeDoubleBE(v);return{type:'number',bits:b.readBigUInt64BE().toString()};}throw Error('Expected primitive result');}
const results=input.map(c=>{try{new vm.Script(c.functionBody?'function handler(event){\n'+c.source+'\n}':c.source);return{parsed:true,...(c.execute?{value:encode(vm.runInNewContext(c.source,{}, {timeout:1000}))}:{})};}catch(e){return{parsed:false,error:e.name,message:e.message};}});console.log(JSON.stringify({results,versions:process.versions}));`, cases);
const failures = [];
for (let index = 0; index < cases.length; index += 1) {
  const c = cases[index];
  try {
    if (c.invalid) {
      assert.equal(native.results[index].parsed, false, 'Invalid fixture must be rejected by native parser');
      assert.equal(actual[index].status, 'parse-error');
    } else if (c.unsupported) {
      assert.equal(native.results[index].parsed, true, 'Boundary fixture must be valid native syntax');
      assert.equal(actual[index].status, 'parse-error');
      assert.equal(actual[index].kind, 'CookieClicker.JavaScript.Lexer.ErrorKind.unsupported');
    } else {
      assert.equal(native.results[index].parsed, true);
      assert.equal(actual[index].status, 'parsed');
      assert.equal(actual[index].matchesReference, true);
      if (c.execute) assert.deepEqual(actual[index].execution, { status: 'complete', value: native.results[index].value });
    }
  } catch (error) { failures.push({ name: c.name, actual: actual[index], native: native.results[index], message: error.message }); }
}
if (failures.length) { console.error(JSON.stringify(failures, null, 2)); process.exitCode = 1; }
console.log(JSON.stringify({ cases: cases.length, passed: cases.length - failures.length,
  pinnedUnits: cases.filter(c => c.pinned).length, pinnedSourceFiles: 7,
  typedASTReference: 'Acorn 8.14.0, ES5 frontend v2', versions: native.versions,
  gameEntryPointExecuted: false, parserRefinementVerified: false }));

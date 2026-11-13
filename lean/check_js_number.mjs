import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { hasNativeEngine, inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

// Prefer the pinned game's engine: transcendental results can differ between
// V8 versions. The fallback is a host-compatibility check, not game refinement.
const buffer = new ArrayBuffer(8);
const view = new DataView(buffer);
const bits = value => { view.setFloat64(0, value); return view.getBigUint64(0).toString(); };
const value = raw => { view.setBigUint64(0, BigInt(raw)); return view.getFloat64(0); };
const normalized = raw => Number.isNaN(value(raw)) ? 'NaN' : raw;
const units = text => Array.from({length:text.length}, (_,i) => text.charCodeAt(i));

const binary = {
  add:(a,b)=>a+b,sub:(a,b)=>a-b,mul:(a,b)=>a*b,div:(a,b)=>a/b,rem:(a,b)=>a%b,
  min:Math.min,max:Math.max,and:(a,b)=>a&b,or:(a,b)=>a|b,xor:(a,b)=>a^b,
  shl:(a,b)=>a<<b,shr:(a,b)=>a>>b,ushr:(a,b)=>a>>>b,
  pow:(a,b)=>Math.pow(a,b),
  atan2:(a,b)=>Math.atan2(a,b),
};
const predicates={eq:(a,b)=>a===b,lt:(a,b)=>a<b,le:(a,b)=>a<=b,sameValue:Object.is,
  sameValueZero:(a,b)=>a===b||Number.isNaN(a)&&Number.isNaN(b)};
const unary={neg:a=>-a,abs:Math.abs,sqrt:Math.sqrt,log:Math.log,atan:Math.atan,sin:Math.sin,cos:Math.cos,floor:Math.floor,ceil:Math.ceil,trunc:Math.trunc,round:Math.round,not:a=>~a};
const unaryPredicates={isNaN:Number.isNaN,isFinite:Number.isFinite,isInteger:Number.isInteger,isSafeInteger:Number.isSafeInteger};
const cases=[];const expected=[];
const add=(input,output)=>{cases.push(input);expected.push(output);};
const boundary=[0,-0,NaN,Infinity,-Infinity,Number.MIN_VALUE,-Number.MIN_VALUE,Number.MAX_VALUE,-Number.MAX_VALUE,
  2**-1022,-(2**-1022),1,-1,0.5,-0.5,0.49999999999999994,-0.49999999999999994,0.5000000000000001,-0.5000000000000001,
  1.5,-1.5,2**31-1,2**31,2**32-1,2**32,2**53-1,2**53,2**53+2,2**90,2**90+2**38,2**90-2**37,
  0.01,0.1,1.15,1e-7,1e-6,1e20,1e21,1e23,1e72,64_436_018.95734597];
let rng=0x9e3779b9;
const next=()=>{rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0;};
const sampled=Array.from({length:384},()=>value((BigInt(next())<<32n|BigInt(next())).toString()));
const values=[...boundary,...sampled];
const angles=[0.3,0.4375,Math.PI/4,Math.PI/2,Math.PI,3*Math.PI/4,1.1875,2.4375,
  2**19*Math.PI/2,1e6,1e10,1e20,1e100,1e300];
for(let i=1;i<=64;i++)angles.push(i*Math.PI/2,i*12345.6789);
for(const angle of angles)for(const sign of [1,-1]){
  const raw=BigInt(bits(sign*angle));
  for(const offset of [-2n,-1n,0n,1n,2n]){
    const a=value((raw+offset).toString());
    for(const op of ['sin','cos','atan','log'])add({op,a:bits(a)},normalized(bits(Math[op](a))));
  }
}
for(const a of values){
  for(const [op,fn] of Object.entries(unary))add({op,a:bits(a)},normalized(bits(fn(a))));
  for(const [op,fn] of Object.entries(unaryPredicates))add({op,a:bits(a)},fn(a));
  add({op:'toInt32',a:bits(a)},String(a|0));add({op:'toUInt32',a:bits(a)},String(a>>>0));
  add({op:'toDecimal',a:bits(a)},units(String(a)));
  for(const parameter of [0,1,2,6,20,50,100])
    add({op:'toFixed',a:bits(a),parameter},units(a.toFixed(parameter)));
  for(const parameter of [1,2,3,6,17,20,50,100])
    add({op:'toPrecision',a:bits(a),parameter},units(a.toPrecision(parameter)));
  if(!Number.isFinite(a)||Number.isInteger(a))for(const parameter of [2,4,8,16,32])
    add({op:'toRadix',a:bits(a),parameter},units(a.toString(parameter)));
}
const pairs=[...boundary.flatMap(a=>boundary.map(b=>[a,b])),...sampled.map((a,i)=>[a,sampled[(i*37+11)%sampled.length]])];
// Native prices, prestige and maturity expressions use bases near one and
// noninteger exponents; uniform raw-bit sampling rarely exercises this range.
pairs.push(...[0.95,1.01,1.05,1.1,1.15,2,10,1e12,1e42,1e56,1e72,1e86].flatMap(a=>
  [1/3,0.1,0.2,0.5,0.8,1.5,3,4,5,10,100,450,700,1000,2**31,2**64].map(b=>[a,b])));
for(const [a,b] of pairs){
  for(const [op,fn] of Object.entries(binary))add({op,a:bits(a),b:bits(b)},normalized(bits(fn(a,b))));
  for(const [op,fn] of Object.entries(predicates))add({op,a:bits(a),b:bits(b)},fn(a,b));
}
const strings=['',' ','\ufeff\t','\u0085','\u180e','\ud800','\udc00','\ud83d\ude00',
  '0','-0','+0','+','-','.','1.','.1','1e','1e+','1e-2','1.25e+bad','12suffix',
  'Infinity','-Infinity','+Infinity','Infinityx','NaN','null','0x1','0x','+0xff','-0xff','0b11','0B101','0o77','0O77','0b2',
  '077','0_1','1_000','1e10000','-1e-10000','9007199254740993','1000000000000000100',
  '2.2250738585072011e-308','2.2250738585072012e-308','4.9406564584124654e-324','2.4703282292062327e-324',
  '1.7976931348623157e308','1.7976931348623159e308',...values.filter(Number.isFinite).map(String)];
for(const text of strings){
  add({op:'parseNumber',text:units(text)},normalized(bits(Number(text))));
  add({op:'parseFloat',text:units(text)},normalized(bits(parseFloat(text))));
  for(const radix of [0,2,4,8,10,16,32,1,37,Infinity,2**32+16])
    add({op:'parseInt',text:units(text),radix:bits(radix)},normalized(bits(parseInt(text,radix))));
}
// Native general-radix parseInt need not equal exact integer conversion.
// Preserve explicit regression cases: unsupported must not silently invent a result.
for(const radix of [3,5,7,11,23,36])
  add({op:'parseInt',text:units('19007199254740993'),radix:bits(radix)},'unresolved');
if(process.argv.includes('--engine') || hasNativeEngine()){
  const engine=inspectNativeEngine();
  const worker=`
    const fs=require('fs');const cases=JSON.parse(fs.readFileSync(0,'utf8'));
    const buffer=new ArrayBuffer(8),view=new DataView(buffer);
    const bits=${bits.toString()},value=${value.toString()},normalized=${normalized.toString()},units=${units.toString()};
    const binary={${Object.entries(binary).map(([k,f])=>`${k}:${['min','max'].includes(k)?`Math.${k}`:`(${f.toString()})`}`).join(',')}};
    const predicates={eq:(a,b)=>a===b,lt:(a,b)=>a<b,le:(a,b)=>a<=b,sameValue:Object.is,sameValueZero:(a,b)=>a===b||Number.isNaN(a)&&Number.isNaN(b)};
    const unary={neg:a=>-a,abs:Math.abs,sqrt:Math.sqrt,log:Math.log,atan:Math.atan,sin:Math.sin,cos:Math.cos,floor:Math.floor,ceil:Math.ceil,trunc:Math.trunc,round:Math.round,not:a=>~a};
    const unaryPredicates={isNaN:Number.isNaN,isFinite:Number.isFinite,isInteger:Number.isInteger,isSafeInteger:Number.isSafeInteger};
    const output=cases.map(c=>{
      if(c.text){const text=String.fromCharCode.apply(null,c.text);const r=c.op==='parseNumber'?Number(text):c.op==='parseFloat'?parseFloat(text):parseInt(text,value(c.radix));return normalized(bits(r));}
      const a=value(c.a),b=c.b===undefined?undefined:value(c.b);
      if(binary[c.op])return normalized(bits(binary[c.op](a,b)));
      if(predicates[c.op])return predicates[c.op](a,b);
      if(unary[c.op])return normalized(bits(unary[c.op](a)));
      if(unaryPredicates[c.op])return unaryPredicates[c.op](a);
      if(c.op==='toInt32')return String(a|0);if(c.op==='toUInt32')return String(a>>>0);
      if(c.op==='toDecimal')return units(String(a));
      return units(c.op==='toRadix'?a.toString(c.parameter):a[c.op](c.parameter));
    });process.stdout.write(JSON.stringify(output));`;
  const native=runNativeEngine(worker,cases);
  for(let i=0;i<cases.length;i++)if(expected[i]!=='unresolved')expected[i]=native[i];
  console.log(`Comparison engine: Electron ${engine.versions.electron}, V8 ${engine.versions.v8}, ${engine.arch}; game entry point not executed.`);
} else {
  console.log(`Pinned game engine unavailable; checking host compatibility with Node ${process.versions.node}, V8 ${process.versions.v8}.`);
}
const result=spawnSync(fileURLToPath(new URL('./.lake/build/bin/jsnumbercheck',import.meta.url)),[],
  {input:JSON.stringify(cases),encoding:'utf8',maxBuffer:64*1024*1024,timeout:300000});
assert.equal(result.status,0,result.stderr||result.error?.message);
const actual=JSON.parse(result.stdout);assert.equal(actual.length,expected.length);
for(let i=0;i<cases.length;i++){
  const op=cases[i].op;
  const comparable=actual[i]==='unresolved' ? actual[i] : Object.hasOwn(binary,op)||Object.hasOwn(unary,op)||op.startsWith('parse') ? normalized(actual[i]) : actual[i];
  assert.deepEqual(comparable,expected[i],JSON.stringify({input:cases[i],actual:actual[i],expected:expected[i]}));
}
console.log(`JavaScript Number comparisons passed ${cases.length} cases: signed zero, infinities, subnormals, rounding, remainder, bitwise conversion, decimal formatting and parsing. These are finite native comparisons, not a full source refinement proof.`);

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

const units=text=>Array.from({length:text.length},(_,i)=>text.charCodeAt(i));
const cases=[];
const texts=['','ABCxyz','éßİıſKﬃ','ΟΣ','ΟΣΑ','AΣ\u0301','AΣ\u0301B','A\u0301Σ','A\u0301Σ\u0301B',
  'Σ','1Σ','AΣ1','😀','\ud800A\udc00','𐐀𐐨','𝔄'];
const engine=process.argv.includes('--engine')?inspectNativeEngine():null;
if(engine){
  const points=new Set();
  const data=readFileSync(new URL('../model/unicode13/UnicodeData.txt',import.meta.url),'utf8');
  for(const line of data.split(/\r?\n/)){const row=line.split(';');if(row[12]||row[13])points.add(parseInt(row[0],16));}
  const special=readFileSync(new URL('../model/unicode13/SpecialCasing.txt',import.meta.url),'utf8');
  for(const line of special.split(/\r?\n/)){const value=line.split('#')[0].trim();if(value)points.add(parseInt(value,16));}
  for(const point of points)texts.push(String.fromCodePoint(point));
  cases.push({op:'properties'});
}
for(const text of texts)for(const op of ['lower','upper','points','legacy'])cases.push({op,text:units(text)});
const script=`const fs=require('fs');const cases=JSON.parse(fs.readFileSync(0,'utf8'));
  const units=${units.toString()};
  const letter=/\\p{Letter}/u,cased=/\\p{Cased}/u,ignorable=/\\p{Case_Ignorable}/u;
  const result=cases.map(c=>{
    if(c.op==='properties')return Array.from({length:0x110000},(_,p)=>{
      const s=String.fromCodePoint(p);return (letter.test(s)?1:0)+(cased.test(s)?2:0)+(ignorable.test(s)?4:0);
    });
    const text=String.fromCharCode.apply(null,c.text);
    if(c.op==='points')return Array.from(text,x=>x.codePointAt(0));
    if(c.op==='lower')return units(text.toLowerCase());
    if(c.op==='upper')return units(text.toUpperCase());
    return c.text.map(unit=>{const converted=String.fromCharCode(unit).toUpperCase();
      return converted.length!==1||unit>=128&&converted.charCodeAt(0)<128?unit:converted.charCodeAt(0);});
  });process.stdout.write(JSON.stringify(result));`;
let expected;
if(engine)expected=runNativeEngine(script,cases);
else{
  const result=spawnSync(process.execPath,['-e',script],{input:JSON.stringify(cases),encoding:'utf8',maxBuffer:32*1024*1024});
  assert.equal(result.status,0,result.stderr);expected=JSON.parse(result.stdout);
}
const result=spawnSync(fileURLToPath(new URL('./.lake/build/bin/jsunicodecheck',import.meta.url)),[],
  {input:JSON.stringify(cases),encoding:'utf8',maxBuffer:64*1024*1024,timeout:120000});
assert.equal(result.status,0,result.stderr||result.error?.message);
const actual=JSON.parse(result.stdout);assert.equal(actual.length,expected.length);
for(let i=0;i<cases.length;i++){
  if(cases[i].op==='properties'){
    assert.equal(actual[i].length,0x110000);
    for(let cp=0;cp<0x110000;cp++)assert.equal(actual[i][cp],expected[i][cp],`Unicode property U+${cp.toString(16)}`);
  }else assert.deepEqual(actual[i],expected[i],JSON.stringify(cases[i]));
}
console.log(JSON.stringify({unicode:'13.0.0',stringCases:cases.length-(engine?1:0),
  exhaustivePropertyCodepoints:engine?0x110000:0,comparisonEngine:engine,
  sourceRefinementProved:false}));

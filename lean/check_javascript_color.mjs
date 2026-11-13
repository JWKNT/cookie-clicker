/** Closed CSS color values compared with pinned Chromium87; no renderer oracle in Lean. */
import assert from 'node:assert/strict';
import{fileURLToPath}from'node:url';
import{spawnSyncWithFileInput as spawnSync}from'./process-input.mjs';
import{runNativeBrowser}from'../model/native-browser.mjs';
import{loadGameSource}from'../model/game-source.mjs';
if(!process.argv.includes('--engine'))throw new Error('Color comparisons require isolated pinned Chromium');
const cases=[],add=(source,expectedStatus)=>cases.push({source,...(expectedStatus?{expectedStatus}:{})});
for(let value=0;value<4096;value++)add('#'+value.toString(16).padStart(3,'0'));
for(let alpha=0;alpha<256;alpha++)for(const rgb of ['000000','123456','ffffff','ff0000','00ff7f'])add('#'+rgb+alpha.toString(16).padStart(2,'0'));
for(let value=0;value<65536;value+=61)add('#'+value.toString(16).padStart(4,'0'));
for(const color of ['transparent','black','white','red','lime','blue','yellow','aqua','cyan','fuchsia','magenta','gray','grey','silver','maroon','olive','green','purple','teal','navy'])for(const text of [color,color.toUpperCase(),' \t'+color+'\r\n'])add(text);
for(const name of ['rgb','rgba','RGB','RGBA'])for(const opacity of ['',',0',',1',',.1',',0.7',',0.500001',',-0.5',',3'])for(const channels of ['0,0,0','255,255,255','12,34,56','-12,999,0','50%,25%,0%','0.5,1.5,254.5','0.499999,1.500001,254.499999'])add(name+'('+channels+opacity+')');
for(let value=-20;value<=280;value++)add('rgb('+value+',17,31)');
for(let value=0;value<=100;value++)add('rgb('+value+'%,0%,0%)');
for(let digit=0;digit<10;digit++)for(const alpha of ['.'+digit,'0.'+digit,'0.'+digit+'00000'])add('rgba(21,43,65,'+alpha+')');
for(const source of ['', '#','#12','#12345','#1234567','#123456789','#ggg','rgb(1,2)','rgb(1,2,3,4,5)','rgb(1,,3)','rgb(foo,2,3)','rgb(1,2,3,.)'])add(source);
for(const source of ['hsl(0,100%,50%)','currentColor','rebeccapurple','rgb(1 2 3)','rgb(1,2,3','rgb(1e2,2,3)','rgb(+1,2,3)','rgb(1,2,3,50%)','rgb(1%,2,3)','rgb(1,2,3,.1234567)','rgb(1/*x*/,2,3)','\\72 ed'])add(source,'unresolved');
const market=loadGameSource().sources['minigameMarket.js'];
const palette=market.slice(market.indexOf('M.colBases=['),market.indexOf('M.setCols=function'));
for(const match of palette.matchAll(/'#[0-9a-f]+'/g))add(match[0].slice(1,-1));
const worker=function(cases){var c=document.createElement('canvas').getContext('2d'),s=document.createElement('div').style;return cases.map(function(test){if(test.expectedStatus)return{status:test.expectedStatus};s.color='';s.color=test.source;if(!s.color)return{status:'invalid'};c.fillStyle='#010203';c.fillStyle=test.source;var value=c.fillStyle,rgba;if(value[0]==='#')rgba=[parseInt(value.slice(1,3),16),parseInt(value.slice(3,5),16),parseInt(value.slice(5,7),16),255];else{var p=value.slice(5,-1).split(',').map(Number);rgba=[p[0],p[1],p[2],Math.round(p[3]*255)];}return{status:'complete',rgba:rgba,css:s.color,canvas:value};});};
const native=runNativeBrowser(worker.toString(),cases);
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(cases.map(c=>({operation:'color',source:c.source}))),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual(observed[i],native.result[i]);}catch(error){failures.push({source:cases[i].source,observed:observed[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures.slice(0,50),null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,failures:failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,fullColorGrammarVerified:false,rendererRefinementVerified:false}));

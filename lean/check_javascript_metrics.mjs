/** Source-derived integral box metrics, not a full renderer refinement proof. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript,numberLiteralBits} from '../model/javascript-ast.mjs';
import {compileCss} from '../model/css-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Metric comparisons require isolated pinned Chromium');
const cases=[],add=(name,source,extra={})=>cases.push({name,source,...extra});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const base='html,body,div,span{margin:0;padding:0;border:0}html,body{width:100%;height:100%}body{overflow:hidden}#parent{position:absolute;left:10px;top:20px;width:400px;height:300px}#target{position:absolute;left:7px;top:11px;width:130px;height:90px}';
const markup='<div id="parent"><div id="target"></div></div>';
const prefix='var target=document.getElementById("target"),parent=document.getElementById("parent");';
const names=['offsetWidth','offsetHeight','clientWidth','clientHeight'];
for(const css of ['', '#target{left:-13px;top:-17px}', '#target{width:0;height:0}', '#target{width:1px;height:2px}',
  '#target{width:100%;height:100%}', '#target{left:13px;right:17px;top:19px;bottom:23px;width:auto;height:auto}',
  '#target{position:fixed;left:7px;top:9px;width:61px;height:73px}', '#target{box-sizing:border-box}',
  '#target{visibility:hidden}', '#target{display:none}', '#parent{display:none}', '#target{overflow:hidden}',
  '#target{overflow:visible}', '#target{margin:0 0;padding:0px;border-width:0;border-style:solid}',
  '#target{width:271px!important}#parent #target{width:19px}', '#target{width:11px}#target{width:21px}']){
  add(`integral native dimensions ${css}`,`[target.offsetWidth,target.offsetHeight,target.clientWidth,target.clientHeight].join(',');`,{css});
}
for(const name of names){
  add(`body ${name}`,`document.body.${name};`);
  add(`detached div ${name}`,`document.createElement('div').${name};`);
  add(`detached canvas ${name}`,`document.createElement('canvas').${name};`);
  const proto=name.startsWith('offset')?'HTMLElement':'Element';
  add(`${name} wrong receiver`,`try{Object.getOwnPropertyDescriptor(${proto}.prototype,'${name}').get.call({});}catch(e){e.name;}`);
  add(`${name} Text receiver`,`try{Object.getOwnPropertyDescriptor(${proto}.prototype,'${name}').get.call(document.createTextNode('x'));}catch(e){e.name;}`);
  add(`${name} captured getter and ignored argument`,`var saved=Object.getOwnPropertyDescriptor(${proto}.prototype,'${name}').get;var Original=${proto};${proto}=function(){};var result=saved.call(target,{toString:function(){throw 'wrong';}});${proto}=Original;result;`);
  add(`quirks ${name} remains explicit`,`target.${name};`,{doctype:false,expectedStatus:'unresolved'});
}
for(const name of ['offsetWidth','offsetHeight'])for(const css of ['', 'html{width:600px;height:500px}', 'html{display:none}'])add(`root ${name} ${css}`,`document.documentElement.${name};`,{css});
for(const name of ['clientWidth','clientHeight'])add(`root ${name} scrollbar state remains explicit`,`document.documentElement.${name};`,{expectedStatus:'unresolved'});
for(const css of ['#target{width:1.5px}', '#target{padding:1px}', '#target{border:1px solid}', '#target{margin:1px}',
  '#target{overflow:auto}', '#target{overflow:scroll}', '#target{overflow:hidden visible}', '#target{transform:scale(2)}',
  '#target{zoom:2}', '#target{display:inline}', '#target{display:contents}', '#target{position:relative}',
  '#target{writing-mode:vertical-rl}', '#target{animation-name:pulse}'])add(`metric width fragment ${css}`,`target.offsetWidth;`,{css,...(['#target{padding:1px}','#target{border:1px solid}','#target{margin:1px}','#target{position:relative}'].includes(css)?{}:{expectedStatus:'unresolved'})});
add('live class cascade changes dimensions',`target.classList.add('wide');target.offsetWidth;`,{css:'.wide{width:231px!important}'});
add('live inline dimensions override source rule',`target.style.width='207px';target.offsetWidth;`);
add('source callback before metric lookup executes normally',`function getTarget(){target.style.height='117px';return target;}getTarget().clientHeight;`);
const main=loadGameSource().sources['main.js'],start=main.indexOf('var triggerAnim=function(element,anim)'),end=main.indexOf('};',start)+2;
assert(start>=0&&end>start);const trigger=main.slice(start,end);
for(const present of [false,true])add(`actual triggerAnim source present=${present}`,`${trigger};${present?"target.classList.add('pulse');":''}triggerAnim(target,'pulse');target.classList.contains('pulse')+':'+target.offsetWidth;`,{sourceFixture:true});
add('actual triggerAnim null source path',`${trigger};triggerAnim(null,'pulse');target.offsetWidth;`,{sourceFixture:true});
const promptStatement=main.split('\n').find(line=>line.includes('Game.promptAnchorL.style.top=Math.floor'));
assert.ok(promptStatement);
add('actual hidden UpdatePrompt source ignores unneeded border layout',`var Game={promptAnchorL:parent,promptWrapL:target,windowH:innerHeight};${promptStatement};parent.style.top;`,
 {css:'#parent{display:none}#target{border:4px ridge #ddd;padding:16px;height:auto}',sourceFixture:true});
const backgroundStatements=main.split('\n').filter(line=>line.includes('canvas.height=')&&line.includes('canvas.parentNode.offsetHeight')).slice(0,2);
assert.equal(backgroundStatements.length,2);
for(const statement of backgroundStatements)add('actual DrawBackground canvas height source '+statement.trim(),
 `var canvas=document.createElement('canvas');target.appendChild(canvas);var Game={Background:{canvas:canvas},LeftBackground:{canvas:canvas}};${statement};canvas.height;`,
 {css:'#target{top:0;bottom:0;height:auto;min-width:100px;width:30%}',sourceFixture:true});
for(const css of ['#target{padding-top:7px;padding-bottom:11px}','#target{border-style:solid;border-width:3px 2px}',
 '#target{height:5px;box-sizing:border-box;padding:9px}','#target{top:0;bottom:0;height:auto;min-height:400px}',
 '#target{width:33.3%;min-width:100px}'])add('independent vertical metric '+css,
 '[target.offsetHeight,target.clientHeight].join(",");',{css});
const worker=function(input){function encode(v){if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};throw Error('Expected primitive result');}
return{viewport:[innerWidth,innerHeight],values:input.cases.map(function(c){if(c.expectedStatus)return{status:c.expectedStatus};document.documentElement.innerHTML='<head><style>'+input.base+(c.css||'')+'</style></head><body>'+input.markup+'</body>';try{return{status:'complete',value:encode((function(){return eval(input.prefix+c.source);})())};}catch(e){return{status:'throw',name:e.name,message:e.message};}})};};
const native=runNativeBrowser(worker.toString(),{cases,base,markup,prefix},{allowEval:true,allowInlineStyles:true});
const requests=cases.map(c=>({browserLibrary:true,fuel:300000,ast:compileJavaScript(prefix+c.source,{name:c.name}),
  initialHtmlUnits:units((c.doctype===false?'':'<!doctype html>')+'<html><head><link rel="stylesheet" href="metrics.css"></head><body>'+markup+'</body></html>'),
  loadedStylesheets:[compileCss(base+(c.css??''),{name:'metrics.css'})],fixtureWindowData:['innerWidth','innerHeight'].map((name,i)=>({name,value:{kind:'number',bits:numberLiteralBits(native.result.viewport[i])}}))}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result.values[i]);}catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result.values[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,sourceFixtures:cases.filter(c=>c.sourceFixture).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,rendererRefinementVerified:false}));

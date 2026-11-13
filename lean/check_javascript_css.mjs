/** Source CSS parsing, selector/cascade and integral positioned-box comparisons.
 * These finite checks do not prove Chromium renderer refinement. */
import assert from 'node:assert/strict';
import {runInNewContext} from 'node:vm';
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileCss,compilePinnedStylesheets} from '../model/css-ast.mjs';
import {compileJavaScript,numberLiteralBits} from '../model/javascript-ast.mjs';
import {defaultGameSourceDirectory,loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw new Error('CSS comparisons require the pinned isolated native Chromium worker');

function tree(){return [
  {tag:'html',attributes:[],parent:null,previous:null,children:[1,2],hasText:false,documentRoot:true},
  {tag:'head',attributes:[],parent:0,previous:null,children:[],hasText:false,documentRoot:false},
  {tag:'body',attributes:[],parent:0,previous:1,children:[3],hasText:false,documentRoot:false},
  {tag:'div',attributes:[['id','wrapper'],['class','onWeb alpha']],parent:2,previous:null,children:[4,5,6],hasText:false,documentRoot:false},
  {tag:'div',attributes:[['id','game'],['class','beta gamma'],['title','Abc def-ghi']],parent:3,previous:null,children:[],hasText:false,documentRoot:false},
  {tag:'span',attributes:[['id','other'],['class','beta']],parent:3,previous:4,children:[],hasText:true,documentRoot:false},
  {tag:'div',attributes:[['id','last']],parent:3,previous:5,children:[],hasText:false,documentRoot:false},
];}
const cases=[];function add(name,operation,css,target=4,extra={}){cases.push({name,operation,css:[css],target,tree:tree(),inline:Array(7).fill(''),...extra});}
for(const target of [0,2,3,4,5,6])for(const selector of ['*','div','html','body','span','#game','.beta','.gamma','.beta.gamma',
  '#wrapper #game','#wrapper > #game','body > #game','body #game','#game + span','#game ~ div','span + div','span ~ #game',
  ':root',':first-child',':last-child',':only-child',':empty',':nth-child(1)',':nth-child(2)',':nth-child(odd)',':nth-child(even)',
  ':not(.beta)',':not(#game)','[id]','[id="game"]','[class~="beta"]','[title^="Abc"]','[title$="ghi"]','[title*="def"]',
  '[title|="Abc def"]','[title="abc DEF-GHI" i]','div::before'])add(`selector ${selector} target ${target}`,'match',`${selector}{left:0}`,target,{selector});
add('irrelevant dynamic pseudo class is disproved by ID','match','#missing:hover{left:1px}',4,{selector:'#missing:hover'});
add('matching dynamic pseudo class remains explicit','match','#game:hover{left:1px}',4,{expectedStatus:'unresolved'});
add('enumerated attribute case table remains explicit','match','[type=text]{left:1px}',4,{expectedStatus:'unresolved',tree:tree().map((n,i)=>i===4?{...n,attributes:[...n.attributes,['type','text']]}:n)});
const reset='html,body,div,span{margin:0;padding:0;border:0}html,body{width:100%;height:100%}body{overflow:hidden}';
const positioned='#wrapper{position:absolute;left:0;top:0;right:0;bottom:0;width:100%;height:100%}#game{position:absolute;left:0;top:0;right:0;bottom:0}';
const base=reset+positioned;
const dynamicStyle=(text,first=false)=>`var style=document.createElement("style");style.type="text/css";style.innerHTML=${JSON.stringify(text)};document.head.${first?'insertBefore(style,document.head.firstChild)':'appendChild(style)'};`;
for(const extra of ['', '#game{top:32px}', '.onWeb #game{top:32px}', '.offWeb #game{top:99px}',
  '#wrapper{left:10px;top:20px;width:300px;height:200px}#game{left:7px;top:11px;right:13px;bottom:17px}',
  '#game{left:auto;top:auto;right:11px;bottom:13px;width:100px;height:70px}',
  '#game{left:20px;top:30px;right:2px;bottom:3px;width:80px;height:90px}',
  '#game{left:-10px;top:-20px;width:100%;height:100%}',
  '#game{left:900px;top:700px}', '#game{display:none}', '#wrapper{display:none}',
  '#game{position:fixed;left:7px;top:9px;width:40px;height:50px}',
  '#game{top:10px!important}#wrapper #game{top:20px}',
  '#game{top:10px}#game{top:20px}#wrapper #game{top:30px}',
  '#game{margin:0px 0px;padding:0px 0px 0px 0px;border-style:solid;border-width:0}',
  '#game{box-sizing:border-box;width:100px;height:40px}'])add(`integral layout ${extra}`,'layout',base+extra);
add('inline normal wins selector specificity','layout',base+'#wrapper #game{top:10px}',4,{inline:['','','','','top:41px','','']});
add('author important beats inline normal','layout',base+'#game{top:10px!important}',4,{inline:['','','','','top:41px','','']});
add('inline important wins author important','layout',base+'#wrapper #game{top:10px!important}',4,{inline:['','','','','top:41px!important','','']});
add('source stylesheet order decides equal specificity','layout',base+'#game{top:11px}',4,{css:[base+'#game{top:11px}','#game{top:23px}']});
for(const extra of ['#game{top:1.5px}','#game{width:50%}','#game{transform:translateX(1px)}','#game{padding:1px}',
  '#game{margin:auto}','#game{position:relative}','#game{overflow:scroll}','#game{animation-name:move}',
  '#game:hover{top:32px}','#game{border:1px solid}', '#game{height:calc(100% - 1px)}',
  '#game{margin-inline-start:10px}', '#wrapper{will-change:transform}', '#game{all:initial}', '#game{inline-size:100px}',
  'body{float:right;width:100px}', '#wrapper{columns:2}', '#game{overflow:hidden visible}', '#game{border-inline-start-style:solid}'])add(`unresolved layout ${extra}`,'layout',base+extra,4,{expectedStatus:'unresolved'});
for(const hoverValue of ['hidden','visible'])for(const nativeHover of [false,true]){
  for(const targetSelector of ['#game','#wrapper'])add(`paired overflow ${targetSelector} ${hoverValue} materialized hover=${nativeHover}`,
    'layout',base+`${targetSelector}{overflow:hidden}${targetSelector}:hover{overflow:${hoverValue}}`,4,{nativeHover});
}
add('paired overflow selector-list ranking remains immaterial','layout',base+'#game{overflow:hidden}#game:hover,.beta{overflow:visible!important}');
add('paired overflow inline priority remains immaterial','layout',base+'#game:hover{overflow:visible!important}',4,{inline:['','','','','overflow:hidden!important','',''],browserExpectedStatus:'unresolved'});
for(const text of ['#game:hover{overflow:auto}','#game:hover{overflow:hidden visible}','#game:hover{overflow:inherit}',
  '#game:hover{overflow:visible}#game{overflow-x:hidden}', '#game:hover{overflow:visible;top:37px}',
  '#game:hover{overflow:visible;display:none}', '#wrapper:hover{overflow:visible;transform:scale(2)}']){
  add(`dynamic overflow projection rejected ${text}`,'layout',base+text,4,{expectedStatus:'unresolved'});
}
for(const extra of ['#game{border:1px solid red;padding:2em;transform:scale(2);width:auto}',
 '#game:hover{display:block}', '#game{all:initial}', '#game{border:4px ridge #ddd;height:auto}'])
 add(`hidden ancestor omits unrelated geometry ${extra}`,'layout',base+'#wrapper{display:none}'+extra);
add('hidden ancestor omits unsupported descendant inline declaration','layout',base+'#wrapper{display:none}',4,{inline:['','','','','border:1px solid red','','']});
add('hidden ancestor omits descendant transform geometry','layout',base+'#wrapper{display:none}',4,{inline:['','','','','transform:scale(2)','','']});
add('hidden box needs no viewport dimensions','layout',base+'#wrapper{display:none}',4,{omitViewport:true});
add('all reset prevents an unsupported hidden inference','layout',base+'#wrapper{display:none;all:initial}',4,{expectedStatus:'unresolved'});
add('unknown dynamic display prevents hidden inference','layout',base+'#wrapper{display:none}#wrapper:hover{display:block}',4,{expectedStatus:'unresolved'});
add('default body margin is not silently erased','layout',positioned,4,{expectedStatus:'unresolved'});
for(const extra of ['', '#game{width:0;height:0}', '#game{display:none}', '#wrapper{display:none}',
  '#game{visibility:hidden}', '#wrapper{visibility:hidden}', '#wrapper{visibility:hidden}#game{visibility:visible}',
  '#wrapper{visibility:hidden}#game{visibility:initial}', '#wrapper{visibility:hidden}#game{visibility:unset}',
  '#game{visibility:collapse}'])add(`focus style ${extra}`,'focus',base+extra);
add('CSS editable focus behavior remains explicit','focus',base+'#wrapper{-webkit-user-modify:read-write}',4,{expectedStatus:'unresolved'});
for(const extra of ['', '#game{border:32px solid transparent;height:auto;padding:2em}',
 '#game:hover{border:32px solid transparent;height:auto}', '#wrapper{-webkit-user-modify:read-write}',
 '#game{-webkit-user-modify:read-write-plaintext-only}',
 '#wrapper{-webkit-user-modify:read-write}#game{-webkit-user-modify:read-only}',
 '#wrapper{-webkit-user-modify:read-write}#game{-webkit-user-modify:initial}',
 '#wrapper{-webkit-user-modify:read-write}#game{-webkit-user-modify:unset}',
 '#wrapper{-webkit-user-modify:read-write}#game{-webkit-user-modify:inherit}',
 '#game{-webkit-user-modify:read-write!important}#wrapper #game{-webkit-user-modify:read-only}',
 '#wrapper{-webkit-user-modify:read-write-plaintext-only}#game{-webkit-user-modify:read-only!important}'])
 add(`editing-only cascade ${extra}`,'editing',base+extra);
for(const extra of ['#game{all:initial}', '#game:hover{-webkit-user-modify:read-write}',
 '#game{-webkit-user-modify:revert}', '#game{-webkit-user-modify:unsupported}'])
 add(`editing-only explicit boundary ${extra}`,'editing',base+extra,4,{expectedStatus:'unresolved'});
add('editing-only inline value wins selector specificity','editing',base+'#wrapper #game{-webkit-user-modify:read-write}',4,
 {inline:['','','','','-webkit-user-modify:read-only','','']});
const pinned=compilePinnedStylesheets().reverse(),directory=defaultGameSourceDirectory();
for(const mode of ['onWeb','offWeb'])for(const target of [0,2,3,4]){
  const t=tree();t[3].attributes[1][1]=mode;
  add(`pinned source ${mode} target ${target}`,'layout','',target,{tree:t,css:pinned.map(s=>readFileSync(new URL(s.name,`file://${directory}/`),'utf8')),compiled:pinned});
}
{
 const promptTree=tree();promptTree[3].children=[4];promptTree[4]={...promptTree[4],attributes:[['id','promptAnchor']],children:[5]};
 promptTree[5]={...promptTree[5],tag:'div',attributes:[['id','prompt'],['class','framed']],parent:4,previous:null,children:[6]};
 promptTree[6]={...promptTree[6],attributes:[['id','promptContent']],parent:5,previous:null,children:[]};
 add('pinned hidden prompt has no renderer box','layout','',5,{tree:promptTree,css:pinned.map(s=>readFileSync(new URL(s.name,`file://${directory}/`),'utf8')),compiled:pinned});
 add('pinned framed prompt has read-only editing style','editing','',5,{tree:promptTree,css:pinned.map(s=>readFileSync(new URL(s.name,`file://${directory}/`),'utf8')),compiled:pinned});
}
const main=loadGameSource().sources['main.js'];
const launchStyleStart=main.indexOf("\tvar css=document.createElement('style');",main.indexOf('Game.Launch=function()'));
const launchStyleEnd=main.indexOf('document.head.appendChild(css);',launchStyleStart)+'document.head.appendChild(css);'.length;
assert(launchStyleStart>0&&launchStyleEnd>launchStyleStart);const launchStyle=main.slice(launchStyleStart,launchStyleEnd);
for(const dynamicScript of [dynamicStyle('#game{top:31px}'),dynamicStyle('/*c*/body .beta,#game.gamma{top:43px!important}'),
  dynamicStyle('#game{background-image:url(a}b;c.png);top:37px}'),dynamicStyle('#game{top:7px;TOP:29px ! IMPORTANT}'),
  dynamicStyle('#game{top:71px}',true),dynamicStyle('#game{top:13px}')+'style.textContent="#game{top:17px}";',
  `var Game={resPath:"",version:2.053};${launchStyle}`,`var Game={resPath:"https://example.invalid/",version:2.053};${launchStyle}`]){
  add(`runtime CSS ${dynamicScript}`,'layout',base+'#game{top:9px}',4,{dynamicScript,browserOnly:true});
}
const pantheonSource=loadGameSource().sources['minigamePantheon.js'];
const pantheonStyleStart=pantheonSource.indexOf("str+='<style>'+"),pantheonStyleEnd=pantheonSource.indexOf("'</style>';",pantheonStyleStart)+"'</style>';".length;
assert(pantheonStyleStart>=0&&pantheonStyleEnd>pantheonStyleStart);
const pantheonStyle=runInNewContext("var Game={resPath:''};var str='';"+pantheonSource.slice(pantheonStyleStart,pantheonStyleEnd)+"str;",{},{timeout:1000}).slice(7,-8);
for(const text of [pantheonStyle,'#game{opacity:0.8;color:rgba(255,255,255,.75);background:linear-gradient(to top,rgba(0,0,0,.1),rgba(0,0,0,0))}',
  '.absent:hover,.absent:active{top:1.5px;animation-duration:.8s}', '#game{top:+2e1px}', '#game{top:2.0e1px}',
  '.absent{opacity:.5;transition:color 1e-1s}','#game{background-image:url("a;b}c.png");top:23px}',
  '#game{unsupported:f(";}",g([x;y]));top:19px}', '#game::before{color:rgba(0,0,0,.5)}']){
  add(`runtime component CSS ${text}`,'layout',base+'#game{top:9px}',4,{dynamicScript:dynamicStyle(text),browserOnly:true,...(text.includes('top:+2e1px')||text.includes('top:2.0e1px')?{expectedStatus:'unresolved'}:{})});
}
for(const text of ['#game{opacity:.5;transition:color 1e-1s}','#game:hover{top:32px}','@media screen{#game{top:32px}}','#game{top:1.5px}',String.raw`#ga\6de{top:32px}`]){
  add(`unsupported runtime CSS ${text}`,'layout',base,4,{dynamicScript:dynamicStyle(text),browserOnly:true,expectedStatus:'unresolved'});
}
const nativeWorker=function(cases){
  return {viewport:[innerWidth,innerHeight],values:cases.map(c=>{
    if(c.expectedStatus)return{status:c.expectedStatus};
    document.adoptedStyleSheets=[];document.head.textContent='';document.body.textContent='';
    const nodes=c.tree.map((n,i)=>i===0?document.documentElement:i===1?document.head:i===2?document.body:document.createElement(n.tag));
    nodes.forEach((node,i)=>{Array.from(node.attributes).forEach(a=>node.removeAttribute(a.name));for(const [name,value]of c.tree[i].attributes)node.setAttribute(name,value);if(c.inline[i])node.setAttribute('style',c.inline[i]);if(c.tree[i].hasText)node.appendChild(document.createTextNode('x'));});
    for(let i=3;i<nodes.length;i++)nodes[c.tree[i].parent].appendChild(nodes[i]);
    // Materialize both Boolean branches only for finite comparison fixtures.
    // This is not a pointer-state input to the Lean model.
    const auditMaterializedStyleSheets=c.css.map(text=>typeof c.nativeHover==='boolean'?text.replace(/:hover/g,c.nativeHover?':not(.never-hover-fixture)':'.never-hover-fixture'):text);
    document.adoptedStyleSheets=auditMaterializedStyleSheets.map(text=>{const sheet=new CSSStyleSheet();sheet.replaceSync(text);return sheet;});
    if(c.dynamicScript){
      // Styles in this fixture must use DOM order relative to external sheets,
      // so replace adopted sheets with real inert-source style elements.
      document.adoptedStyleSheets=[];
      for(const text of c.css){const style=document.createElement('style');style.textContent=text;document.head.appendChild(style);}
      eval(c.dynamicScript);
    }
    if(c.operation==='match')return{status:'matched',results:[{status:nodes[c.target].matches(c.selector)?'yes':'no'}]};
    if(c.operation==='focus'){nodes[c.target].tabIndex=0;nodes[c.target].focus({preventScroll:true});return{status:'complete',value:document.activeElement===nodes[c.target]};}
    if(c.operation==='editing')return{status:'complete',value:getComputedStyle(nodes[c.target]).webkitUserModify==='read-only'};
    const r=nodes[c.target].getBoundingClientRect();return{status:'complete',box:[r.x,r.y,r.width,r.height]};
  })};
};
const native=runNativeBrowser(nativeWorker.toString(),cases,{allowInlineStyles:true,allowEval:true});
const pureCases=cases.filter(c=>!c.browserOnly);
const requests=pureCases.map(c=>({operation:c.operation,stylesheets:c.compiled??c.css.map((text,i)=>compileCss(text,{name:`${c.name}-${i}`})),
  tree:c.tree,target:c.target,viewport:native.result.viewport,inline:c.inline.map(text=>compileCss(`a{${text}}`))}));
requests.unshift({operation:'decode',stylesheets:pinned});
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout);assert.deepEqual(observed.shift(),{status:'decoded',sheets:2,rules:527});
const failures=[];for(let i=0;i<pureCases.length;i++)try{
  if(cases[i].expectedStatus){const status=cases[i].operation==='match'?observed[i].results[0].status:observed[i].status;assert.equal(status,cases[i].expectedStatus);}
  else assert.deepEqual(observed[i],native.result.values[i]);
}catch(error){failures.push({name:cases[i].name,observed:observed[i],expected:native.result.values[i],error:error.message});}
const browserCases=cases.map((c,index)=>({...c,index})).filter(c=>c.operation==='layout');
const htmlEscape=s=>s.replace(/&/g,'&amp;').replace(/"/g,'&quot;').replace(/</g,'&lt;');
const browserRequests=browserCases.map(c=>{
  const sheets=c.compiled??c.css.map((text,i)=>compileCss(text,{name:`sheet-${i}.css`}));
  const render=index=>{const n=c.tree[index];return `<${n.tag}${n.attributes.map(([k,v])=>` ${k}="${htmlEscape(v)}"`).join('')}${c.inline[index]?` style="${htmlEscape(c.inline[index])}"`:''}>`+
    (index===1?sheets.map(s=>`<link rel="stylesheet" href="${htmlEscape(s.name)}">`).join(''):'')+
    (n.hasText?'x':'')+n.children.map(render).join('')+`</${n.tag}>`;};
  const html='<!doctype html>'+render(0),target=c.target===0?'document.documentElement':c.target===2?'document.body':`document.getElementById(${JSON.stringify(c.tree[c.target].attributes.find(([k])=>k==='id')[1])})`;
  return {browserLibrary:true,ast:compileJavaScript((c.dynamicScript??'')+`var r=${target}.getBoundingClientRect();r.x+","+r.y+","+r.width+","+r.height;`,{name:c.name}),fuel:100000,
    initialHtmlUnits:Array.from({length:html.length},(_,i)=>html.charCodeAt(i)),loadedStylesheets:sheets,
    fixtureWindowData:(c.omitViewport?[]:['innerWidth','innerHeight']).map((name,i)=>({name,value:{kind:'number',bits:numberLiteralBits(native.result.viewport[i])}}))};
});
const browserChild=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(browserRequests),encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});
if(browserChild.error)throw browserChild.error;assert.equal(browserChild.status,0,browserChild.stderr);const browserObserved=JSON.parse(browserChild.stdout);
let browserFailures=0;for(let i=0;i<browserCases.length;i++)try{
  const c=browserCases[i],actual=browserObserved[i];
  if(c.browserExpectedStatus??c.expectedStatus)assert.equal(actual.status,c.browserExpectedStatus??c.expectedStatus);
  else{assert.equal(actual.status,'complete');assert.deepEqual(actual.value,{type:'string',units:Array.from(native.result.values[c.index].box.join(','),c=>c.charCodeAt(0))});}
}catch(error){browserFailures++;failures.push({name:`browser adapter ${browserCases[i].name}`,observed:browserObserved[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:pureCases.length,passed:pureCases.length-(failures.length-browserFailures),nativeComparisons:pureCases.filter(c=>!c.expectedStatus).length,
  browserAdapterCases:browserCases.length,browserAdapterPassed:browserCases.length-browserFailures,
  stylesheets:pinned.map(s=>({name:s.name,sha256:s.sha256})),viewport:native.result.viewport,versions:native.versions,executableHash:native.executableHash,
  gameEntryPointExecuted:false,rendererRefinementVerified:false,hitTestingVerified:false}));

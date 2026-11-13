/** Definite vertical layout probes. This is not a browser-renderer refinement theorem. */
import assert from 'node:assert/strict';
import{readFileSync}from'node:fs';
import{fileURLToPath}from'node:url';
import{spawnSyncWithFileInput as spawnSync}from'./process-input.mjs';
import{compileCss,compilePinnedStylesheets}from'../model/css-ast.mjs';
import{compileJavaScript,numberLiteralBits}from'../model/javascript-ast.mjs';
import{defaultGameSourceDirectory}from'../model/game-source.mjs';
import{runNativeBrowser}from'../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw new Error('Height comparisons require the isolated pinned Chromium worker');
const baseTree=()=>[
 {tag:'html',attributes:[],parent:null,previous:null,children:[1,2],hasText:false,documentRoot:true},
 {tag:'head',attributes:[],parent:0,previous:null,children:[],hasText:false,documentRoot:false},
 {tag:'body',attributes:[],parent:0,previous:1,children:[3],hasText:false,documentRoot:false},
 {tag:'div',attributes:[['id','outer']],parent:2,previous:null,children:[4],hasText:false,documentRoot:false},
 {tag:'div',attributes:[['id','target']],parent:3,previous:null,children:[],hasText:true,documentRoot:false}
];
const base='html,body,div{margin:0;padding:0;border:0}html,body{width:100%;height:100%}body{overflow:hidden}#outer{position:relative;width:400px;height:400px}#target{top:5px;bottom:7px}';
const cases=[];const add=(name,css,extra={})=>cases.push({name,css:[base+css],tree:baseTree(),target:4,...extra});
for(const position of ['static','relative','absolute','fixed'])for(const height of ['auto','0','40px','100%','25%'])
for(const sizing of ['content-box','border-box'])for(const edges of ['', 'padding:3px 8px;margin:2px 5px;border-style:solid;border-width:2px']){
 add(`${position} ${height} ${sizing} ${edges}`,`#target{position:${position};height:${height};box-sizing:${sizing};${edges}}`,
  height==='auto'&&['static','relative'].includes(position)?{expectedStatus:'unresolved'}:{});
}
for(const rule of ['min-height:500px','max-height:80px','height:70px;min-height:100px;max-height:30px',
 'height:5px;padding:20px;box-sizing:border-box','top:300px;bottom:200px','margin-top:-20px;margin-bottom:15px',
 'transition:opacity 1s','transition:text-shadow 0.25s,background 0.25s','transition-property:opacity,background',
 'width:auto;min-width:100px;padding-left:16px;padding-right:32px','width:1.5px',
 'overflow:hidden','overflow:visible'])add(`definite height ${rule}`,`#target{position:absolute;${rule}}`);
for(const position of ['absolute','relative'])for(const sizing of ['content-box','border-box'])
 add(`containing padding ${position} ${sizing}`,
 `#outer{padding:10px 20px;border-style:solid;border-width:5px;box-sizing:${sizing}}#target{position:${position};height:50%}`);
add('hidden ancestor has no box','#outer{display:none}');
add('irrelevant hover width does not determine height','#target{height:50px}#target:hover{width:19px}');
add('paired hover overflow does not determine height','#target{height:50px;overflow:hidden}#target:hover{overflow:visible}');
for(const rule of ['height:1.5px','height:33.3%','position:absolute;top:auto;height:auto',
 'overflow:scroll','overflow:hidden visible','float:left','display:inline','transform:scale(2)',
 'animation-name:move','transition:height 1s','transition:all 1s','min-height:-1px','padding-top:-1px',
 'padding-top:10%','margin-bottom:5%'])add(`unsupported height ${rule}`,`#target{${rule}}`,{expectedStatus:'unresolved'});
add('fractional fixed viewport percent needs LayoutUnit','#target{position:fixed;height:30%}',{expectedStatus:'unresolved'});
add('fractional exact integer percent needs LayoutUnit','#outer{height:333px}#target{height:30%}',{expectedStatus:'unresolved'});
add('binary32 percentage product bound','#outer{height:1000000px}#target{height:100%}',{expectedStatus:'unresolved'});
add('auto containing height remains explicit','#outer{height:auto}#target{height:100%}',{expectedStatus:'unresolved'});
add('viewport scrollbar exclusion required','body{overflow:visible}#target{height:50px}',{expectedStatus:'unresolved'});
add('viewport all reset is explicit','body{overflow:hidden;all:initial}#target{height:50px}',{expectedStatus:'unresolved'});
add('unknown dynamic height remains explicit','#target{height:50px}#target:hover{height:31px}',{expectedStatus:'unresolved'});
for(const timing of ['ease','linear','ease-in','ease-out','ease-in-out','step-start','step-end'])
 add(`paint timing keyword ${timing}`,`#target{position:absolute;transition:opacity 0.1s ${timing}}`);
add('source framed transition','#target{position:absolute;transition:opacity 0.1s ease-out;color:red}');
add('mixed paint timing keywords','#target{position:absolute;transition:opacity 0.1s ease-out,background-color 100ms linear}');
for(const transition of ['height 0.1s ease-out','width 0.1s ease-out','all 0.1s ease-out',
 'opacity 0.1s unknown','opacity -1s ease-out','opacity 1px ease-out',
 'opacity 0.1s cubic-bezier(0,0,1,1)','opacity 0.1s ease-out 0.1s'])
 add(`unproved transition ${transition}`,`#target{position:absolute;transition:${transition}}`,{expectedStatus:'unresolved'});
const pinned=compilePinnedStylesheets().reverse(),directory=defaultGameSourceDirectory();
for(const mode of ['onWeb','offWeb'])for(const target of [3,4,5]){
 const t=baseTree();t[3].attributes=[['id','wrapper'],['class',mode]];t[3].children=[4];
 t[4].attributes=[['id','game']];t[4].children=[5];t[4].hasText=false;
 t.push({tag:'div',attributes:[['id','sectionLeft']],parent:4,previous:null,children:[],hasText:false,documentRoot:false});
 cases.push({name:`pinned ${mode} ${target}`,css:pinned.map(s=>readFileSync(new URL(s.name,`file://${directory}/`),'utf8')),compiled:pinned,tree:t,target});
}
const worker=function(cases){return{viewport:[innerWidth,innerHeight],values:cases.map(c=>{
 if(c.expectedStatus)return{status:c.expectedStatus};
 document.adoptedStyleSheets=[];document.head.textContent='';document.body.textContent='';
 const nodes=c.tree.map((n,i)=>i===0?document.documentElement:i===1?document.head:i===2?document.body:document.createElement(n.tag));
 nodes.forEach((node,i)=>{Array.from(node.attributes).forEach(a=>node.removeAttribute(a.name));for(const[k,v]of c.tree[i].attributes)node.setAttribute(k,v);if(c.tree[i].hasText)node.textContent='A long ticker line whose text can wrap into several lines.';});
 for(let i=3;i<nodes.length;i++)nodes[c.tree[i].parent].appendChild(nodes[i]);
 document.adoptedStyleSheets=c.css.map(text=>{const sheet=new CSSStyleSheet();sheet.replaceSync(text);return sheet;});
 const node=nodes[c.target],style=getComputedStyle(node),border=node.offsetHeight,padding=node.clientHeight;
 if(!node.getClientRects().length)return{status:'complete',heights:[0,0,0]};
 return{status:'complete',heights:[padding-parseFloat(style.paddingTop)-parseFloat(style.paddingBottom),padding,border]};
})};};
const native=runNativeBrowser(worker.toString(),cases);
const requests=cases.map(c=>({operation:'height',stylesheets:c.compiled??c.css.map((text,i)=>compileCss(text,{name:`height-${i}`})),tree:c.tree,target:c.target,viewport:native.result.viewport,inline:c.tree.map(()=>compileCss('a{}'))}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const results=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(results[i].status,cases[i].expectedStatus);else assert.deepEqual(results[i],native.result.values[i]);}catch(error){failures.push({name:cases[i].name,observed:results[i],expected:native.result.values[i],error:error.message});}
const units=text=>Array.from({length:text.length},(_,index)=>text.charCodeAt(index));
const escape=text=>text.replace(/&/g,'&amp;').replace(/"/g,'&quot;').replace(/</g,'&lt;');
const browserRequests=cases.map(c=>{
 const sheets=c.compiled??c.css.map((text,i)=>compileCss(text,{name:`height-${i}.css`}));
 const render=index=>{const n=c.tree[index];return `<${n.tag}${n.attributes.map(([k,v])=>` ${k}="${escape(v)}"`).join('')}>`+
  (index===1?sheets.map(s=>`<link rel="stylesheet" href="${escape(s.name)}">`).join(''):'')+
  (n.hasText?'A long ticker line whose text can wrap into several lines.':'')+n.children.map(render).join('')+`</${n.tag}>`;};
 const html='<!doctype html>'+render(0),target=c.tree[c.target].attributes.find(([name])=>name==='id')[1];
 return {browserLibrary:true,ast:compileJavaScript(`var e=document.getElementById(${JSON.stringify(target)});e.offsetHeight+","+e.clientHeight;`,{name:c.name}),
  fuel:100000,initialHtmlUnits:units(html),loadedStylesheets:sheets,
  fixtureWindowData:['innerWidth','innerHeight'].map((name,index)=>({name,value:{kind:'number',bits:numberLiteralBits(native.result.viewport[index])}}))};
});
const adapter=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(browserRequests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(adapter.error)throw adapter.error;assert.equal(adapter.status,0,adapter.stderr);const adapterResults=JSON.parse(adapter.stdout);let adapterFailures=0;
for(let i=0;i<cases.length;i++)try{
 if(cases[i].expectedStatus)assert.equal(adapterResults[i].status,cases[i].expectedStatus);
 else{assert.equal(adapterResults[i].status,'complete');const heights=native.result.values[i].heights;assert.deepEqual(adapterResults[i].value,{type:'string',units:units(heights[2]+','+heights[1])});}
}catch(error){adapterFailures++;failures.push({name:`browser ${cases[i].name}`,observed:adapterResults[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-(failures.length-adapterFailures),browserAdapterCases:cases.length,browserAdapterPassed:cases.length-adapterFailures,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,rendererRefinementVerified:false}));

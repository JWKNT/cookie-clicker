/** Source border shorthand geometry; native layout measurements are test outputs only. */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {compileCss,compilePinnedStylesheets} from '../model/css-ast.mjs';
import {defaultGameSourceDirectory} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
import {spawnSyncWithFileInput} from './process-input.mjs';

if(!process.argv.includes('--engine'))throw Error('Border comparisons require isolated pinned Chromium');
const cases=[],add=(name,declaration,expectedStatus)=>cases.push({name,declaration,expectedStatus});
const reset='html,body,div{margin:0;padding:0;border:0}html,body{height:100%;width:100%;overflow:hidden}#target{position:absolute;left:0;top:0;width:100px;height:40px;padding:2px}';
for(const value of ['0','0px','none','hidden','solid','dashed','double','groove','ridge','inset','outset',
 'thin','medium','thick','red','transparent','currentColor','#12345680','rgb(12, 34, 56)',
 'rgba(255, 255, 255, 0.25)','1px solid #ccc','3px solid transparent','0px solid #000']){
 add('border shorthand '+value,`border:${value};`);
 add('border shorthand then solid '+value,`border:${value};border-style:solid;`);
}
const permutations=values=>values.length?values.flatMap((v,i)=>permutations(values.filter((_,j)=>j!==i)).map(rest=>[v,...rest])):[[]];
for(const words of permutations(['3px','dashed','#abc']))add('border order '+words.join(' '),'border:'+words.join(' ')+';');
for(const side of ['top','right','bottom','left']){
 add('side resets to medium '+side,`border-${side}:none;border-${side}-style:solid;`);
 add('side zero remains zero '+side,`border-${side}:0;border-${side}-style:solid;`);
 add('side explicit width '+side,`border-${side}:5px double #abc;`);
 add('all none resets preceding side '+side,`border-${side}:5px solid;border:none;border-style:solid;`);
}
for(const declaration of ['border:none!important;border-style:solid;',
 'border:solid;border-left-width:7px;', 'border-left-width:7px;border:solid;',
 'border:solid red;border:none;border-left-style:solid;',
 'border:3PX SOLID RED;', 'border:-0px solid;', 'border:0 solid;'])add('cascade/default '+declaration,declaration);
for(const declaration of ['border:-1px solid;', 'border:1.5px solid;', 'border:1em solid;',
 'border:solid solid;', 'border:3px 4px solid;', 'border:3px solid notacolor;',
 'border:inherit;', 'border:initial;', 'border:3px solid hsl(0,100%,50%);',
 'border:calc(1px + 1px) solid;'])add('explicit grammar '+declaration,declaration,'unresolved');
let sourceDeclarations=0;
for(const sheet of compilePinnedStylesheets()){
 const source=readFileSync(defaultGameSourceDirectory()+'/'+sheet.name,'utf8');
 for(const rule of sheet.rules)if(rule.kind==='style')for(const declaration of rule.declarations){
  if(!/^border(?:-(?:top|right|bottom|left))?$/.test(declaration.property))continue;
  sourceDeclarations++;
  add(`actual source ${sheet.name}:${declaration.start}`,source.slice(declaration.start,declaration.end)+';');
 }
}
assert.equal(sourceDeclarations,25);
const native=runNativeBrowser(function(input){return{viewport:[innerWidth,innerHeight],cases:input.cases.map(test=>{
 if(test.expectedStatus)return{status:test.expectedStatus};
 document.adoptedStyleSheets=[];document.head.textContent='';document.body.textContent='';
 for(const node of [document.documentElement,document.body])Array.from(node.attributes).forEach(a=>node.removeAttribute(a.name));
 const target=document.createElement('div');target.id='target';document.body.appendChild(target);
 const sheet=new CSSStyleSheet();sheet.replaceSync(input.reset+'#target{'+test.declaration+'}');document.adoptedStyleSheets=[sheet];
 return{widths:[100,target.clientWidth,target.offsetWidth],heights:[40,target.clientHeight,target.offsetHeight]};
 })};}.toString(),{cases,reset});
const tree=[
 {tag:'html',attributes:[],parent:null,previous:null,children:[1],hasText:false,documentRoot:true},
 {tag:'body',attributes:[],parent:0,previous:null,children:[2],hasText:false,documentRoot:false},
 {tag:'div',attributes:[['id','target']],parent:1,previous:null,children:[],hasText:false,documentRoot:false},
];
const requests=cases.flatMap(test=>['width','height'].map(operation=>({operation,
 stylesheets:[compileCss(reset+'#target{'+test.declaration+'}')],tree,target:2,
 viewport:native.result.viewport,inline:tree.map(()=>compileCss('x{}'))})));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout),failures=[];
for(const [i,test]of cases.entries())try{
 for(const [j,field]of ['widths','heights'].entries()){
  const result=observed[2*i+j];if(test.expectedStatus)assert.equal(result.status,test.expectedStatus);
  else assert.deepEqual(result,{status:'complete',[field]:native.result.cases[i][field]});
 }
}catch(error){failures.push({name:test.name,observed:observed.slice(2*i,2*i+2),expected:native.result.cases[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,
 nativeComparisons:cases.filter(c=>!c.expectedStatus).length,sourceDeclarations,
 versions:native.versions,executableHash:native.executableHash,rendererRefinementVerified:false}));

import assert from 'node:assert/strict';
import {runInNewContext} from 'node:vm';
import {fileURLToPath} from 'node:url';
import {loadGameSource} from '../model/game-source.mjs';
import {createHash} from 'node:crypto';
import {compileCss,tokenizeCss} from '../model/css-ast.mjs';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
const pantheonSource=loadGameSource().sources['minigamePantheon.js'];
const start=pantheonSource.indexOf("str+='<style>'+"),end=pantheonSource.indexOf("'</style>';",start)+"'</style>';".length;
assert(start>=0&&end>start);
// This exact source expression only assembles the stylesheet with a fixed resource prefix.
// No game state, save, generator, or outcome is read here.
const temple=runInNewContext("var Game={resPath:''};var str='';"+pantheonSource.slice(start,end)+"str;",{},{timeout:1000}).slice(7,-8);
const main=loadGameSource().sources['main.js'];
const launchStart=main.indexOf("var css=document.createElement('style');",main.indexOf('Game.Launch=function()'));
const launchEnd=main.indexOf('document.head.appendChild(css);',launchStart)+'document.head.appendChild(css);'.length;
assert(launchStart>=0&&launchEnd>launchStart);
let launch;
runInNewContext(main.slice(launchStart,launchEnd),{Game:{resPath:'',version:2.053},document:{createElement(){return{}},head:{appendChild(node){launch=node.innerHTML;}}}},{timeout:1000});
const styles=[launch,temple];
const cases=[];
function tokens(source){cases.push({operation:'runtime-css-tokenize',source,expected:tokenizeCss(source)});}
function parse(source){cases.push({operation:'runtime-css-parse',source,expected:compileCss(source,{name:'fixture'})});}
for(const sign of ['', '-', '+'])for(const whole of ['0','1','12345'])for(const fraction of ['', '.0','.005'])for(const exponent of ['', 'e2','E+3','e-8'])for(const suffix of ['', '%','px','s'])tokens(sign+whole+fraction+exponent+suffix);
for(const source of ['.5','-.5','+.5','1.','1e','1e+','1e-','1E.2','1.2.3','+','-','.','--1','1e2foo','1E-2px','0/**/.5', 'rgba(255, 0, 1, .75)', 'linear-gradient(to top, rgba(0,0,0,0.1),rgba(0,0,0,0))', 'url("a;b}c")', 'url(a;b}c)', 'calc(1px + (2px))'])tokens(source);
for(const style of styles){tokens(style);parse(style);}
for(const source of ['#x{opacity:.5;transition:transform 1e-1s}', '.absent:hover,.absent:active{top:1.5px;color:rgba(1,2,3,.5)}', '#x{background:linear-gradient(to top,rgba(0,0,0,.1),rgba(0,0,0,0));top:2px}', '#x{custom:f(";}",g([x;y]));left:2px}', '#x::before,#x:before{content:";}"}', '#x{background:url("a;b}c");top:7px}', '#x{width:1e2px!important}'])parse(source);
const invalid=['#x{color:rgb(1,2,3}','#x{color:rgb(1,2,3));}','#x{color:f([)];}','#x{color:f(1;top:2px}','#x{custom:{nested};}','#x:hover(){top:1px}','@media screen{#x{top:1px}}','#x{top:1px','[x=y]{top:1px}'];
for(const source of invalid)cases.push({operation:'runtime-css-parse',source,expectedStatus:'unresolved'});
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(cases),encoding:'utf8',timeout:60000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);
const out=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(out[i].status,cases[i].expectedStatus);else{assert.equal(out[i].status,'complete');assert.equal(out[i].equal,true);}}catch(e){failures.push({i,source:cases[i].source,result:out[i],message:e.message});}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,failures:failures.slice(0,2),templeCssHash:createHash('sha256').update(temple).digest('hex'),frontendEquivalenceOnly:true,nativeRendererRefinementVerified:false}));if(failures.length)process.exitCode=1;

/** Exact source dependencies and open obligations for a prompt-layout quotient.
 * This audit does not erase layout from the executable game model. */
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {loadGameSource} from '../model/game-source.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const {parse}=require('acorn');
const source=loadGameSource(),main=source.sources['main.js'];
const ast=parse(main,{ecmaVersion:2020,locations:true});
const nodes=[];
function walk(node){if(!node||typeof node!=='object')return;if(node.type)nodes.push(node);for(const [key,value]of Object.entries(node)){if(key==='loc')continue;if(Array.isArray(value))value.forEach(walk);else if(value&&typeof value==='object')walk(value);}}
walk(ast);
function path(node){if(node?.type==='Identifier')return node.name;if(node?.type==='MemberExpression'){const property=node.computed?(node.property.type==='Literal'?String(node.property.value):null):node.property.name;const object=path(node.object);return object&&property!==null?object+'.'+property:null;}return null;}
const hash=text=>createHash('sha256').update(text).digest('hex');
const span=node=>({start:node.start,end:node.end,line:node.loc.start.line,endLine:node.loc.end.line,sha256:hash(main.slice(node.start,node.end))});
const names=['Game.UpdatePrompt','Game.Prompt','Game.ClosePrompt','Game.ConfirmPrompt','Game.FocusPromptOption','Game.showLangSelection'];
const functions=Object.fromEntries(names.map(name=>{const matches=nodes.filter(n=>n.type==='AssignmentExpression'&&path(n.left)===name&&n.right.type==='FunctionExpression');assert.equal(matches.length,1,name);return[name,matches[0].right];}));
const update=functions['Game.UpdatePrompt'];
assert.equal(update.body.body.length,2);
assert.equal(update.body.body[0].type,'IfStatement');
assert.equal(path(update.body.body[0].test),'Game.promptUpdateFunc');
const store=update.body.body[1].expression;
assert.equal(store.type,'AssignmentExpression');
assert.equal(path(store.left),'Game.promptAnchorL.style.top');
assert.equal(main.slice(store.right.start,store.right.end),"Math.floor((Game.windowH-Game.promptWrapL.offsetHeight)/2-16)+'px'");
const within=node=>nodes.filter(n=>n.start>=node.start&&n.end<=node.end);
const assignments=within(update).filter(n=>n.type==='AssignmentExpression').map(n=>({target:path(n.left),...span(n)}));
const calls=within(update).filter(n=>n.type==='CallExpression').map(n=>({callee:path(n.callee),...span(n)}));
assert.deepEqual(assignments.map(n=>n.target),['Game.promptAnchorL.style.top']);
assert.deepEqual(calls.map(n=>n.callee),['Game.promptUpdateFunc','Math.floor']);
const references=['Game.promptAnchorL','Game.promptWrapL','Game.promptOn','Game.promptUpdateFunc'].map(name=>({name,
 references:nodes.filter(n=>n.type==='MemberExpression'&&path(n)===name).map(span)}));
assert.equal(nodes.filter(n=>n.type==='MemberExpression'&&path(n)==='Game.App').length,0);
const runtime=readFileSync(new URL('../model/runtime.mjs',import.meta.url),'utf8');
assert(runtime.includes("context.localStorage.setItem('CookieClickerLang', 'EN');"));
assert(source.sources['index.html'].includes("var App=typeof App==='undefined'?0:App;"));
assert(main.includes("if (App && !lang) showLangSelect(loadLangAndLaunch);"));
assert(main.includes("else if (!lang) {loadLangAndLaunch('EN',true);}"));
assert(main.includes("else loadLangAndLaunch(lang);"));
const report={schema:1,sourceHashes:source.hashes,scope:'source-prompt-layout-dependency-audit',
 functions:Object.entries(functions).map(([name,node])=>({name,...span(node)})),
 update:{assignments,calls,evaluationOrder:[
  'Read promptUpdateFunc; if truthy, read it again and invoke it with Game as receiver.',
  'Resolve promptAnchorL and its style object before evaluating the right-hand side.',
  'Resolve Math.floor, read windowH, then read promptWrapL.offsetHeight.',
  'Perform the source subtraction, division, subtraction, floor and string concatenation.',
  'Set the native style top property; preserve its conversions, validation and exceptions.'
 ],directRandomDraws:0,callbackEffectsMustBeRetained:true},references,
 startup:{globalSwitch:'App',gameAppReferences:0,gameSetting:'CookieClickerLang',
  executableFixture:'Steam adapter plus English in browser localStorage; game save is empty.',
  routes:[
   {app:false,language:'absent',loadLanguage:'EN',firstLaunch:true,postInitLanguagePrompt:true},
   {app:false,language:'EN',loadLanguage:'EN',firstLaunch:false,postInitLanguagePrompt:false},
   {app:true,language:'absent',prelaunchSelection:true,firstLaunch:false,postInitLanguagePrompt:false},
   {app:true,language:'EN',loadLanguage:'EN',firstLaunch:false,postInitLanguagePrompt:false}],
  steamWrapperExecutedByLeanProbe:false,configuredEnglishChangesGameSave:false},
 quotient:{status:'obligations-only; no executable transition is replaced',
  possibleLowerBound:'Allow additional target activations independent of geometric hit testing, while retaining the source handlers, random-draw order, elapsed time and completion predicate. A proven simulation into this larger strategy class would give a lower bound.',
  retained:['promptUpdateFunc calls and their complete effects','promptOn, promptNoClose, options and focused option state','DOM target identities, callback paths and source event ordering','All audio and source random draws','Public observations, including allowed save export','Native save and reload effects'],
  obligations:[
   'Show that each concrete native task maps to an abstract task with the same retained state, draw stream and elapsed time.',
   'Do not remove information available to a concrete observation-based policy; define a history/observation simulation.',
   'Retain style/layout-flush effects that can invoke callbacks, queue events or change retained state.',
   'Prove that every concrete legal action is admitted by the larger abstract action class.',
   'For a candidate upper bound, construct concrete target reachability, hit-test and event/default-action witnesses. The lower-bound action expansion does not supply these.',
   'Show equality of the candidate cost with a certified lower bound; a source dependency audit alone supplies neither.'
  ],
  counterexamplesToBlanketErasure:[
   'Prompt position changes pointer target reachability and visual observations.',
   'promptOn gates bulk-key shortcuts and ascension inputs.',
   'Language mouseover changes the heading and plays audio; the click requests a current save and reload.',
   'Ordinary prompt options can buy upgrades, spend lumps and ascend.',
   'The first language prompt has zero option buttons, so ConfirmPrompt cannot replace its language click.',
   'Canvas dimensions influence source draw loops and random draws; the prompt slice does not justify erasing those metrics.'
  ]},
 sourceNoninterferenceProved:false,rendererRefinementVerified:false,optimalityProved:false};
const target=new URL('../model/prompt-layout-audit.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),text,'Prompt layout audit is stale');
else writeFileSync(target,text);
console.log(JSON.stringify({functions:report.functions.length,directAssignments:assignments.length,directCalls:calls.length,sourceNoninterferenceProved:false}));

import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine,EXPECTED_NATIVE_ENGINE} from '../model/native-engine.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url)),acorn=require('acorn');
const source=loadGameSource(),main=source.sources['main.js'],hash=s=>createHash('sha256').update(s).digest('hex');
const fn=(text,name)=>{let a=text.indexOf(name+'=function');assert(a>=0,name);return acorn.parseExpressionAt(text,a+name.length+1,{ecmaVersion:2020,locations:true})};
const init=fn(main,'Game.Init'),scheduling=init.body.body.find(n=>n.type==='IfStatement'&&main.slice(n.start,n.end).includes('else if (App.saveData) setTimeout'));
assert(scheduling);const timerPaths=[];const walk=(n,f)=>{if(!n||typeof n!=='object')return;f(n);for(const[k,v]of Object.entries(n)){if(k==='loc')continue;if(Array.isArray(v))v.forEach(x=>walk(x,f));else if(v&&typeof v==='object')walk(v,f)}};
walk(scheduling.alternate,n=>{if(n.type==='CallExpression'&&n.callee.type==='Identifier'&&n.callee.name==='setTimeout'){assert.equal(n.arguments[1].value,100);timerPaths.push({line:n.loc.start.line,callback:main.slice(n.arguments[0].start,n.arguments[0].end),delay:n.arguments[1].value});}});assert.equal(timerPaths.length,2);
const exportFn=fn(main,'Game.ExportSave'),exportText=main.slice(exportFn.start,exportFn.end),saveFn=fn(main,'Game.WriteSave'),saveText=main.slice(saveFn.start,saveFn.end);
const files={...source.sources,'../steam/steam.js':readFileSync(join(dirname(source.directory),'steam/steam.js'),'utf8'),'../start.js':readFileSync(join(dirname(source.directory),'start.js'),'utf8')};
const loadSites=[];for(const[file,text]of Object.entries(files))text.split('\n').forEach((line,index)=>{if(/Game\.LoadSave\s*\(/.test(line))loadSites.push({file,line:index+1,text:line.trim()})});
assert(!exportText.includes('LoadSave')&&!saveText.includes('LoadSave'));
const sourceFragment=main.slice(scheduling.start,scheduling.end);
const worker=String.raw`
const fs=require('fs'),vm=require('vm');const x=JSON.parse(fs.readFileSync(0,'utf8'));
const results=[];for(const tag of ['missing','empty','current-save','false','zero','null','object']){
 const timers=[],calls=[];const App={};if(tag!=='missing')App.saveData=tag==='empty'?'':tag==='current-save'?'CURRENT-SAVE':tag==='false'?false:tag==='zero'?0:tag==='null'?null:{};
 const Game={LoadSave:function(){calls.push(Array.from(arguments).map(v=>v===undefined?'undefined':typeof v==='object'?'object':v));}};
 const c=vm.createContext({App,Game,setTimeout:function(callback,delay){timers.push({callback,delay});},localStorageGet:()=>{throw Error('web branch entered')}});
 vm.runInContext(x.scheduling,c);
 if(calls.length!==0||timers.length!==1||timers[0].delay!==100)throw Error('early source load or wrong timer');
 const before=calls.length;timers[0].callback();results.push({tag,scheduledDelay:timers[0].delay,loadCallsBeforeCallback:before,callbackLoadArguments:calls});
}
const trace=[],el={focus:()=>trace.push('focus'),select:()=>trace.push('select')};
const c=vm.createContext({Game:{prefs:{},WriteSave:t=>{trace.push('WriteSave:'+t);return'CURRENT-SAVE'},Prompt:()=>trace.push('Prompt'),LoadSave:()=>{throw Error('export restored')}},loc:x=>x,l:()=>el});
vm.runInContext('Game.ExportSave=('+x.exportSave+');Game.ExportSave();',c);
process.stdout.write(JSON.stringify({versions:process.versions,cases:results,exportTrace:trace,exportBackupWarning:c.Game.prefs.showBackupWarning,gameEntryPointExecuted:false,realTimersOrNavigationExecuted:false}));
`;
const native=runNativeEngine(worker,{scheduling:sourceFragment,exportSave:exportText},{timeout:30000});
for(const[k,v]of Object.entries(EXPECTED_NATIVE_ENGINE))assert.equal(native.versions[k],v);
assert.deepEqual(native.exportTrace,['WriteSave:1','Prompt','focus','select']);
const report={schema:'cookie-steam-reload-load-gate-v1',sourceHashes:Object.fromEntries(Object.entries(files).map(([k,v])=>[k,hash(v)])),startupTimerPaths:timerPaths,sourceFragment:{text:sourceFragment,sha256:hash(sourceFragment)},native,workerSha256:hash(worker),loadSites,restorationEntryClassification:[{entry:'Steam Init App.saveData truthy',gateMilliseconds:100,site:'main.js16116'},{entry:'Steam Init App.saveData falsy/missing',gateMilliseconds:100,site:'main.js16117 then2899–2908 and Steam.getMostRecentSave callback'},{entry:'Web Init localStorage/cookie',gateMilliseconds:0,applicableToPinnedSteam:false,site:'main.js16106–16115'},{entry:'Game.Resume',gate:'Prior Game.Timeout UI state; fresh Init resets lastActivity/time/delayTimeouts. Native timeout requires at least300000ms inactivity.',site:'main.js1937–1957,1998–2003,16781–16785',fullReachabilityProof:false},{entry:'Game.ImportSaveCode',admissible:false,reason:'Current user control contract forbids imports.',site:'main.js2621–2626'},{entry:'Steam.restoreBackup',admissible:false,reason:'Older-state restoration is forbidden; bakery-name backup command is not maintenance.',site:'steam/steam.js141–149;main.js2255'},{entry:'Game.LoadSave internal App callback',gate:'Inherits the call time of its initiating LoadSave request; no independent startup application.',site:'main.js2907'},{entry:'Steam.loadMods metadata read',restoresGameState:false,site:'steam/steam.js564; calls analyzeSaveData then extracts modMeta'}],sourceStateDistinction:{readyIsRestored:false,readySetAtInitEntry:'main.js1963',freshCountersReset:'main.js1968–2045',gateRegistered:'main.js16116–16117',freshLoopBeforeLoad:'main.js16119–16124',exportRestores:false,exportEffects:'WriteSave(1), last-save bookkeeping, prompt/focus/select retained; native export does not call LoadSave or App.save.'},scope:{startupFragmentNativeExecution:true,timerRegistrationCapturedNotNativeTimerFiring:true,fullStartupRefinement:false,fullCurrentSaveCodecProof:false,allReloadInterleavingsCovered:false,noImportedOrPlayerSaveRead:true},conclusion:'For the standard pinned Steam startup save-restoration path, a timer with requested delay100 must fire before that path can apply the saved state. Chromium87 normalizes100 to100 at every nesting depth. Zero navigation/assets/IPC latency cannot erase this gate. Fresh-state input before the callback, abandoned/overlapping navigations, alternative entry reachability and callback host effects remain part of the full model.'};
const output=new URL('../model/reload-load-gate.json',import.meta.url);if(process.argv.includes('--check'))assert.deepEqual(JSON.parse(readFileSync(output,'utf8')),report);else writeFileSync(output,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({timerPaths:timerPaths.length,nativeCases:native.cases.length,delay:100,exportTrace:native.exportTrace,loadSites:loadSites.length}));

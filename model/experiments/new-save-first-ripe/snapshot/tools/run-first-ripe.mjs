import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createPolicySession,decidePolicy,censorPolicyAction} from '../model/policy-runtime.mjs';
import {assessCompletion,buildCompletionContract} from '../model/completion.mjs';
import {completionPolicySource} from '../model/completion-policy.mjs';
const read=name=>JSON.parse(readFileSync(new URL('../model/'+name,import.meta.url),'utf8'));
const contract=buildCompletionContract(read('catalogue.json'),read('completion-profile.json'));
const horizon=Number(process.argv[2]||365*24*3600000),label=process.argv[3]||'full-route';
const config={clickRate:50,inputBatchMilliseconds:1000,lowEffects:true,earlyFunding:{cycles:16384,batchCycles:249},helperSetup:true};
const environment={randomSeed:1,recordAudit:false,maintenanceReload:{firstMs:7*24*3600000,everyMs:7*24*3600000}};
const source=completionPolicySource(config),policySha256=createHash('sha256').update(source).digest('hex');
writeFileSync(new URL('../'+label+'-policy.js',import.meta.url),source+'\n');
writeFileSync(new URL('../'+label+'-start.json',import.meta.url),JSON.stringify({config,environment,horizon,policySha256,startedAtUtc:new Date().toISOString()},null,2)+'\n');
let firstCompletionMs=null,checkpoints=0,lastCheckpointMs=0;
const session=createPolicySession({...environment,
 transitionAchievementGate:contract.requiredAchievements.map(({name})=>name),
 onTransition:event=>{
  if(event.elapsedMs<lastCheckpointMs)throw new Error('Nonmonotone native checkpoint');
  lastCheckpointMs=event.elapsedMs;checkpoints++;
  if(firstCompletionMs===null&&event.observation&&assessCompletion(event.observation,contract).complete)firstCompletionMs=event.elapsedMs;
 }});
let o=session.policy.observe(),m=null,decisions=0,nextProgress=0,stage=null,error=null,status='censored',sameTime=0,previousTime=o.elapsedMs;
const start=performance.now(),stages={};let interrupted=false;
process.on('SIGINT',()=>{interrupted=true});process.on('SIGTERM',()=>{interrupted=true});
const brief=()=>({elapsedMs:o.elapsedMs,decisions,stage,bank:o.cookies,earned:o.cookiesEarned,cps:o.cookiesPs,click:o.cookiesPerClick,
 ascensions:o.ascensions,prestige:o.prestige,lumps:o.lumps,lump:o.lump,temple:{amount:o.progression.buildingAmounts.Temple,level:o.progression.buildingLevels.Temple},
 achievementsOwned:o.progression.achievementsOwned,wonFlags:Object.values(o.achievements).filter(Boolean).length,
 garden:o.garden?{level:o.garden.level,seeds:o.progression.gardenSeeds.length,converts:o.garden.convertTimes}:null,
 buff:o.buffs.Devastation?{time:o.buffs.Devastation.time,multClick:o.buffs.Devastation.multClick}:null,
 hardcore:o.achievements.Hardcore,neverclick:o.achievements.Neverclick,firstCompletionMs,checkpoints,
 wallSeconds:(performance.now()-start)/1000,rss:process.memoryUsage().rss});
try{
 while(firstCompletionMs===null&&o.elapsedMs<=horizon&&decisions<50000000&&sameTime<1000000&&!interrupted){
  const d=decidePolicy(source,o,session.policy.actions(),m,{timeoutMs:10000});m=d.memory;stage=d.stage;stages[stage]=(stages[stage]||0)+1;
  const remaining=horizon-o.elapsedMs;
  const requested=d.action.type==='wait'?d.action.milliseconds:d.action.type==='sequence'?d.action.actions.reduce((sum,a)=>sum+(a.type==='wait'?a.milliseconds:0),0):0;
  o=session.policy.act(censorPolicyAction(d.action,remaining));decisions++;
  sameTime=o.elapsedMs===previousTime?sameTime+1:0;previousTime=o.elapsedMs;
  if(o.elapsedMs>=nextProgress){
   const summary=brief(),completion=assessCompletion(o,contract);
   console.error(JSON.stringify({...summary,missing:completion.missing.length}));
   writeFileSync(new URL('../'+label+'-public-progress.json',import.meta.url),JSON.stringify({summary,memory:m,observation:o,completion,scope:'Public diagnostic inputs only; not a resumable game or random-state checkpoint.'},null,2)+'\n');
   nextProgress=o.elapsedMs+1800000;
   // Diagnostic stop only: preserve the original horizon and all earlier actions.
   if(o.elapsedMs>=95400678){status='censored-prefix';break;}
  }
  if(requested>remaining)break;
  if(decisions%100===0)await new Promise(resolve=>setImmediate(resolve));
 }
 if(firstCompletionMs!==null)status='complete';else if(interrupted)status='interrupted';else if(decisions>=50000000||sameTime>=1000000)status='budget';
}catch(cause){status='error';error={name:cause.name,message:cause.message,stack:cause.stack};}
const final=session.exportSummary({includeObservation:true});o=final.observation;
const result={schemaVersion:1,status,error,scope:'Genuine new-save observation-only fixed controller. No injected resources, save retries, future outcomes or seeded timing search. Summary-only Node/LCG diagnostic; not an expected-time or optimality certificate.',
 checkpointSemantics:'native-action-and-timer-boundaries-v1',config,environment,horizon,policySha256,summary:brief(),firstCompletionMs,
 completion:assessCompletion(o,contract),stages,memory:m,observation:o,audit:session.exportSummary()};
writeFileSync(new URL('../'+label+'-result.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({status,error,summary:result.summary,missing:result.completion.missing.length}));

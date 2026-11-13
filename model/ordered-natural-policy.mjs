import { readFileSync } from 'node:fs';
import { completionPolicySource } from './completion-policy.mjs';
import { recoveryTailPolicySource, NATURAL_TAIL_MAINTENANCE, NATURAL_TAIL_ACHIEVEMENTS, NATURAL_TAIL_PREFIX_ACHIEVEMENTS } from './recovery-tail-policy.mjs';
import { finalRunPolicySource } from './final-run-policy.mjs';
import { veilPolicySource } from './veil-policy.mjs';
import { saturationFundingPolicySource } from './saturation-funding-policy.mjs';
import { productionPolicySource } from './production-policy.mjs';
import { RESEARCH_UPGRADES } from './season-policy.mjs';
const catalogue = JSON.parse(readFileSync(new URL('./catalogue.json', import.meta.url)));
const requirements = JSON.parse(readFileSync(new URL('./completion-requirements.json', import.meta.url)));
const resetGoals = ['Rebirth','Resurrection','Reincarnation','All the stars in heaven','No more room in hell','Debt evasion',
  'Hardcore','Neverclick','A wizard is you','And a little extra',"Speed's the name of the game (no it's not it's called Cookie Clicker)","What's not clicking"];
const preFinalGoals = ['Eldeer','Wrath cookie','Early bird','Fading luck',"Black cat's paw","Baby it's old outside"];

/** Ordered candidate. Its finite-mean route and optimality remain unproved. */
export function orderedNaturalPolicySource({ saturation = {}, targetBank = 2 ** 304 } = {}) {
  if (!Number.isFinite(targetBank) || targetBank < 2 ** 90 || targetBank > 2 ** 936) throw new RangeError('Invalid ordered-route target bank.');
  const base = { clickRate: 50, inputBatchMilliseconds: 1000, lowEffects: true, farmSugar: false,
    gardenEnabled: false, ripeLumpsOnly: true, minimumFarmLevel: 10, allowFinalCollection: false,
    finalPreparation: false, deferVeil: true, buildingAmountLimit: 700,
    market: { collectTrades: false },
    combo: { configureAuras: false, castHandOfFate: false, godzamok: false },
    ascension: { assignPermanentSlots: false, finalRunCookies: 2 ** 286 } };
  const resources = completionPolicySource({ ...base, season: { naturalSeasons: true, research: false, eldeer: false } });
  const elder = completionPolicySource({ ...base, season: { naturalSeasons: true, research: true, eldeer: true } });
  return `(function(){
    const resources=(${resources}), elder=(${elder}), tail=(${recoveryTailPolicySource()});
    const prepare=(${finalRunPolicySource({released:true,allowReset:true,boundarySupplied:false})});
    const veil=(${veilPolicySource({released:true})});
    const fund=(${saturationFundingPolicySource(saturation)});
    const finalFund=(${saturationFundingPolicySource({...saturation,restoreTarget:1000})});
    const produce=(${productionPolicySource({finalCollection:true,clickRate:50})});
    const research=${JSON.stringify(RESEARCH_UPGRADES)}, resetGoals=${JSON.stringify(resetGoals)}, preFinalGoals=${JSON.stringify(preFinalGoals)};
    const gods=${JSON.stringify(catalogue.pantheon.gods)};
    const requiredNames=${JSON.stringify(requirements.requiredAchievements.map(a=>a.name))};
    const tailNames=${JSON.stringify(NATURAL_TAIL_ACHIEVEMENTS)}, mandatoryPrefix=${JSON.stringify(NATURAL_TAIL_PREFIX_ACHIEVEMENTS)};
    return function(o,a,memory){
      const m={phase:'resources',...(memory||{})};
      const reply=(status,stage,action=null,extra={})=>({status,stage,action,memory:m,...extra});
      const wait=(stage,ms=1000)=>reply('waiting',stage,{type:'wait',milliseconds:ms});
      const won=n=>!!o.achievements?.[n],p=o.progression;
      const levelReady=Object.entries({Cursor:12,Farm:10,Temple:1,'Wizard tower':1,Bank:1}).every(([n,l])=>p.buildingLevels[n]>=l);
      const resetReady=o.ascensions>=100 && resetGoals.every(won) && o.ascension.heavenlyUpgrades.every(u=>u.bought);
      const produced=[...(o.production?.bankAchievements||[]),...(o.production?.cpsAchievements||[]),...(o.production?.handmadeAchievements||[]),
        ...o.shop.buildings.flatMap(b=>[...b.countAchievements,...b.productionAchievements])].map(a=>a.name);
      const covered=new Set([...tailNames,...produced,'Thick-skinned']);
      const prefixMissing=[...new Set([...requiredNames.filter(n=>!covered.has(n)),...mandatoryPrefix.filter(n=>n!=='Thick-skinned')])].filter(n=>!won(n));
      const inTransition=p.onAscend||p.ascendTimer||p.reincarnateTimer;
      // All source mutations remain in the chosen controllers. These gates use
      // public accomplishments, never a seed, predicted drop, or failed outcome.
      if(m.highestAscensions!==undefined && (o.ascensions<m.highestAscensions || m.hardcore && !won('Hardcore')))
        return wait('maintenance-restoration');
      // Before the first challenge award no ordinary reset is released and
      // research is withheld. Native current-save export/load preserves this
      // finite earned number; a fresh pre-load realm has lost it temporarily.
      if(!m.hardcore && !won('Hardcore') && o.ascensions===0 && m.openingEarned!==undefined && o.cookiesEarned<m.openingEarned)
        return wait('opening-maintenance-restoration');
      if(!m.hardcore && !won('Hardcore') && o.ascensions===0)m.openingEarned=o.cookiesEarned;
      m.highestAscensions=Math.max(m.highestAscensions||0,o.ascensions);m.hardcore=!!(m.hardcore||won('Hardcore'));
      if(m.phase==='tail'){
        const d=tail(o,a,{...(m.tail||{}),released:true});m.tail=d.memory;
        return reply(d.status,'tail/'+d.stage,d.action,{tailBoundary:d.status==='needs-entry'?d:null});
      }
      if(m.phase==='final-reset'){
        const d=prepare(o,a,m.finalReset);m.finalReset=d.memory;
        if(d.action)return reply(d.status,'planned-final-reset',d.action);
        if(d.status!=='complete')return reply(d.status,'planned-final-reset',null,{reason:d.reason});
        m.phase='veil';
      }
      if(m.phase==='veil'){
        const d=veil(o,a,m.veil);m.veil=d.memory;
        if(d.action)return reply(d.status,'direct-veil',d.action);
        if(d.status!=='complete')return reply(d.status,'direct-veil',null,{reason:d.reason});
        m.phase='rebuild'; delete m.prefix; delete m.fund;
      }
      if(m.phase==='rebuild'){
        if(inTransition || !p.minigames.Temple || !o.controls.pantheon)return wait('rebuild-native-readiness');
        if(o.controls.promptOn)return wait('rebuild-unowned-prompt');
        if(o.controls.menu)return reply('acting','rebuild-view',{type:'open-menu',menu:''});
        const P=o.controls.pantheon;
        const other=P.slots.findIndex((id,slot)=>id>=0 && (slot!==0 || id!==2));
        if(other>=0){const god=gods.find(g=>g.id===P.slots[other]);return reply('acting','fixed-pantheon',{type:'pantheon-slot',god:god.key,slot:-1});}
        if(P.slots[0]!==2){if(!(P.swaps>0))return wait('pantheon-swap');return reply('acting','fixed-pantheon',{type:'pantheon-slot',god:'ruin',slot:0});}
        if(o.dragon.aura!==0 || o.dragon.aura2!==0)return reply('blocked','unexpected-final-aura');
        if(m.fund && !['complete','interrupted'].includes(m.fund.phase)){
          const d=(m.restoreFullCursors?finalFund:fund)(o,a,m.fund);m.fund=d.memory;
          if(d.action)return reply(d.status,'final-funding',d.action);
          if(d.status==='blocked')return reply('blocked','final-funding',null,{reason:d.reason});
          delete m.fund;
        }
        if(o.dragon.nextCanUpgrade)return reply('acting','rebuild-dragon',{type:'upgrade-dragon'});
        const view={...o,shimmers:o.shimmers.filter(s=>s.type!=='golden'),shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!research.includes(u.name))}};
        const d=produce(view,a,m.production);m.production=d.memory;
        if(d.action && d.action.type!=='wait')return reply(d.status,'deterministic-rebuild',d.action);
        const board=o.shop.buildings.every(b=>b.amount>=b.goalAmount);
        if(board && o.cookies>=${JSON.stringify(targetBank)} && o.dragon.level>=27){m.phase='tail';return wait('tail-release',1);}
        if(o.cookies>=2**90 && o.upgrades['Plastic mouse']?.bought){
          const cursor=o.shop.buildings.find(b=>b.id===0);m.restoreFullCursors=board || cursor.goalPurchase.price<=o.cookies/4;
          const f=(m.restoreFullCursors?finalFund:fund)(o,a,{});m.fund=f.memory;
          if(f.action)return reply(f.status,'final-funding',f.action);
          if(f.status==='blocked')return reply('blocked','final-funding',null,{reason:f.reason});
        }
        // The ordinary post-reset activation/starting buildings must create
        // the first2^90. This delegates actual purchases/clicks, not resources.
        const inner={...(m.rebuildGrowth||{}),ascension:{config:{allowReset:false,assignPermanentSlots:false}},misc:{deferVeilToPreparation:true}};
        const fallback=resources(view,a,inner);m.rebuildGrowth=fallback.memory;
        if(['ascend','reincarnate','market-loan'].includes(fallback.action?.type))return reply('blocked','unplanned-final-reset');
        return reply('acting','rebuild-growth',fallback.action);
      }
      const prefixExclusive=m.prefix?.spellReset?.active || m.prefix?.earlyFunding?.phase && !['complete','interrupted'].includes(m.prefix.earlyFunding.phase)
        || m.prefix?.combo?.rebuy || m.prefix?.helperSetup?.active || m.prefix?.season?.helperReleaseAt != null
        || m.prefix?.season?.helperPress || o.controls.mouseDown;
      if(m.fund && !['complete','interrupted'].includes(m.fund.phase)){
        const d=fund(o,a,m.fund);m.fund=d.memory;
        if(d.action)return reply(d.status,'prefix-saturation',d.action);
        if(d.status==='blocked')return reply('blocked','prefix-saturation',null,{reason:d.reason});
        delete m.fund;m.nextFunding=o.elapsedMs+1000;
      }
      if(!prefixExclusive && !inTransition && !o.controls.promptOn && !o.controls.menu){
        if(o.garden?.ready && !o.garden.freeze)return reply('acting','freeze-prefix-garden',{type:'sequence',actions:[{type:'minigame-open',id:2},{type:'garden-freeze'}]});
        const level=[['Temple',1],['Farm',1],['Farm',3],['Wizard tower',1],['Bank',1],['Cursor',12],['Farm',10]].find(([n,l])=>p.buildingLevels[n]<l);
        if(level){const b=o.shop.buildings.find(b=>b.name===level[0]);if(b.amount>0 && o.lumps>=b.level+1)return reply('acting','guaranteed-level-prefix',{type:'level-building',id:b.id});}
        if(m.phase==='resources' && levelReady && resetReady && preFinalGoals.filter(n=>!['Eldeer','Wrath cookie'].includes(n)).every(won))m.phase='elder';
        if(m.phase==='elder' && levelReady && resetReady && preFinalGoals.every(won) && prefixMissing.length===0 && o.dragon.level>=27 && o.prestige>=2**82){
          m.phase='final-reset';m.finalReset={};return wait('release-one-final-reset',1);
        }
        if(resetReady && won('A wizard is you') && o.prestige<2**82 && o.ascension.prestigeIfAscend>=2**82)
          return reply('acting','planned-prestige-floor',{type:'ascend'});
        if(o.cookies>=2**90 && o.upgrades['Plastic mouse']?.bought && o.elapsedMs>=(m.nextFunding||0)
          && o.controls.pantheon?.slots?.[0]===2 && !(levelReady && resetReady && o.prestige>=2**82)){
          const d=fund(o,a,{});m.fund=d.memory;if(d.action)return reply(d.status,'prefix-saturation',d.action);
        }
      }
      const withheld=m.phase==='resources'?research:[];
      const view={...o,shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!withheld.includes(u.name))}};
      m.prefix={...(m.prefix||{}),season:{...(m.prefix?.season||{}),config:{...(m.prefix?.season?.config||{}),naturalSeasons:true,research:m.phase==='elder',eldeer:m.phase==='elder'}}};
      const d=(m.phase==='resources'?resources:elder)(view,a,m.prefix);m.prefix=d.memory;
      return reply('acting',m.phase+'/'+d.stage,d.action);
    };
  })()`;
}
export function orderedNaturalPlan(options={}) { return {maintenanceReload:{...NATURAL_TAIL_MAINTENANCE},policySource:orderedNaturalPolicySource(options),
  status:'unproved-ordered-new-save-candidate',changesFrozenExperiment:false}; }

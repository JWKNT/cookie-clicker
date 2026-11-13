import { readFileSync } from 'node:fs';
import { baselinePolicySource } from './baseline-policy.mjs';
import { gardenPolicySource } from './garden-policy.mjs';
import { marketPolicySource } from './market-policy.mjs';
import { miscPolicySource } from './misc-policy.mjs';
import { seasonPolicySource } from './season-policy.mjs';
import { ascensionPolicySource } from './ascension-policy.mjs';
import { productionPolicySource } from './production-policy.mjs';
import { comboPolicySource } from './combo-policy.mjs';
import { grimoireResetPolicySource } from './grimoire-reset-policy.mjs';
import { finalRunPolicySource } from './final-run-policy.mjs';
import { veilPolicySource } from './veil-policy.mjs';
import { helperSetupPolicySource } from './helper-setup-policy.mjs';
import { earlyFundingPolicySource } from './early-funding-policy.mjs';
import { HELPER_ART_EXCLUSIONS } from './helper-cover.mjs';

const catalogue = JSON.parse(readFileSync(new URL('./catalogue.json', import.meta.url)));
const requirements = JSON.parse(readFileSync(new URL('./completion-requirements.json', import.meta.url)));

/**
 * Compose native subsystem controllers against the full completion target.
 * This is an experimental schedule, without a full completing trajectory or
 * certified expected completion time. A subsystem's success is not completion.
 * It preserves the first-run conditions for Neverclick and Hardcore.
 */
export function completionPolicySource({ clickRate = 20, inputBatchMilliseconds = 300, garden = {}, market = {}, season = {}, ascension = {}, production = {}, combo = {}, earlyFunding = {}, lowEffects = false, farmSugar = true, spellReset = true, finalPreparation = true, helperSetup = season.helperGrandma ?? true, withholdEarlyPrestigeActivation = false, preserveChallengeAchievements = true, gardenEnabled = true, ripeLumpsOnly = false, minimumFarmLevel = 9, allowFinalCollection = true, deferVeil = null, buildingAmountLimit = null } = {}) {
  if (![gardenEnabled, ripeLumpsOnly, allowFinalCollection].every(value => typeof value === 'boolean')
    || !Number.isInteger(minimumFarmLevel) || minimumFarmLevel < 9 || minimumFarmLevel > 12
    || deferVeil !== null && typeof deferVeil !== 'boolean'
    || buildingAmountLimit !== null && (!Number.isInteger(buildingAmountLimit) || buildingAmountLimit < 1 || buildingAmountLimit > 2000)) {
    throw new RangeError('Invalid completion-route restrictions.');
  }
  const growth = baselinePolicySource({ clickRate, inputBatchMilliseconds });
  const singleGrowth = baselinePolicySource({ clickRate });
  const noClickGrowth = baselinePolicySource({ clickRate: 0 });
  const gardenSource = gardenPolicySource(garden);
  const marketSource = marketPolicySource(market);
  const miscSource = miscPolicySource();
  const seasonSource = seasonPolicySource({ preserveChallengeAchievements, ...season });
  const ascensionOptions={allowReset:true,preserveChallengeAchievements,earlyCountResets:true,earlyResetCookieTarget:2**90,...ascension};
  const ascensionSource = ascensionPolicySource(ascensionOptions);
  const productionSource = productionPolicySource({ clickRate, preserveChallengeAchievements, ...production });
  const comboSource = comboPolicySource({ clickRate, preserveChallengeAchievements, ...combo });
  const slotId = catalogue.achievements.find(a => a.name === 'Here you go').id;
  return `(function () {
    const grow = (${growth});
    const earlyGrow = (${baselinePolicySource({clickRate,inputBatchMilliseconds:1000,purchaseIntervalMilliseconds:1000})});
    const earlyNoClick = (${baselinePolicySource({clickRate:0,purchaseIntervalMilliseconds:1000})});
    const growSingle = (${singleGrowth});
    const growWithoutClicks = (${noClickGrowth});
    const tend = (${gardenSource});
    const trade = (${marketSource});
    const collectMisc = (${miscSource});
    const collectSeason = (${seasonSource});
    const ascend = (${ascensionSource});
    const produce = (${productionSource});
    const combine = (${comboSource});
    const fund = (${earlyFundingPolicySource({clickRate,...earlyFunding})});
    const earlyFundingEnabled = ${JSON.stringify((earlyFunding.enabled ?? true) && (earlyFunding.clickRate ?? clickRate) > 0)};
    const lowEffects = ${JSON.stringify(lowEffects)};
    const resetSpells = (${grimoireResetPolicySource()});
    const prepareFinalRun = (${finalRunPolicySource()});
    const finishVeil = (${veilPolicySource()});
    const finalPreparationEnabled = ${JSON.stringify(finalPreparation && (ascension.allowReset ?? true))};
    const setupHelper = (${helperSetupPolicySource()});
    const helperSetupEnabled = ${JSON.stringify(helperSetup)};
    const helperArtExclusions = ${JSON.stringify(HELPER_ART_EXCLUSIONS)};
    const spellResetEnabled = ${JSON.stringify(spellReset)};
    const resetPermission = ${JSON.stringify(ascension.allowReset ?? true)};
    const earlyCountDefault = ${JSON.stringify(ascensionOptions.earlyCountResets)};
    const withholdActivation = ${JSON.stringify(withholdEarlyPrestigeActivation)};
    const activationNames=['Heavenly chip secret','Heavenly cookie stand','Heavenly bakery','Heavenly confectionery','Heavenly key'];
    const clickRate = ${JSON.stringify(clickRate)};
    const normalNames = ${JSON.stringify(catalogue.achievements.filter(a => a.normal).map(a => a.name))};
    const requiredNames = ${JSON.stringify(requirements.requiredAchievements.map(a => a.name))};
    const preserveChallenges = ${JSON.stringify(preserveChallengeAchievements)};
    const farmSugar = ${JSON.stringify(farmSugar)};
    const gardenEnabled = ${JSON.stringify(gardenEnabled)};
    const ripeLumpsOnly = ${JSON.stringify(ripeLumpsOnly)};
    const minimumFarmLevel = ${JSON.stringify(minimumFarmLevel)};
    const allowFinalCollection = ${JSON.stringify(allowFinalCollection)};
    const deferVeil = ${JSON.stringify(deferVeil)};
    const buildingAmountLimit = ${JSON.stringify(buildingAmountLimit)};
    const collectTradesOverride = ${JSON.stringify(market.collectTrades ?? null)};
    const minimumSacrifices = ${JSON.stringify(garden.sacrificesRequired ?? 1)};
    const naturalCookieFarm = ${JSON.stringify(garden.naturalCookieFarm ?? true)};
    return function (o, actions, memory) {
      const m = { ...(memory || {}) };
      // The final zero-building veil phase must have no flat production.
      // The normal quoted "egg" upgrade is still bought in final collection.
      if(finalPreparationEnabled && Array.isArray(o.ascension?.permanentCandidates))
        o={...o,ascension:{...o.ascension,permanentCandidates:o.ascension.permanentCandidates.filter(u=>u.name!=='"egg"')}};
      const earlyCountPhase=(m.ascension?.config?.allowReset ?? resetPermission)
        && (m.ascension?.config?.earlyCountResets ?? earlyCountDefault) && o.ascensions<100;
      // Optional diagnostic restriction for the older zero-prestige-effect profile.
      // Native profitable-reset and Lucky conditions do not require this hold.
      if(earlyCountPhase && withholdActivation)o={...o,shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!activationNames.includes(u.name))}};
      // The exhaustive helper certificate has exactly two Christmas artworks.
      // Preserve that pool, including across permanent-slot assignments.
      const needHelperSetup=helperSetupEnabled && !m.spellReset?.active && (m.season?.config?.helperGrandma ?? true) && !o.achievements["Baby it's old outside"];
      if(needHelperSetup)o={...o,shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!helperArtExclusions.includes(u.name))},
        ascension:{...o.ascension,permanentCandidates:(o.ascension.permanentCandidates || []).filter(u=>!helperArtExclusions.includes(u.name))}};
      const answer = (action, stage) => {
        let at=o.elapsedMs,lastClick=null;
        for(const input of action.type==='sequence' ? action.actions : [action]) {
          if(input.type==='wait')at+=input.milliseconds;
          if(input.type==='click')lastClick=at;
        }
        if(lastClick!==null && clickRate>0) {
          const next=lastClick+1000/clickRate;
          if(m.growth)m.growth={...m.growth,nextClick:next};
          if(m.combo)m.combo={...m.combo,nextClickAt:next};
          if(m.production)m.production={...m.production,nextClickAt:next};
        }
        return {action, memory:m, stage, optimalityCertified:false};
      };
      const wait = (milliseconds, stage) => answer({type:'wait',milliseconds},stage);
      const runFunding = (reserve=0) => {
        if(!m.earlyFunding?.phase)m.fundingReserve=reserve;
        const view={...o,cookies:Math.max(0,o.cookies-(m.fundingReserve||0))};
        const decision=fund(view,actions,m.earlyFunding);m.earlyFunding=decision.memory;
        if(decision.status==='blocked')throw new Error('Early funding source boundary: '+decision.reason);
        if(decision.action)return answer(decision.action,'early-income-burst');
        if(decision.status==='complete'||decision.status==='interrupted'){
          delete m.earlyFunding;delete m.fundingReserve;m.nextFundingAt=o.elapsedMs+1000;
          if(m.growth)m.growth={...m.growth,nextPurchase:o.elapsedMs};
          // A current-save reload may discard inputs and restore the original
          // buff arguments. Retain its actual state and give restoration time.
          if(decision.status==='interrupted')return wait(1000,'early-income-interrupted');
        }
        return null;
      };
      const runSpellReset = () => {
        const state={...(m.spellReset || {}),config:{allowReset:spellResetEnabled && resetPermission && (m.ascension?.config?.allowReset ?? true),
          ascensionReady:true,collectionStarted:!!m.finalCollectionStarted}};
        const decision=resetSpells(o,actions,state);m.spellReset=decision.memory;
        if(decision.status==='blocked')throw new Error('Spell-reset source boundary: '+decision.reason);
        return decision.action ? answer(decision.action,'spell-count-resets') : null;
      };
      const runFinalPreparation = () => {
        const state={...(m.finalRun || {}),config:{released:true,allowReset:resetPermission && (m.ascension?.config?.allowReset ?? true),
          boundarySupplied:m.spellReset?.phase==='complete'}};
        const finalDecision=prepareFinalRun(o,actions,state);m.finalRun=finalDecision.memory;
        if(finalDecision.status==='blocked')throw new Error('Final-run source boundary: '+finalDecision.reason);
        if(finalDecision.action)return answer(finalDecision.action,'final-run-preparation');
        if(finalDecision.status!=='complete')return null;
        const veilDecision=finishVeil(o,actions,{...(m.veil || {}),config:{released:true}});m.veil=veilDecision.memory;
        if(veilDecision.status==='blocked')throw new Error('Direct veil source boundary: '+veilDecision.reason);
        if(veilDecision.action)return answer(veilDecision.action,'direct-veil');
        if(veilDecision.status==='complete')m.finalPreparationComplete=true;
        return null;
      };
      const p = o.progression;
      // The next burst returns Cursors to its fixed batch. Invest ordinary
      // growth in other buildings while that income phase is available.
      const growthBuildings = () => earlyFundingEnabled && !m.finalCollectionStarted && p.minigames.Temple
        && o.controls.pantheon?.slots?.[0]===2 && o.upgrades['Plastic mouse']?.bought
        && o.shop.buildings.some(b=>b.name==='Temple'&&b.amount>0)
        ? o.shop.buildings.map(b=>b.id===0?{...b,locked:true}:b) : o.shop.buildings;
      const inTransition=!!(p.onAscend || p.ascendTimer || p.reincarnateTimer);
      // A fresh maintenance realm can expose its initial values before loading
      // the current save. Ordinary resets retain these observed milestones.
      if ((m.run!==undefined && o.ascensions<m.run) || (m.hardcoreObserved && !o.achievements.Hardcore))
        return wait(1000,'current-save-restoration');
      m.hardcoreObserved=!!(m.hardcoreObserved || o.achievements.Hardcore);
      // Reincarnation resets current-run control state, but not achievements,
      // building levels, or the seed log. Never carry a stale prompt owner.
      if ((m.run !== undefined && m.run !== o.ascensions) || (m.wasInTransition && !inTransition)) {
        delete m.garden; delete m.market; delete m.season; delete m.growth; delete m.misc; delete m.production; delete m.combo;
        delete m.confirmOneMind;delete m.nextHelperBuilding;delete m.helperSetup;delete m.earlyFunding;delete m.nextFundingAt;delete m.fundingReserve;
      }
      m.run = o.ascensions;
      m.wasInTransition=inTransition;
      // Once selected, this phase owns every action through its final reset.
      // It observes count progress, but never chooses a schedule from spell outcomes.
      if(m.spellReset?.active) {
        const decision=runSpellReset();if(decision)return decision;
      }
      if(m.finalRun?.active || m.veil?.active){const decision=runFinalPreparation();if(decision)return decision;}
      if (p.onAscend || p.ascendTimer || p.reincarnateTimer) {
        const decision = ascend(o,actions,m.ascension); m.ascension=decision.memory;
        return decision.action ? answer(decision.action,'ascension') : wait(100,'ascension-blocked');
      }
      if(m.earlyFunding?.phase && m.earlyFunding.phase!=='complete'){const decision=runFunding();if(decision)return decision;}
      if (m.combo?.rebuy || m.combo?.confirmAura || m.combo?.auraRestore) {
        const decision=combine(o,actions,m.combo);m.combo=decision.memory;
        if(decision.action)return answer(decision.action,'combo-transaction');
        if(decision.exclusive)return wait(100,'combo-transaction-reserve');
      }
      // A controller can confirm only the prompt that it requested.
      if (m.confirmOneMind) {
        const pending=m.confirmOneMind;
        delete m.confirmOneMind;
        if (o.controls.promptOn && o.elapsedMs===pending.elapsedMs && o.upgrades['One mind']?.unlocked
          && !o.upgrades['One mind'].bought) return answer({type:'prompt',option:0},'research-confirmation');
      }
      if(m.confirmEarlyLevel) {
        const pending=m.confirmEarlyLevel;delete m.confirmEarlyLevel;
        if(o.controls.promptOn && o.elapsedMs===pending.elapsedMs && p.buildingLevels.Temple===pending.level)
          return answer({type:'prompt',option:0},'early-income-temple-confirmation');
      }
      if (o.controls.promptOn) {
        const owner = m.garden?.confirmSacrifice ? ['garden',tend]
          : m.season?.confirm ? ['season',collectSeason]
          : m.misc?.giftPending ? ['misc',collectMisc] : null;
        if (!owner) return wait(100,'unowned-prompt');
        const decision=owner[1](o,actions,m[owner[0]]); m[owner[0]]=decision.memory;
        return decision.action ? answer(decision.action,owner[0]) : wait(100,'unowned-prompt');
      }
      if (m.season?.helperPress || m.season?.helperReleaseAt != null) {
        const decision=collectSeason(o,actions,m.season); m.season=decision.memory;
        if (decision.action) return answer(decision.action,'season-pointer');
      }

      // Fixed presentation preferences reduce diagnostic work. They never depend
      // on a seed, a sampled outcome, or a search over future random events.
      if(lowEffects && !m.lowEffectsReady){
        const pref=['fancy','particles','numbers'].find(name=>o.controls.preferences[name]);
        if(pref)return answer({type:'preference',name:pref},'presentation-setup');
        if(o.controls.volume!==0)return answer({type:'volume',channel:'sound',value:0},'presentation-setup');
        m.lowEffectsReady=true;
      }
      if(lowEffects && o.achievements["Baby it's old outside"] && !m.helperEffectsRestored){
        if(o.controls.preferences.fancy)return answer({type:'preference',name:'fancy'},'presentation-setup');
        m.helperEffectsRestored=true;
      }

      if (!o.achievements["What's in a name"]) return answer({type:'name-bakery',name:'Completion Bakery'},'interface-achievements');
      if (!o.achievements['Tiny cookie']) return answer({type:'tiny-cookie'},'interface-achievements');
      if (!o.achievements['Here you go']) return answer({type:'achievement-slot',id:${slotId}},'interface-achievements');
      if (!o.achievements['Olden days']) return answer({type:'forgotten-madeleine'},'interface-achievements');
      if (!o.achievements['Tabloid addiction']) {
        if (!m.newsViewport) { m.newsViewport=true; return answer({type:'resize',width:1200,height:900},'interface-achievements'); }
        return answer({type:'click-news'},'interface-achievements');
      }
      if (!o.achievements['Stifling the press']) {
        if (!m.narrowViewport) { m.narrowViewport=true; return answer({type:'resize',width:800,height:900},'interface-achievements'); }
        return answer({type:'click-news'},'interface-achievements');
      }
      if (!m.restoreViewport) { m.restoreViewport=true; return answer({type:'resize',width:1200,height:900},'interface-achievements'); }
      if (o.controls.menu) return answer({type:'open-menu',menu:''},'interface-achievements');

      if(needHelperSetup) {
        const helperDecision=setupHelper(o,actions,m.helperSetup);m.helperSetup=helperDecision.memory;
        if(helperDecision.status==='blocked')throw new Error('Helper setup source boundary: '+helperDecision.reason);
        if(helperDecision.action)return answer(helperDecision.action,'two-art-helper-setup');
        if(helperDecision.status==='needs-resources') {
          const next=earlyGrow({...o,shop:{...o.shop,buildings:growthBuildings()}},actions,m.growth);m.growth=next.memory;
          return answer(next.action,'two-art-helper-funding');
        }
      }

      if(earlyCountPhase) {
        // Keep the early funding/count phase separate from unbounded collection.
        // Ripe nonmeaty harvests fund Temple1 without an unripe success trial.
        if(o.lump?.available && o.lump.ageMs>=o.lump.ripeAge && o.lump.ageMs<o.lump.overripeAge)
          return answer({type:'harvest-lump'},'early-income-lump');
        const temple=o.shop.buildings.find(b=>b.name==='Temple');
        if(temple?.amount>0 && temple.level===0 && o.lumps>=1) {
          m.confirmEarlyLevel={elapsedMs:o.elapsedMs,level:temple.level};
          return answer({type:'level-building',id:temple.id},'early-income-temple');
        }
        const decision=ascend(o,actions,m.ascension);m.ascension=decision.memory;
        if(decision.action && decision.action.type!=='wait')return answer(decision.action,'early-profitable-ascensions');
        if(temple?.amount>0 && p.minigames.Temple && o.controls.pantheon?.open===false)
          return answer({type:'minigame-open',id:temple.id},'early-income-pantheon');
        if(earlyFundingEnabled && temple?.amount>0 && p.minigames.Temple && o.elapsedMs>=(m.nextFundingAt||0)){
          const decision=runFunding();if(decision)return decision;
        }
        if(temple?.amount>0 && p.minigames.Temple) {
          const comboState={...(m.combo || {}),config:{...(m.combo?.config || {}),configureAuras:false,castHandOfFate:false,reserveCookies:0}};
          const decision=combine(o,actions,comboState);m.combo=decision.memory;
          if(decision.action)return answer(decision.action,'early-income-combo');
          if(decision.exclusive)return wait(100,'early-income-combo-reserve');
        }
        const needHardcore=preserveChallenges && !o.achievements.Hardcore;
        const needNeverclick=preserveChallenges && !o.achievements.Neverclick;
        const growthView={...o,decisionHorizonMs:1000,shop:{...o.shop,buildings:growthBuildings().map(b=>buildingAmountLimit!==null && b.amount>=(b.id===0?1000:buildingAmountLimit)?{...b,locked:true}:b),upgrades:needHardcore?[]:o.shop.upgrades.filter(u=>temple?.level>0 || u.name!=='One mind')}};
        const next=(needNeverclick?(o.cookieClicks>=15?earlyNoClick:growSingle):earlyGrow)(growthView,actions,m.growth);
        m.growth=next.memory;
        if(next.action.type==='buy-upgrade' && o.upgrades['One mind']?.id===next.action.id)
          m.confirmOneMind={elapsedMs:o.elapsedMs};
        return answer(next.action,needHardcore || needNeverclick?'challenge-achievements':'early-income-growth');
      }

      m.misc={...(m.misc || {}),deferGrandmaSaleUntilHardcore:preserveChallenges,
        deferVeilToPreparation:deferVeil ?? (finalPreparationEnabled && (m.ascension?.config?.allowReset ?? true))};
      const miscDecision=collectMisc(o,actions,m.misc); m.misc=miscDecision.memory;
      if (miscDecision.action) return answer(miscDecision.action,'misc');
      // Fading luck needs one cookie left on screen until its last second.
      // Only the owning controller can click that cookie during the hold.
      const held = new Set(miscDecision.deferShimmerIds || []);
      const publicObservation={...o,shimmers:o.shimmers.filter(s=>!held.has(s.id))};

      if (o.lump?.available && o.lump.ageMs >= (ripeLumpsOnly || o.achievements['Hand-picked'] ? o.lump.ripeAge : o.lump.matureAge)
        && o.lump.ageMs < o.lump.overripeAge) return answer({type:'harvest-lump'},'sugar-resources');

      // A finite access schedule, not a claim about optimal lump allocation.
      const levels=[['Farm',1],['Farm',3],['Wizard tower',1],['Temple',1],['Bank',1],['Farm',9],['Cursor',12],['Farm',minimumFarmLevel]];
      const target=levels.find(([name,level])=>p.buildingLevels[name]<level);
      if (target) {
        const b=o.shop.buildings.find(b=>b.name===target[0]);
        if (b?.amount>0 && o.lumps>=b.level+1) return answer({type:'level-building',id:b.id},'finite-unlocks');
      }
      // The last milk is unlocked at 600 normal achievements. The required
      // set plus the mandatory Cursor level gives only 599 in the worst case.
      const needsMilkLevel = !target && requiredNames.every(name=>o.achievements[name])
        && normalNames.filter(name=>o.achievements[name]).length<600 && p.buildingLevels.Farm===9;
      if (needsMilkLevel && o.lumps>=10) {
        return answer({type:'level-building',id:2},'milk-unlock');
      }

      const ascensionDecision=ascend(o,actions,m.ascension); m.ascension=ascensionDecision.memory;
      if (ascensionDecision.action && ascensionDecision.action.type!=='wait') return answer(ascensionDecision.action,'ascension');
      if(spellResetEnabled && ascensionDecision.status==='complete' && !m.finalCollectionStarted
        && !o.achievements['A wizard is you']) {
        const decision=runSpellReset();if(decision)return decision;
      }

      if(finalPreparationEnabled && ascensionDecision.status==='complete' && !m.finalCollectionStarted && !m.finalPreparationComplete
        && (!spellResetEnabled || o.achievements['A wizard is you'])) {
        const decision=runFinalPreparation();if(decision)return decision;
      }

      m.season={...(m.season || {}),config:{...(m.season?.config || {}),
        suppressWrathForCookieCount:naturalCookieFarm && ascensionDecision.status==='complete'}};
      const seasonDecision=collectSeason(publicObservation,actions,m.season); m.season=seasonDecision.memory;
      if (seasonDecision.action && seasonDecision.action.type!=='wait') return answer(seasonDecision.action,'season');
      if (seasonDecision.status==='needs-ascension' && !earlyCountPhase && m.ascension.config.allowReset
        && (!preserveChallenges || o.achievements.Hardcore && o.achievements.Neverclick)) {
        return answer({type:'ascend'},'season-retry');
      }
      const finalCollection=allowFinalCollection && ascensionDecision.status==='complete' && seasonDecision.status==='complete'
        && (!spellResetEnabled || o.achievements['A wizard is you'])
        && (!finalPreparationEnabled || m.finalPreparationComplete);
      if(finalCollection)m.finalCollectionStarted=true;
      // The seasonal controller owns reindeer timing for Eldeer. Growth must
      // not immediately click a reindeer that this controller is holding.
      const growthShimmers=publicObservation.shimmers.filter(s=>s.type!=='reindeer');

      if (farmSugar && o.garden?.ready) {
        const finalLevels={Farm:9,'Wizard tower':1,Temple:1,Bank:1,Cursor:12};
        const levelCost=Object.entries(finalLevels).reduce((sum,[name,goal])=>{
          const now=Math.min(goal,p.buildingLevels[name]);
          return sum+(goal*(goal+1)-now*(now+1))/2;
        },needsMilkLevel ? 10 : 0);
        const harvests=Math.ceil(Math.max(0,levelCost-o.lumps)/10);
        m.garden={...(m.garden || {}),config:{...(m.garden?.config || {}),
          sacrificesRequired:Math.max(minimumSacrifices,o.garden.convertTimes+harvests)}};
      }
      m.garden={...(m.garden || {}),config:{...(m.garden?.config || {}),naturalCookieFarm:naturalCookieFarm && finalCollection}};
      const gardenDecision=gardenEnabled ? tend(o,actions,m.garden) : {status:'deferred',action:null,memory:m.garden};
      if (gardenDecision.action && gardenDecision.action.type!=='wait') {
        m.garden=gardenDecision.memory;
        return answer(gardenDecision.action,'garden');
      }
      m.garden=gardenDecision.memory;
      // Reserve an explicitly requested planting cost. Otherwise the growth
      // controller can spend every cookie and starve the Garden indefinitely.
      let reserve=Math.max(gardenDecision.status==='needs-resources' ? gardenDecision.requiredCookies || 0 : 0,
        miscDecision.status==='needs-resources' ? miscDecision.requiredCookies || 0 : 0,
        seasonDecision.status==='needs-resources' ? seasonDecision.requiredCookies || 0 : 0);
      const marketObservation={...o,cookies:Math.max(0,o.cookies-reserve)};
      m.market={...(m.market || {}),config:{...(m.market?.config || {}),
        collectTrades:collectTradesOverride ?? finalCollection}};
      const marketDecision=trade(marketObservation,actions,m.market);
      m.market=marketDecision.memory;
      if (marketDecision.status==='budget-exhausted') throw new Error('Stock Market controller decision budget exhausted');
      if (marketDecision.action && marketDecision.action.type!=='wait') {
        let action=marketDecision.action;
        if (reserve>0 && action.type==='market-buy' && action.amount===10000) {
          // Native 10000 means Max, not a numerical order size. Bound the
          // transaction using the unreserved bank before calling that API.
          const good=o.market.goods.find(g=>g.id===action.id);
          let amount=Math.min(9999,good.maxStock-good.stock,Math.floor(marketObservation.cookies/good.buyCookiePrice));
          while (amount>0 && good.buyCookiePrice*amount>marketObservation.cookies) amount--;
          if (amount<1) return wait(100,'market-reserve');
          action={...action,amount};
        }
        return answer(action,'market');
      }
      if (marketDecision.status==='needs-resources') reserve+=marketDecision.requiredCookies || 0;

      // Native office costs and seasonal sprite goals need particular buildings.
      // An income ranking alone need not ever choose those buildings.
      const request=[marketDecision,seasonDecision,gardenDecision].find(d=>d.building && d.amount>p.buildingAmounts[d.building]);
      if (request) {
        const b=o.shop.buildings.find(b=>b.name===request.building);
        if (b && !b.locked && b.buy1price<=o.cookies-reserve &&
          (request!==seasonDecision || o.elapsedMs>=(m.nextHelperBuilding || 0))) {
          if (request===seasonDecision) m.nextHelperBuilding=o.elapsedMs+34;
          return answer({type:'buy-building',id:b.id,amount:1},'required-building');
        }
        if (b && !b.locked) reserve=Math.max(reserve,b.buy1price);
      }

      m.production={...(m.production || {}),config:{...(m.production?.config || {}),finalCollection}};
      const productionDecision=produce({...o,cookies:Math.max(0,o.cookies-reserve)},actions,m.production);
      m.production=productionDecision.memory;
      if (productionDecision.action && productionDecision.action.type!=='wait') return answer(productionDecision.action,'production');
      if (productionDecision.status==='needs-resources') reserve=Math.max(reserve,productionDecision.requiredCookies || 0);

      // Continue the same real income controller through later prestige growth.
      // Final current building holdings are collected after this phase ends.
      if(earlyFundingEnabled && !m.finalCollectionStarted && ascensionDecision.status!=='complete'
        && o.elapsedMs>=(m.nextFundingAt||0)){
        const decision=runFunding(reserve);if(decision)return decision;
      }

      m.combo={...(m.combo || {}),config:{...(m.combo?.config || {}),reserveCookies:reserve,deferredShimmerIds:[...held]}};
      const comboDecision=combine(o,actions,m.combo);m.combo=comboDecision.memory;
      if(comboDecision.action)return answer(comboDecision.action,'combo');
      if(comboDecision.exclusive)return wait(100,'combo-transaction-reserve');

      // These goals use native callbacks and never inspect a spell's outcome.
      if (o.santa?.canUpgrade && o.cookies-o.santa.price>=reserve) return answer({type:'upgrade-santa'},'santa');
      if (o.dragon?.nextCanUpgrade && reserve===0) return answer({type:'upgrade-dragon'},'dragon');
      const grimoire=o.controls.grimoire;
      if (p.minigames['Wizard tower'] && grimoire && !o.achievements['A wizard is you']) {
        // These spells always finish their callback. A cheaper unavailable
        // spell can refund its cost and leave the policy in a zero-time loop.
        const safeSpells=['conjure baked goods','hand of fate',"haggler's charm",'summon crafty pixies','diminish ineptitude'];
        const spell=Object.entries(grimoire.spells).filter(([key,s])=>safeSpells.includes(key) && s.cost<=grimoire.magic-(comboDecision.reserveMagic || 0)
          && !(reserve>0 && key==='conjure baked goods'))
          .sort((a,b)=>a[1].cost-b[1].cost || a[0].localeCompare(b[0]))[0];
        if (spell) return answer({type:'cast-spell',spell:spell[0]},'spell-count');
      }
      const needHardcore=preserveChallenges && !o.achievements.Hardcore;
      const needNeverclick=preserveChallenges && !o.achievements.Neverclick;
      const decisionHorizonMs=Math.min(miscDecision.wakeAfterMs || 1000,
        gardenDecision.action?.type==='wait' ? gardenDecision.action.milliseconds : 1000,
        marketDecision.action?.type==='wait' ? marketDecision.action.milliseconds : 1000,
        seasonDecision.action?.type==='wait' ? seasonDecision.action.milliseconds : 1000,
        productionDecision.action?.type==='wait' ? productionDecision.action.milliseconds : 1000);
      const growObservation={...o,decisionHorizonMs,shimmers:growthShimmers,cookies:Math.max(0,o.cookies-reserve),shop:{...o.shop,
        buildings:growthBuildings().map(b=>buildingAmountLimit!==null && b.amount>=(b.id===0?1000:buildingAmountLimit)?{...b,locked:true}:b),upgrades:needHardcore ? [] : o.shop.upgrades}};
      const next=(needNeverclick ? (o.cookieClicks>=15 ? growWithoutClicks : growSingle) : grow)(growObservation,actions,m.growth);
      m.growth=next.memory;
      if (next.action.type==='wait' && gardenDecision.action?.type==='wait') {
        next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,gardenDecision.action.milliseconds)};
      }
      if (next.action.type==='wait' && marketDecision.action?.type==='wait') {
        next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,marketDecision.action.milliseconds)};
      }
      if (next.action.type==='wait') next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,
        miscDecision.wakeAfterMs || 1000,seasonDecision.action?.type==='wait' ? seasonDecision.action.milliseconds : 1000,
        productionDecision.action?.type==='wait' ? productionDecision.action.milliseconds : 1000)};
      if (next.action.type==='buy-upgrade' && o.upgrades['One mind']?.id===next.action.id) {
        m.confirmOneMind={elapsedMs:o.elapsedMs};
      }
      return answer(next.action,needHardcore || needNeverclick ? 'challenge-achievements' : 'growth');
    };
  })()`;
}

import { GARDEN_RECIPES, GARDEN_DROP_CROPS } from './garden-policy.mjs';
import { RESEARCH_UPGRADES, DRAGON_DROPS } from './season-policy.mjs';

// This is a manifest-linked proof plan. Neither a target mapping nor a local
// positive event establishes a proper policy for the composed native game.
export const COLLECTION_STEPS = Object.freeze({
  challenge: {
    source: ['main.js:16323-16330', 'main.js:4766-4797'],
    program: 'Make 15 accepted clicks and buy one Cursor. Without buying upgrades or making more cookie clicks, buy one each Grandma, Farm, Mine, Factory, Bank, Temple and Wizard tower when affordable. Wait until 1e9 cookies have been baked and the five-second native check has run before buying upgrades.',
    localArgument: 'bootstrap-route-witness.json records the genuine 15-click/one-Cursor prefix, then separate purchase, challenge and ripe-lump boundary fixtures. JavaScriptCounterLadder proves the joint bank/earned arithmetic and purchase guards for the eight-stage ladder within 6660050 passive credits. JavaScriptThresholdBridge proves the native canLumps comparison on its stated entry heap. The eight production invariants, actual initialization, complete purchase/Logic callbacks and scheduling remain open; the recorded boundary fixtures do not execute the whole ladder.',
    open: ['Refine actual initialization and all eight no-upgrade production boards through CalculateGains and Logic', 'Compose complete native purchases, earned-counter updates and canLumps with the initialized game heap and frame schedule'],
  },
  income: {
    source: ['main.js:4683-4748', 'main.js:7830-7901', 'main.js:16303-16307'],
    program: 'Use the low-bank Cursor sale/rebuy growth construction, then the funded native income ladder; buy 1000 Cursors and 700 of every other building, restore sacrifices, and cross each production counter threshold.',
    localArgument: 'income-route-witness.json records native affordable purchases, actual ascensions, click ULP margins and all 20 final production-counter crossings.',
    open: ['Discharge initial funding, rebuild funding and finite macro endpoints', 'Uniform resource and CpS bounds over arbitrary retry epochs'],
  },
  ascension: {
    source: ['main.js:3461-3546', 'main.js:3968-3989', 'main.js:4117-4142', 'main.js:10894-10900'],
    program: 'Complete 100 early ascensions, each with at least 2^90 earned cookies and a strictly positive finite native prestige gain. Buy the affordable heavenly-power activation upgrades during rebuilding. Include an ascension during an active loan. Later forfeit the largest required cookie amount and buy heavenly upgrades in parent order. Enter the prestige-display interval [7777000000,7777999999] for all three Lucky upgrades.',
    localArgument: 'A reset increments Game.resets only when gainedPrestige>0. The candidate permits prestige activation by default; neither the native reset counter nor Lucky visibility requires withholding it. The funded reset ledger does not supply new-save income or a uniform rebuild proof. Lucky visibility tests string digits. Every integer in the stated interval has four leading 7 digits; its width avoids reliance on hitting a single late-game prestige integer. Its native cookie preimage and click-step bound remain open.',
    open: ['A funded native schedule hitting the Lucky display intervals', 'Uniform bounded rebuilding after a failed collection epoch'],
  },
  sugar: {
    source: ['main.js:4412-4432', 'main.js:4465-4538'],
    program: 'Keep elderWrath zero while generating lumps. Obtain and spend 136 gross ripe lumps: 78 on Cursor 12, 55 on Farm 10 and one on each other minigame building. After both the early helper sweep and Lucky purchases, retry Hand-picked at the observed mature age plus 1 ms.',
    localArgument: 'The unripe choose([0,1]) uses one free IID53 draw, so its success mass is exactly 1/2. After a possibly inherited meaty lump is discarded, wrath zero excludes new meaty types. Every other ripe type yields at least one lump, regardless of seeded type correlations. All native non-debug ripe thresholds are at most 23 hours.',
    event: { handPickedNumerator: '1', handPickedDenominator: '2', maximumMatureWaitMs: 72000001, grossLevelLumps: 136 },
    open: ['Clock/type callback refinement and preservation of the free RNG phase'],
  },
  garden: {
    source: ['minigameGarden.js:638-703', 'minigameGarden.js:1820-1837', 'minigameGarden.js:1850-1981'],
    program: 'Use the ordered 33 recipes below on dirt with no Supreme Intellect aura. Stagger parent planting so required mature parents coexist around one empty tile. Harvest each mature novel plant. Complete the log, sacrifice once, rebuild it, harvest 1000 mature plants, and mature a full 36-tile thumbcorn plot.',
    localArgument: 'garden-cylinders-witness.json records all 33 recipes, a native sacrifice, all 33 recipes again, all seven purchased drops, a full plot and 1009 mature harvests. The independent fixed-tape replay uses 4925 Garden ticks and 171505 IID53 draws. Its event mass in that callback harness is 2^-9089765. The public policy cannot select this tape. The two-pass harvest-all recovery removes even maximal meddleweed replacement branches.',
    open: ['Refine exact-deadline Garden callback jumps to full native waits, including intervening random draws', 'Uniform resource and maturation invariants at every retry entry', 'Kernel source refinement of the callback and recovery traces'],
  },
  gardenDrops: {
    source: ['minigameGarden.js:612-618', 'minigameGarden.js:1097-1101', 'minigameGarden.js:1456'],
    program: 'After the seed log is rebuilt, grow each of the seven drop crops in isolation, harvest at maturity, and buy its missing upgrade. Retry a failed mature harvest.',
    localArgument: 'At dropRateMult>=1 each per-harvest drop rate is at least its table value; every rate is >=0.001. The dyadic interval [0,1/1024) is a success event. The Garden fixed-tape witness includes the mature harvest and purchase of each drop; it does not yet account for all intervening full-game callbacks.',
    event: { conditionalSuccessAtMatureHarvest: 'at least 1/1024' },
    open: ['Full-game refinement of the recorded maturation blocks', 'Uniform planting affordability or a proved bank-ULP absorption invariant'],
  },
  market: {
    source: ['minigameMarket.js:196-255', 'minigameMarket.js:548', 'minigameMarket.js:762-799', 'minigameMarket.js:803-984'],
    program: 'During retry epochs, stop at office4 and reach750 highest of each goods building after the golden-count phase; storage is then at least750+250=1000. Wait for You price >=189, then buy exactly1000 of all18 goods and liquidate after the buy/sell guard resets. Trade1000 You shares repeatedly: buy at price<=117, sell at price>=189, with overhead<=1.2. Upgrade office5 only after all stochastic collection succeeds and no further reset is planned.',
    localArgument: 'The first high-price You purchase exceeds 86400 dollars; a forced high sale does likewise. Each low/high trade earns at least 48600 dollars before binary64 error. Under the existing market-recurrence bounds, a falling/rising forcing block uses 1032 ticks and at most 337464 market draws. A strict 45000-dollar lower bound would cover roundoff. An initial debit <=5.5e9 plus 122445 profitable cycles exceeds 1e7 profit. This route uses 1000 shares, not an 86401-share storage assumption. The larger Gaseous assets goal is a shadow.',
    event: { proposedCycleGainDollars: 45000, sufficientCyclesAfterInitialDebit: 122445, maximumInitialDebitDollars: 5500000000,
      forcingTicksFromExistingLemma: 1032, forcingDrawsFromExistingLemma: 337464 },
    open: ['Source refinement of the existing market recurrence', 'Native per-trade rounding and storage guards', 'Uniform cookie funding, including the raw-CpS-highest exchange rate', 'Preserve the visible office-upgrade button on retries: drawT saturation can retain display:none after resetting an office5 run'],
  },
  research: {
    source: ['main.js:10200-10245', 'main.js:16222-16241', 'main.js:16444-16447'],
    program: 'Buy the ten research-chain upgrades in order, wait for each research timer, confirm One mind, and reach Elder Pact. Buy ten Elder Pledges with expiration or Covenant/revoke between them; buy Covenant once, revoke it for wrinkler work, and buy Sacrificial rolling pins.',
    localArgument: 'Research and pledge timers are finite. Ownership of normal research upgrades is compatible with the historical access union for mutually exclusive covenant controls.',
    open: ['A native funded ordering for all research and pledge guards'],
  },
  wrinklers: {
    source: ['main.js:14340-14385', 'main.js:14417-14466'],
    program: 'At elderWrath 3, wait for a wrinkler, allow it to attach and store positive cookies, and pop 200. For Wrinkler poker, poke one live wrinkler 50 times with enough recovery between pokes.',
    localArgument: 'With no negative spawn modifiers, one designated empty slot has a spawn event of mass at least 2^-17 per frame. Attachment takes a bounded number of frames. Poking subtracts 0.75 HP; the chosen recovery schedule must preserve HP above 0.5.',
    event: { designatedSlotSpawnPerFrame: 'at least 1/131072' },
    open: ['Native hover/hit-testing and HP recovery timing', 'A bounded pop block preserving positive stored payout'],
  },
  christmas: {
    source: ['main.js:5760-5866', 'main.js:10260-10296', 'main.js:14990-15070'],
    program: 'Activate Christmas, buy the festive hat, buy each Santa drop before the next level, reach Santa 14 and buy Santa dominion. Catch 200 counted reindeer and purchase all seven reindeer cookies.',
    localArgument: 'At dropRateMult>=1 a specific missing reindeer cookie has a conservative success mass >=1/64 per pop. Reindeer timer maxima are finite. Santa draws from the remaining drop list; the exact depletion and final-level logic must be checked in the composed trace.',
    event: { specificReindeerDropPerPop: 'at least 1/64' },
    open: ['A successful bounded 24-hour season block and retry-epoch preservation'],
  },
  halloween: {
    source: ['main.js:14482-14514'],
    program: 'During Halloween, pop attached wrinklers with stored payout >0.5 and buy all seven Halloween cookies.',
    localArgument: 'With dropRateMult>=1, use a drop draw in [255/256,1) and a chosen-cookie bucket of mass >=1/8. A specified missing cookie therefore has success mass >=1/2048 per qualifying pop.',
    event: { specificDropPerQualifyingPop: 'at least 1/2048' },
    open: ['The wrinkler block obligations', 'A successful bounded season block rather than indefinitely increasing seasonUses'],
  },
  easter: {
    source: ['main.js:10413-10460', 'main.js:14513', 'main.js:16356-16366'],
    program: 'During Easter, pop qualifying wrinklers and buy each newly unlocked egg until all 20 are owned. Do not pop golden cookies during this post-count collection phase.',
    localArgument: 'For a qualifying wrinkler pop, [255/256,1) passes failRate<=0.98. A desired rare/common branch and a bucket in a list of at most 32 entries give a conservative specified-egg mass >=1/262144. Existing eggs are not required to be rerolled for this chosen first-hit event.',
    event: { specificEggPerQualifyingPop: 'at least 1/262144' },
    open: ['The wrinkler block obligations', 'A bounded successful season block and native egg prices'],
  },
  valentines: {
    source: ['main.js:10300-10335', 'main.js:16331-16355'],
    program: 'Activate Valentines after the cookie thresholds are funded, run native checks, and buy all heart cookies.',
    localArgument: 'This chain uses cookie thresholds and purchases, with no rare-drop fairness premise.',
    open: ['Native full-chain purchase ordering'],
  },
  fortunes: {
    source: ['main.js:6986-6992', 'main.js:7565-7604', 'main.js:7630-7652', 'main.js:16369-16378'],
    program: 'Own Fortune cookies and wait for automatic ticker changes. Click visible fortunes and buy each fortune upgrade. Do not manually refresh the ticker to create opportunities.',
    localArgument: 'Automatic changes occur every ten seconds. The fortune branch has mass >=1/64 and its pool has at most 27 entries, so any specified still-locked fortune has mass >=1/4096 per eligible change. Already unlocked entries leave the pool.',
    event: { specifiedFortunePerEligibleTicker: 'at least 1/4096', automaticTickerSeconds: 10 },
    open: ['Bounded epoch opportunities and final five-second ownership check'],
  },
  dragon: {
    source: ['main.js:14760-14820', 'main.js:14890-14910'],
    program: 'Buy dragon access, train through level 27 using the native cookie/building costs, then restore all sacrificed building amounts. Leave aura choices compatible with the collection bounds.',
    localArgument: 'Training spends 31 million cookies and sacrifices 100 of each building, then 50 of each and 200 of each: 350 per building in total. Restoring each sacrifice before the next purchase keeps the board below the proposed 2000-per-building envelope.',
    open: ['Native funded training and restoration ledger'],
  },
  pets: {
    source: ['main.js:14943-14975'],
    program: 'Start with all four dragon drops absent. In each of four distinct quarter-hour phases, pet until its previously unseen drop unlocks, buy it, then advance to the next phase.',
    localArgument: 'The seeded shuffle is one fixed permutation of four drops. The independent trigger has mass >=1/32 per pet. Known-empty phase retries complete almost surely at that same timestamp with finitely many inputs; no independent seeded-drop assumption is used.',
    event: { petTrigger: 'at least 1/32', phases: 4, totalPhaseAdvanceMsAtMost: 2700000 },
    open: ['Establish absence/known phase status after reset and permanent slots', 'Composed source semantics for the almost-sure finite zero-time retry macro'],
  },
  helper: {
    source: ['main.js:8299-8310', 'main.js:8380-8440', 'main.js:8466-8477', 'main.js:8722-8743'],
    program: 'Before buying Grandma artwork upgrades in a fresh Christmas run, buy 24 Grandmas and execute helperSweepActions: a fixed 3350ms grid sweep, with no seed or private sprite-position inputs. Do this before any unbounded retry phase.',
    localArgument: 'helper-seeds-witness.json exhaustively covers all 11881376 startup seeds. Each two-art Christmas display has an elf among indices 0 through 23; ubyju is the unique worst seed. The grid points hit every possible jittered hitbox, and the worst-seed native fixture wins. This is finite native evidence, not a kernel-checked all-seed theorem.',
    open: ['Kernel-check the exhaustive certificate and refine its ARC4/normalization projection to source', 'Prove the legal early entry setup and draw schedule; drawT still cannot be allowed to saturate before this finite sweep'],
  },
  golden: {
    source: ['main.js:5189-5279', 'main.js:5396-5423', 'main.js:5729-5738'],
    program: 'In a fresh run with elderWrath0 and no research purchases, keep golden switch off, the Garden empty and dragon auras off. Hold 1000 Cursors and at most700 of every other building; do not take loans, activate Sugar frenzy, slot scorn or click the big cookie. Click 7777 timer-created leaders, with one immediate click for Early bird and one final-second click for Fading luck. Wrath cookie is completed in the earlier Eldeer phase. Stop popping golden cookies, let accumulated buffs expire, and refill resources.',
    localArgument: 'Only spawnLead cookies count. Every native leader arrives by its finite maximum timer, including chain leaders. With the stated empty Garden and auras0, the maximum duration multiplier is2.4495818395400004 and the longest base production effect is77 seconds. A conservative240 seconds per pop gives a post-count drain budget of55,994,401 logic frames for golden-created production/click buffs. Do not wait for unrelated Sugar blessing, which can be renewed by later lumps. Native modifier cases and callback scheduling still need refinement.',
    open: ['A native bound on all timer modifiers along this setup', 'Pointer observability and final-second scheduling', 'Post-count resource rebuilding'],
  },
  eldeer: {
    source: ['main.js:5427-5453', 'main.js:5530-5560', 'main.js:5790-5798'],
    program: 'Before the final collection epoch, during Christmas and elder wrath, arrange an overlap of a natural wrath leader and a reindeer. Click the wrath cookie, which also completes Wrath cookie; if it produces Elder frenzy, click the reindeer before the buff ends. Reincarnate before the later wrath0 counted-cookie phase.',
    localArgument: 'Do Lucky first, then attempt Eldeer while withholding ordinary frequency upgrades and frequency auras. Wait out Sugar blessing and use an empty Garden. Heavenly luck alone gives a golden interval (4.75 minutes,14.25 minutes]. After a golden leader expires, pop the first reindeer at time r<=6 minutes+4 seconds; its next interval (r+3 minutes,r+6 minutes] intersects that golden interval. Choose an interior frame as a probability event, suppress earlier spawns, select Elder frenzy, and pop the reindeer. The policy watches visible shimmers and cannot select the draws. Failed bounded attempts can use ordinary resets without invalidating already-owned Lucky upgrades.',
    open: ['Native full-trace refinement of the joint-timer cylinder', 'Its full IID53 mass and finite-attempt duration', 'Uniform funded rebuilding of the early Eldeer retry phase'],
  },
  grimoire: {
    source: ['minigameGrimoire.js:14-41', 'minigameGrimoire.js:264-286', 'minigameGrimoire.js:305-337', 'minigameGrimoire.js:476-482', 'main.js:3560-3619', 'main.js:16380-16386'],
    program: 'Count one affordable Conjure Baked Goods cast before each of the 100 early profitable ascensions once Wizard tower level1 is available. After the required high-prestige growth, but before final ownership and Garden setup, finish the remaining casts with a fixed ordinary reset cycle. With Starter kit and Starter kitchen, wait5100ms after reincarnation, buy Heavenly chip secret, wait200ms, buy one Wizard tower, and make one Conjure cast. Ascend on either outcome, use Escape, wait40ms and reincarnate. Complete the final reincarnation after the999th persistent cast.',
    localArgument: 'Native level1 reset supplies magic5; the one-tower Conjure cost is4. Both source outcomes finish and increment spellsCastTotal; failure spends bank cookies but does not decrease cookiesEarned, and Reset clears Clot. grimoire-reset-route-witness.json completes999 such cycles in5335760ms from one explicit1e57-cookie/one-lump boundary, with no later funding and both outcomes observed. Its native profitable-reset count stays1: these cycles do not replace the100 early profitable ascensions. The Wizard level is already in the136-lump ledger. No seeded success-frequency or favourable-outcome assumption is used.',
    open: ['Reach the funded normal-run entry through the actual new-save source route', 'Prove the starter-income, five-second unlock and cycle timing bounds uniformly over the stated retained upgrades and public entry conditions', 'Refine the legal native input controls and complete notification/Reset callbacks; this finite diagnostic is not a full-game completion certificate'],
  },
  interface: {
    source: ['main.js:4766-4797', 'main.js:6440-6960', 'main.js:7625-7635', 'main.js:15300-15600'],
    program: 'Use the existing guarded native actions to rename the bakery, click the small statistics cookie and Here you go achievement, click 50 ticker stories, compress the ticker, scroll to the old-cookie footer, sell one Grandma, dunk the cookie by resizing, and send/redeem a self-addressed gift. Perform accepted clicks faster than 15/s for Uncanny clicker.',
    localArgument: 'These goals have finite ordinary UI actions; the gift code is a displayed native code. No hidden save data is needed.',
    open: ['Full source/action refinement and a composed native UI trace'],
  },
  veil: {
    source: ['main.js:4766-4797', 'main.js:11278-11309', 'main.js:11351-11369', 'main.js:16348'],
    program: 'After the heavenly, growth and spell-count phases, make the one precommitted final normal-run reset, independent of Thick-skinned, the seed and veil outcomes. Reuse the fixed final spell reincarnation only if it actually supplied this boundary. Keep cookieClicks at zero through activation. With Shimmering veil and all four defense upgrades owned, sell every starter building, wait for the native zero-production update, and require a visible zero-price veil toggle. Make consecutive accepted direct cookie clicks at counters 0 through 34, stopping when Thick-skinned is won; rebuy the free veil after each failure. Do not reset after a failed click. Exclude only the quoted "egg" upgrade from permanent slots and buy it later in final collection.',
    localArgument: 'veil-cover-witness.json retains exhaustive native evidence for all 11881376 five-letter startup seeds: one of counters 0 through 34 has a sufficient output below the four-upgrade defense, and the checked prefix has no zero initial six-byte ARC4 word. The source tests the veil before incrementing cookieClicks. The controller does not read a seed, select outcomes or assume independent seeded trials. The composed supplied-entry regression sells native starter buildings and buys zero-price toggles. Active final-run, spell and veil phases retain their memory and wait through scheduled maintenance prompts; this test does not prove a uniform reload bound. The finite certificate is not a Lean theorem or a new-save route.',
    event: { startupSeedsCoveredByNativeCertificate: 11881376, maximumSufficientCounter: 34, maximumAcceptedClicks: 35, failureResets: 0 },
    open: ['Kernel-check the complete finite certificate and refine its ARC4/normalization projection to source', 'Reach the untouched final normal-run boundary with the required heavenly upgrades and zero unbuffed CpS from a new save', 'Compose complete reset, maintenance, activation, sale, toggle-purchase, accepted-click and notification callbacks'],
  },
  milk: {
    source: ['main.js:16199-16223', 'main.js:12580-13680', 'main.js:10719-10724'],
    program: 'Finish all 598 retained normal achievements. Cursor level 12 necessarily adds its excluded level-10 achievement; Farm level 10 adds a second. Buy Fanciful dairy so all milk choices are exposed.',
    localArgument: '598+2=600 won normal flags meets the aggregate flag requirement. Milk choices also require the native AchievementsOwned counter to reach 600; Game.Win updates it after notification calls. This is why the route budgets Farm level 10 although the manifest requires level 9.',
    open: ['Composition with all other achievement proofs', 'Preserve the native AchievementsOwned counter through complete award callbacks; won flags alone do not establish milk access'],
  },
  unlocks: {
    source: ['main.js:16331-16530', 'minigameGarden.js:877-929', 'minigameMarket.js:526-549'],
    program: 'Record all17 toggle/selector accesses, including both sides of the switches and Covenant; keep all four minigames ready, all seeds,300+ Farms for all soils, all goods, all spell/god entries, dragon27 and Santa14. After all stochastic work is complete, make the final office4-to5 upgrade, restore its Cursor sacrifice, and run deterministic achievement/milk checks. End in normal mode, outside ascension and animations.',
    localArgument: 'Historical access handles exclusive toggles. Ordinary owned upgrades still require simultaneous current ownership.',
    open: ['Concrete final native snapshot and proof of the complete predicate'],
  },
});

export function buildCollectionRouteCandidate(coverage, requirements, seasonalGroups = {}) {
  const assignment = new Map();
  const names = (step, list) => { for (const name of list) assignment.set(name, step); };
  names('challenge', ['Hardcore', 'Neverclick']);
  names('sugar', ['Hand-picked', 'Dude, sweet', 'Sugar rush']);
  names('grimoire', ['Bibbidi-bobbidi-boo', "I'm the wiz", 'A wizard is you']);
  names('dragon', ['Here be dragon', 'A crumbly egg', 'Dragon cookie']);
  names('pets', DRAGON_DROPS);
  names('research', [...RESEARCH_UPGRADES, 'Sacrificial rolling pins', 'Elder nap', 'Elder slumber', 'Elder calm', 'Grandmapocalypse']);
  names('wrinklers', ['Itchscratcher', 'Wrinklesquisher', 'Moistburster', 'Wrinkler poker']);
  names('christmas', ['Coming to town', 'All hail Santa', 'Let it snow', 'Oh deer', 'Sleigh of hand', 'Reindeer sleigher', 'A festive hat', "Santa's dominion", ...(seasonalGroups.santa || []), ...(seasonalGroups.reindeer || [])]);
  names('halloween', ['Spooky cookies', ...(seasonalGroups.halloween || [])]);
  names('easter', ['The hunt is on', 'Egging on', 'Mass Easteria', 'Hide & seek champion', ...(seasonalGroups.easter || [])]);
  names('valentines', ['Lovely cookies', ...(seasonalGroups.valentines || [])]);
  names('fortunes', ['O Fortuna', ...(seasonalGroups.fortunes || [])]);
  names('helper', ["Baby it's old outside"]);
  names('eldeer', ['Eldeer', 'Wrath cookie']);
  names('veil', ['Thick-skinned']);
  names('golden', ['Golden cookie', 'Lucky cookie', 'A stroke of luck', 'Fortune', 'Leprechaun', "Black cat's paw", 'Early bird', 'Fading luck', 'Lucky day', 'Serendipity', 'Get lucky']);
  names('gardenDrops', GARDEN_DROP_CROPS.map(item => item.upgrade));
  const entries = [];
  const add = (category, key, step, nativeId) => {
    if (!COLLECTION_STEPS[step]) throw new Error(`Unmapped collection step: ${step}`);
    entries.push({ category, key, step, ...(nativeId === undefined ? {} : { nativeId }) });
  };
  const fallback = { production: 'income', baseline: 'income', ascension: 'ascension', garden: 'garden', market: 'market', misc: 'interface', completion: 'interface' };
  for (const item of coverage.achievements) add('achievement', item.name, assignment.get(item.name) || fallback[item.controller], item.id);
  for (const item of coverage.upgrades) add('ownedUpgrade', item.name, assignment.get(item.name) || (item.controller === 'ascension' ? 'ascension' : item.controller === 'baseline' ? 'income' : undefined), item.id);
  for (const item of requirements.accessUpgrades) add('accessUpgrade', item.name, ['Elder Pledge', 'Elder Covenant', 'Revoke Elder Covenant'].includes(item.name) ? 'research' : 'unlocks', item.id);
  add('cosmeticUnlock', 'milkChoices', 'milk');
  add('progression', 'achievementsOwned', 'milk');
  for (const item of requirements.minigames) add('minigame', item.name, 'sugar');
  for (const item of requirements.buildingLevels) add('buildingLevel', item.building, 'sugar');
  for (const item of requirements.seeds) add('gardenSeed', item.key, 'garden', item.id);
  for (const item of requirements.soils) add('gardenSoil', item.key, 'unlocks', item.id);
  for (const item of requirements.marketGoods) add('marketGood', String(item.id), 'market', item.id);
  for (const item of requirements.loans) add('marketLoan', String(item.id), 'market', item.id);
  for (const item of requirements.spells) add('grimoireSpell', item.key, 'grimoire', item.id);
  for (const item of requirements.gods) add('pantheonGod', item.key, 'unlocks', item.id);
  for (const [key, step] of Object.entries({ dragonLevel: 'dragon', santaLevel: 'christmas', stockOfficeLevel: 'market', gardenLevel: 'sugar', ascensionMode: 'unlocks', onAscend: 'unlocks', ascendTimer: 'unlocks', reincarnateTimer: 'unlocks' })) add('progression', key, step);
  return {
    schemaVersion: 1, status: 'manifest-linked-candidate-with-open-obligations', sourceHashes: requirements.sourceHashes,
    proves: ['Every completion condition has an explicit candidate step'],
    doesNotProve: ['legal new-save reachability', 'finite expected full completion', 'optimality'],
    epochPlan: [
      'Finish the challenge and first nonmeaty ripe lump, reach the 2^90 bootstrap endpoint, and perform the early helper sweep before unbounded retries. Run the native drawT%5 product update with all20 store visibility requirements met before drawT saturates. Thereafter avoid screen-reader preference changes or other BuildStore calls: ordinary Reset retains those product classes, while BuildStore recreates every row as toggledOff. Normal upgrade unlocks rebuild through Logic without a drawT gate.',
      'Finish 136 gross level lumps, 100 early productive ascensions and the Lucky display interval. Then finish Eldeer and Wrath cookie using bounded attempts with only Heavenly luck among golden-frequency upgrades; do not place unbounded retries before the fixed Lucky interval. Complete the income ladder and fixed spell-count reset phase, preserving minigame levels across ordinary rebuilds. Supply one precommitted final normal-run boundary, reusing the fixed final spell reincarnation only when available. Then complete the zero-production direct Thick-skinned click prefix with no reset after a failed click, and start final current-ownership collection in that run.',
      'Within a candidate collection epoch, first finish the counted golden-cookie work with elderWrath0 and no research purchases, wait out its finite accumulated buffs, and refill. Do not pop any more golden cookies in that epoch. Then do research and ordinary wrinkler work, the four bounded seasonal windows, Garden collection, market trades, pets, automatic fortunes and final access actions. The persistent Grimoire cast goal is already complete. Easter drops use wrinklers only; a Fortune-generated golden cookie is left untouched.',
      'Use at most four season switches in an epoch. After its fixed failure deadline, ordinarily ascend and rebuild; do not assume repeated season renewal prices remain affordable. Keep office<=4 during all retry epochs, with750 highest of each goods building for1000-share capacity. The final office5 upgrade follows every stochastic goal, so its hidden upgrade button never has to be restored after reset.',
      'The successful branch can bound its 1000-share market segment by 231+1+122445*1032 minute ticks and its Garden segment by 4925 five-minute ticks. Full-game callback and funding bounds must still be composed.',
      'A single successful epoch must retain all current upgrades and finite unlocks. Achievements, levels and Garden seed knowledge can carry between epochs. Only uniform epoch duration and positive conditional success mass imply finite expected completion.',
    ],
    globalOpenObligations: [
      'The funded income ladder and all retry rebuilding premises remain unproved from a new save.',
      'Supply an explicit full successful native epoch, with a bounded IID draw cylinder, for every reachable retry-entry state.',
      'Prove uniform resource/price bounds under growing retry prestige and milk; no floating-point counter may silently stall below a needed goal.',
      'Handle native Game.T and drawT saturation: T resets on ordinary ascension, drawT does not. Source-refine the all-seed finite helper sweep before any unbounded retry phase.',
      'Refine the complete Garden callback cylinder, early Eldeer overlap construction and native market recurrence into the full operational model.',
      'Specify the accepted unbounded-clock calendar/string semantics and preserve native seeded correlations.',
    ],
    steps: COLLECTION_STEPS,
    gardenRecipes: GARDEN_RECIPES,
    gardenDrops: GARDEN_DROP_CROPS,
    veilDirectCover: {
      witness: 'model/veil-cover-witness.json',
      scope: 'exhaustive-native-evidence-not-kernel-proof',
      domainSize: 11881376,
      maximumSufficientCounter: 34,
      maximumAcceptedClicks: 35,
      certificateSha256: '6d8770c7f4dc48309d3f8cdaf5fa31831bb61cbe39eb4b7d1cb8c03f0a1afb33',
      resetSchedule: 'One final normal-run boundary fixed independently of Thick-skinned, the seed and veil outcomes; reuse the fixed final spell reincarnation only if it supplied that boundary.',
      resetsAfterFailedClick: 0,
      kernelChecked: false,
    },
    entries, conditionCount: entries.length,
  };
}

import { createRequire } from 'node:module';
import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { loadGameSource } from './game-source.mjs';
import { ACTION_TYPES } from './runtime.mjs';

// Acorn is already a dependency of the mod build. The report itself has no parser dependency.
const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const { parse } = require('acorn');
const symbol = n => !n ? '' : n.type === 'Identifier' ? n.name : n.type === 'ThisExpression' ? 'this' : n.type === 'Literal' ? String(n.value) : n.type === 'MemberExpression' ? `${symbol(n.object)}.${symbol(n.property)}` : '';
const value = n => n?.type === 'Literal' ? n.value : null;

const ranges = {
  'main.js': [
    [1,1900,'environment',[],'Global browser, mod and locale services; game mods and external loading are outside the vanilla policy.'],
    [1900,1986,'environment',[],'Sleep/resume and engine lifecycle remain environment operations; no retry load is exposed.'],
    [1987,2148,'implemented',['resize'],'Viewport resize invokes native callbacks with adapter pane geometry.'],
    [2149,2420,'implemented',['name-bakery'],'Bakery naming and startup notices.'],
    [2421,2656,'unresolved',[],'Tooltip, language and navigation inputs; not all pointer states are represented.'],
    [2657,3680,'partial',['export-save'],'Native current-save serialization and load run for immutable clock-scheduled maintenance. Current native export text may be inspected and decoded; save import, external transfer and outcome-retry reloads remain excluded. Full navigation refinement is unresolved.'],
    [3681,4070,'implemented',['buy-upgrade','achievement-slot','reincarnate','key'],'Crate and ascension selection surfaces; pointer tooltip effects remain an environment boundary.'],
    [4071,4370,'implemented',['ascend','reincarnate','key'],'Native ascension and animation controls.'],
    [4371,4800,'implemented',['harvest-lump','minigame-refill','prompt'],'Lump click and native confirmation dialogs.'],
    [4801,4928,'implemented',['click','key','visibility','wrinkler-hover','wrinkler-poke'],'Keyboard and targeted pointer inputs; arbitrary scroll/drag paths are not yet covered.'],
    [4929,6170,'implemented',['click-shimmer','wait'],'Shimmer interactions and autonomous production/buff transitions.'],
    [6171,6284,'unresolved',[],'Notification close controls affect rendering and sound; no specific action yet.'],
    [6285,6440,'implemented',['prompt','close-prompt','preference','volume'],'Native prompt and settings helpers.'],
    [6441,6537,'implemented',['open-menu'],'Menu and panel selection. Mobile panel layout is outside Steam desktop target.'],
    [6538,6544,'implemented',['tiny-cookie'],'Stats tiny-cookie click.'],
    [6545,6600,'partial',[],'Immutable clock-scheduled maintenance clicks the native same-English selection and saves current state before a fresh realm. Other locales and adaptive outcome-retry reloads are excluded.'],
    [6601,6682,'implemented',['open-menu','export-save','preference','volume','gift-send','gift-redeem'],'Visible Steam preference controls; screen-reader reload, cloud/OS actions and save import are excluded.'],
    [6683,6978,'implemented',['open-menu','forgotten-madeleine','achievement-slot'],'Info/stats menu interactions; external links do not change economic state.'],
    [6979,7700,'implemented',['click-news'],'News ticker and fortune click.'],
    [7701,8999,'implemented',['buy-building','sell-building','click-product','store-bulk','level-building','minigame-open','building-mute'],'Building economic inputs and display controls.'],
    [9000,9320,'implemented',['customizer-gene','customizer-random'],'Clone customization; customizer import/export is an unresolved alternate input path.'],
    [9321,9359,'implemented',['building-hover','building-mute'],'Building pointer entry is native; You-hover entry is policy-excluded except diagnostic mode.'],
    [9360,9820,'implemented',['buy-upgrade','upgrade-vault','buy-all-upgrades','select-cosmetic','prompt'],'Upgrade purchase, choice and native confirmation callbacks.'],
    [9821,10600,'implemented',['buy-upgrade','permanent-slot','prompt'],'Upgrade effects and permanent-slot selection.'],
    [10601,11849,'implemented',['buy-upgrade','select-cosmetic','prompt'],'Season, research and toggle effects entered through native upgrade purchases.'],
    [11850,11940,'unresolved',[],'Jukebox playback and track controls are only partly covered by select-cosmetic.'],
    [11941,12290,'implemented',['gift-send','gift-redeem'],'Native gift forms with cooldown; optional design/icon controls remain unmodeled.'],
    [12291,14298,'implemented',['buy-upgrade','achievement-slot','wait'],'Unlock and achievement callbacks, including dynamically assigned click functions.'],
    [14299,14849,'implemented',['wrinkler-hover','wrinkler-poke','wait'],'Native wrinkler input and autonomous updates.'],
    [14850,15164,'implemented',['upgrade-santa','upgrade-dragon','dragon-aura','pet-dragon','prompt'],'Santa and dragon native operations; direct special-menu positioning remains partial.'],
    [15165,15940,'environment',['resize','wait'],'Rendering and physics execute against partial DOM/canvas layout; toy dragging is unmodeled.'],
    [15941,16090,'excluded',[],'Developer console, grants, re-seeding and cheat actions are forbidden.'],
    [16091,16850,'autonomous',['wait'],'Native initialization, logic and drawing execute through scheduled callbacks.'],
    [16851,20000,'excluded',[],'Native startup executes with fixed English. Language-selection inputs remain outside that environment, and unpinned external scripts cannot be loaded.'],
  ],
  'minigameGarden.js': [[1,100000,'implemented',['garden-plant','garden-harvest','garden-harvest-all','garden-soil','garden-freeze','garden-sacrifice','minigame-refill','wait'],'Garden gameplay operations; selective harvest tools, seed selection and information controls require per-surface review.']],
  'minigameMarket.js': [[1,100000,'implemented',['market-buy','market-sell','market-office','market-broker','market-loan','wait'],'Market gameplay operations include native Max trades through amount 10000. Graph and row visibility controls remain partial.']],
  'minigamePantheon.js': [[1,100000,'implemented',['pantheon-slot','minigame-refill','wait'],'Native drag/drop semantic actions and swap refills; intermediate dragging remains partial.']],
  'minigameGrimoire.js': [[1,100000,'implemented',['cast-spell','minigame-refill','wait'],'Spell and refill handlers plus native autonomous magic recovery.']],
};

// Per-site audit of the formerly unclassified inputs. A partial entry is a known
// modeling obligation, not a claim that the input cannot affect later execution.
const reviewedSites = {
  'index.html:51': ['environment', [], 'The inline tiny-globe startup draw executes in page-script order before native window.onload. Language-link pointer entry would start its animation interval, but this web top-bar control is hidden in the fixed-English Steam environment.'],
  'index.html:89': ['mapped-family', ['close-prompt'], 'Visible prompt close button plays tickOff and closes the native prompt; promptNoClose guards the action.'],
  'index.html:150': ['mapped-family', ['tooltip-pointer'], 'Leaving the visible tooltip dispatches the native mouseout handler and calls Game.tooltip.hide.'],
  'main.js:2427': ['partial', ['tooltip-pointer'], 'Static crate handlers on identified controls preserve Game.onCrate, drawing, and wobble. Anonymous non-crate targets and full browser hit testing remain outside this input contract.'],
  'main.js:2428': ['partial', ['tooltip-pointer'], 'Static tooltip handlers on identified controls preserve entry and delayed hide. Anonymous callers and complete CSS visibility remain separate obligations.'],
  'main.js:2433': ['partial', ['tooltip-pointer'], 'Native dynamic crate handlers preserve Game.onCrate, held-pointer gating, callback drawing, and modifier updates. Identified controls and native stats type/data-id crates are supported; other anonymous targets and full hit testing remain partial.'],
  'main.js:2434': ['partial', ['tooltip-pointer'], 'Dynamic tooltip entry and leave dispatch native handlers on identified controls. Callback-specific effects, anonymous targets, and general pointer geometry are not exhaustively verified.'],
  'main.js:2444': ['partial', ['tooltip-pointer'], 'Attached native tooltip listeners are dispatched on identified controls; native herald text is checked. Caller visibility and full browser geometry remain partial.'],
  'main.js:2445': ['partial', ['tooltip-pointer'], 'Native attached tooltip leave sets shouldHide. The represented target transition leaves the old tooltip before entering another; complete browser pointer paths remain partial.'],
  'main.js:2535': ['excluded', [], 'HTTPS switch is inside if (!App), absent from the Steam target; it also navigates to a different save slot.'],
  'main.js:2541': ['excluded', [], 'Top-bar language click is inside if (!App), absent from the Steam target. Steam locale changes require the external wrapper and reload.'],
  'main.js:2612': ['mapped-family', ['export-save','prompt','close-prompt'], 'User-authorized current native Export save inspection. The Options anchor calls ExportSave and WriteSave1; the readonly visible textarea is observable, including its encoded startup seed. Import, edits and restoration remain excluded.'],
  'main.js:2618': ['excluded', [], 'Import-save prompt loads externally supplied state. Save editing and outcome-retry reloads are forbidden. Scheduled maintenance reloads use only the current native save, not this import control.'],
  'main.js:4852': ['mapped-family', ['click', 'cookie-pointer'], 'The existing click action invokes Game.ClickCookie directly. The pointer click phase dispatches the native big-cookie click listener, then bubbles to document; detail1 preserves the physical-pointer click throttle.'],
  'main.js:4853': ['mapped-family', ['cookie-pointer'], 'Native mousedown sets BigCookieState, optionally plays the cookie sound, and bubbles to the document mouseDown/clickFrom listener. Its incidental random draw is retained.'],
  'main.js:4854': ['mapped-family', ['cookie-pointer'], 'Native mouseup changes the cookie display state and bubbles to clear document mouseDown/clickFrom.'],
  'main.js:4855': ['mapped-family', ['cookie-pointer'], 'Native mouseout restores the cookie display state.'],
  'main.js:4856': ['mapped-family', ['cookie-pointer'], 'Native mouseover sets the hovered cookie display state; the enter action also dispatches native pointer coordinates at the visible cookie center.'],
  'main.js:6211': ['mapped-family', ['dismiss-note'], 'A visible notification close button plays tick and calls Game.CloseNote(id); native DOM handler is dispatched.'],
  'main.js:6218': ['mapped-family', ['dismiss-note'], 'The close-all notification control plays tick and calls Game.CloseNotes; available only when the native control exists.'],
  'main.js:11873': ['partial', ['jukebox-sound'], 'Jukebox choices render sound controls plus Steam Music controls. Sound callback is exposed, but the full menu depends on unpinned steam/steam.js Music initialization.'],
  'main.js:11880': ['mapped-family', ['jukebox-sound'], 'Previous sound invokes native setSound(onSound-1); explicit sound selection covers the resulting native callback.'],
  'main.js:11881': ['mapped-family', ['jukebox-sound'], 'Play current sound invokes native setSound(onSound). Audio itself is inert in the adapter.'],
  'main.js:11882': ['mapped-family', ['jukebox-sound'], 'Next sound invokes native setSound(onSound+1); explicit sound selection covers the resulting native callback.'],
  'main.js:11884': ['mapped-family', ['jukebox-sound'], 'Sound dropdown invokes native setSound with the selected index.'],
  'main.js:11889': ['partial', [], 'Random sound chooses an index with Math.random, then calls setSound. No random-sound action is exposed; deliberate RNG manipulation is forbidden, but ordinary UI effects still need a precise admissibility treatment.'],
  'main.js:11899': ['partial', [], 'Music play/pause delegates to external Steam Music and reads the audio paused state; this service is outside the eight pinned files.'],
  'main.js:11900': ['partial', [], 'Music loop toggles jukebox.trackLooped and delegates looping to external Steam Music.'],
  'main.js:11904': ['partial', [], 'Music scrub input/change writes external audio currentTime and starts a repeated time-display callback. Audio timing and callback interaction are not modeled.'],
  'main.js:11906': ['partial', [], 'Music Auto toggles trackAuto and cues external Music; track dropdown selects a track and may change playback, filters and looping. Both handlers require the external Music service.'],
  'main.js:11911': ['inactive', [], 'Shuffle markup is inside an HTML comment, so it is not an active native UI input. The adapter parser ignores comment descendants.'],
};

function disposition(file, line, kind, callee) {
  const reviewed = reviewedSites[`${file}:${line}`];
  if (reviewed) return { status: reviewed[0], actions: reviewed[1], note: reviewed[2], mappingScope: 'individual source callsite review; not a transition equivalence proof' };
  if (kind === 'timer') return { status: 'autonomous', actions: ['wait'], note: 'Native callback is scheduled by the deterministic timer adapter; asynchronous browser APIs remain environment assumptions.' };
  if (kind === 'rng-reset') return { status: 'environment', actions: [], note: 'Explicit seeded generator is native; unseeded reset resumes the injected tape. No policy receives future draws.' };
  if (kind === 'helper') return { status: 'helper', actions: [], note: 'Generic handler-construction helper; call sites require individual coverage.' };
  const row = ranges[file]?.find(([start,end]) => line >= start && line <= end);
  if (!row) return { status: 'unresolved', actions: [], note: 'No reviewed adapter mapping for this source surface.' };
  const [, , status, actions, note] = row;
  return { status: status === 'implemented' ? 'mapped-family' : status, actions, note, mappingScope: 'reviewed source region; not a per-callback equivalence proof' };
}

/** Static input-site inventory, not a completeness theorem for the DOM or game semantics. */
export function buildActionCoverage({ sourceDirectory } = {}) {
  const source = loadGameSource(sourceDirectory);
  const surfaces = [];
  const add = (file, node, kind, callee, extra = {}) => {
    const line = node.loc.start.line;
    surfaces.push({ id: `${file}:${line}:${node.loc.start.column}:${kind}`, file, line, column: node.loc.start.column,
      endLine: node.loc.end.line, kind, symbol: callee, ...extra, ...disposition(file, line, kind, callee) });
  };
  for (const [file, text] of Object.entries(source.sources)) {
    if (!file.endsWith('.js')) {
      text.split(/\r?\n/).forEach((line, i) => { if (/\bon(?:click|mouse\w+|touch\w+|key\w+|change|input)\s*=/i.test(line)) add(file, { loc: { start: { line: i + 1, column: 0 }, end: { line: i + 1 } } }, 'html-handler', 'inline HTML'); });
      continue;
    }
    const ast = parse(text, { ecmaVersion: 'latest', locations: true, allowReturnOutsideFunction: true });
    const visit = (node, parent) => {
      if (!node || typeof node !== 'object') return;
      if (node.type === 'CallExpression') {
        const name = symbol(node.callee);
        if (name === 'AddEvent' || name.endsWith('.addEventListener')) add(file, node, 'listener', name, { event: value(node.arguments[1]) ?? value(node.arguments[0]) });
        else if (['setTimeout','setInterval','requestAnimationFrame'].includes(name) || /\.(setTimeout|setInterval|requestAnimationFrame)$/.test(name)) add(file, node, 'timer', name);
        else if (name === 'Game.WritePrefButton') add(file, node, 'preference', name, { preference: value(node.arguments[0]), control: value(node.arguments[1]) });
        else if (name === 'Game.WriteSlider') add(file, node, 'slider', name, { control: value(node.arguments[0]) });
        else if (name === 'Game.Prompt') add(file, node, 'prompt', name);
        else if (name === 'Math.seedrandom') add(file, node, 'rng-reset', name, { explicitSeed: node.arguments.length > 0 });
      } else if (node.type === 'AssignmentExpression') {
        const name = symbol(node.left);
        if (/\.(clickFunction|activateFunction|choicesPick|choicesFunction|onclick|onmousedown|onmouseup|onkeydown|onkeyup|onchange|oninput)$/.test(name)) add(file, node, 'callback-property', name);
        else if (/^(Game\.(Logic|Loop|Draw|UpdateWrinklers|UpdateShimmers|doLumps|CalculateGains)|M\.logic)$/.test(name)) add(file, node, 'autonomous-step', name);
      } else if (node.type === 'MemberExpression' && symbol(node) === 'Game.clickStr') {
        add(file, node, 'generated-event-attribute', 'Game.clickStr');
      } else if (node.type === 'Literal' && typeof node.value === 'string') {
        const events = [...new Set([...node.value.matchAll(/\bon(click|mouse\w+|touch\w+|key\w+|change|input)\s*=/gi)].map(m => m[1].toLowerCase()))];
        if (events.length) add(file, node, 'generated-html-handler', 'string literal', { events });
      } else if (node.type === 'FunctionDeclaration' && ['AddEvent','FireEvent'].includes(node.id?.name)) add(file, node, 'helper', node.id.name);
      for (const [key, child] of Object.entries(node)) {
        if (key === 'loc') continue;
        if (Array.isArray(child)) { for (const item of child) if (item?.type) visit(item, node); }
        else if (child?.type) visit(child, node);
      }
    };
    visit(ast, null);
  }
  surfaces.sort((a,b) => a.file.localeCompare(b.file) || a.line - b.line || a.column - b.column || a.kind.localeCompare(b.kind));
  const counts = Object.fromEntries([...new Set(surfaces.map(s => s.status))].sort().map(status => [status, surfaces.filter(s => s.status === status).length]));
  return {
    schemaVersion: 1, gameVersion: '2.053', edition: 'steam', sourceHashes: source.hashes,
    scope: 'AST inventory of listener calls, generated HTML handler literals, prompt/preference/choice callbacks, timer calls and selected autonomous entry points in the eight pinned source files.',
    completenessClaim: false,
    caveats: ['Region mappings identify an implementation family, not verified callback equivalence.', 'Dynamic string concatenation, handler generation and browser layout require separate runtime evidence.', 'The policy action set combines UI events and guarded API operations. It neither enumerates all UI histories nor proves every API operation equivalent to one physical input.', 'The policy action set is still a reviewed subset; partial or unresolved entries must not be silently excluded from an optimality theorem.'],
    actionModelBoundary: {
      scope: 'Limits of this executable adapter, not restrictions proved sufficient for all-strategy comparison.',
      buildingPurchases: {
        source: 'main.js:7797-7854,8516-8542',
        nativeUiQuantities: [1, 10, 100],
        nativeUiMax: 'There is no buy-Max control. Selecting All in buy mode changes the quantity to100; All is visible only in sell mode.',
        guardedApiAmountRange: [1, 1000],
        guardedApiAffordability: 'buy-building requires the full getSumPrice quote. The native buy loop can still purchase fewer copies because it debits each rounded getPrice separately.',
        quoteVsDebit: 'getSumPrice rounds once after the raw sum and discounts. buy(amount) rounds and debits each copy. The quote is not an exact acquisition-cost certificate.',
        equivalenceLimit: 'Several smaller batches invoke sound and refresh callbacks more often and permit interleavings. No event-history equivalence is claimed.',
      },
      buildingSales: {
        source: 'main.js:7858-7905,8516-8542',
        nativeUiQuantities: [1, 10, 100, 'all'],
        nativeUiAllPath: ['store-bulk(id1)', 'store-bulk(id5)', 'click-product'],
        guardedApiAmountRange: 'Positive safe integers up to the current holding.',
      },
      otherLimits: [
        'market-buy and market-sell accept1..10000; native10000 is the Max/All sentinel, not a fixed numerical quantity.',
        'resize accepts width200..16384 and height100..16384; these are adapter resource limits, not a native maximum screen size.',
        'The policy sequence macro permits at most1000 inputs. It does not skip callbacks or infer an admissible infinite input sequence.',
        'Explicit cookie-pointer phases preserve the mapped native handlers; general pointer paths, capture, focus and drag semantics remain partial.',
        'tooltip-pointer supports native control IDs and statistics crates by type/data-id, dispatches existing handlers, and rejects selected CSS-hidden or covered controls. Anonymous non-crate targets and complete CSS hit testing remain partial.',
      ],
      maintenanceReloads: {
        authorizedClass: 'Scheduled maintenance reloads are allowed; random-outcome retries remain forbidden.',
        adapterSubclass: 'An immutable list of elapsed-ms requests or fixed-period schedule is selected before new-save startup. Lifecycle guards defer requests; overlapping requests coalesce. The policy cannot trigger a reload, supply a save, or alter the schedule after startup.',
        nativePath: 'Visible Options → Change language → English; native Logic waits for minigame loading and save completion before App.reload. A fresh VM/DOM/timer queue then executes the pinned startup and native delayed LoadSave.',
        preservedState: 'Only the current native serialized save, localStorage, elapsed clock and continuing free-draw stream cross navigation. Native serialization and load determine quantization, buff reconstruction, discarded shimmers and timer restart.',
        exportInteraction: 'ExportSave clears toSave without persisting. Export remains available after a maintenance request, but a subsequent native reload without an App.save after that request is an inadmissible rollback trace, not a native game failure. The native Ctrl+S input can restore the save request before navigation.',
        limitation: 'This implements a scheduled subclass. It does not prove equivalence to every allowed maintenance policy or a full browser navigation refinement.',
      },
      informationBoundary: 'The policy receives public observations and their history, including the current native Export save textarea when opened through the Options anchor. Its encoded startup seed may be decoded under the user-approved rule. Direct private state, experiment RNG state and future draws are not exposed. The user allows scheduled current-save maintenance reloads and forbids import, save editing, outcome retries and deliberate native-UI manipulation of random outcomes.',
    },
    actionTypes: [...ACTION_TYPES], counts, surfaces,
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  const output = resolve(process.argv[2] || 'model/action-coverage.json');
  const report = buildActionCoverage({ sourceDirectory: process.argv[3] });
  writeFileSync(output, `${JSON.stringify(report, null, 2)}\n`);
  console.log(`Wrote ${report.surfaces.length} source surfaces to ${output}; ${JSON.stringify(report.counts)}`);
}

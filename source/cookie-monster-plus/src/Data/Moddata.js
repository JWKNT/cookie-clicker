/** Data related directly to Cookie Monster */

export const VersionMajor = '2.053';
export const VersionMinor = '13';

/** Information about Cookie Monster to be displayed in the info section */
export const ModDescription = `<a href="https://github.com/CookieMonsterTeam/CookieMonster" target="blank">Cookie Monster</a>
 offers a wide range of tools and statistics to enhance your game experience.
 It is not a cheat interface – although it does offer helpers for golden cookies and such, everything can be toggled off at will to only leave how much information you want.</br>
 Progess on new updates and all previous release notes can be found on the GitHub page linked above!</br>
 Please also report any bugs you may find over there!</br>
 `;

/** Latest releasenotes of Cookie Monster to be displayed in the info section */
export const LatestReleaseNotes = `Cookie Monster+ (local build based on 2.053.10)</br>
- Version 13 publishes a readable (unminified) build and the full source at github.com/JWKNT/cookie-clicker, installed by a patcher that checks every file</br>
- Version 12 adds Godzamok combos: with Godzamok slotted, autoplay sells and buys back every building type whose round trip pays, every frame, so his click buff keeps growing (income rises thousands of times over), and the Pantheon slots him for it (within seconds of an ascension, or with a sugar lump to refill the worship swaps when they ran out)</br>
- The Grandmapocalypse stage is now chosen by income: with the Elder Pact a pledge costs next to nothing, so autoplay pledges whenever calm (golden cookies, Frenzies on clicks) earns more than wrath and wrinklers, and revokes the covenant the elder achievements leave behind. It bursts wrinklers for "Wrinklesquisher" and "Moistburster" when they are worth the income given up</br>
- Achievements are valued in seconds of play (a share of income times the play still expected); a Born again run for Neverclick and Hardcore starts once they are worth more than its four hours</br>
- The garden breeds new seeds along the wheat chain on a checkerboard (Thumbcorn, Cronerice, Gildmillet, Clover, Golden clover, ...) with the right soil; the Stock Market upgrades its offices and takes loans that end before their interest; sugar lumps go to cursor levels for the first loan and to the Sugar frenzy; fortunes, Santa's helper grandmas, gift codes, dragon petting and a narrow-window ticker click are taken as well</br>
- Version 11 plays the whole game: the Grandmapocalypse (wrath cookies beat golden ones when every cookie is clicked, and wrinklers multiply income about six times), the dragon (trained every run, auras picked by the CpS they add), seasons (Santa, heart biscuits, Easter eggs, reindeer), sugar lumps (minigames first, then building levels), the Pantheon, the Grimoire, permanent upgrade slots, heavenly upgrades for all of these, and achievements that only take an action</br>
- Autoplay: clicks the big cookie (20 per second by default), buys the building or upgrade with the best payback period, clicks golden cookies and reindeer, and ascends at the optimal time (all switchable under Options, Autoplay)</br>
- Ascension Advisor: plans every future ascension with a dynamic program, counting prestige levels, Legacy and the heavenly upgrades the chips can buy (several per ascension); it never recommends an ascension worth less than a 10% speed-up</br>
- Click and golden cookie upgrades are valued at what they bring under autoplay (auto-click rate, golden cookie income), so they are coloured instead of gray and bought when they are the best deal; a "Lucky!" bank is kept only when that pays back faster than buying</br>
- Heavenly chips are spent along one purchase order, most time saved per chip first ((1 - 1/multiplier) / cost, which is provably optimal without parent constraints) with required parents included, which the Ascension Advisor also plans with; auto-ascend buys as many items as the chips cover and saves the rest for the next one</br>
- The auto-buyer judges purchases by what they add to long-run income: click power at the auto-click rate (now for buildings too), multiplied by what the golden cookies autoplay clicks make of production (Frenzies, building specials, cookie storms and Click frenzies), without current buffs. A "Lucky!" bank is only kept back from purchases that pay back slower than banked cookies do, which is now rare</br>
- The "Next buy" countdown uses the income measured over the last ten minutes, as the expected income counts rare jackpots that seldom arrive within minutes</br>
- Timer bar: a "Lucky!" bank row appears while autoplay keeps cookies back for "Lucky!", which explains why an affordable "Next buy" can still be waiting</br>
- Auto-ascend pops normal wrinklers and buys the Chocolate egg before ascending, then reincarnates</br>
- Average CPS is measured on cookies earned, so seconds with a purchase no longer count as zero income</br>
- Exact heavenly chips per second, compact tooltips, combined bank warnings and compact bottom-bar times</br>
- Bugfix: the sell price shown in building tooltips in sell mode was always "1"</br>
- Bugfix: right after the game loaded, the auto-buyer could buy as if there were no "Lucky!" bank (its target was computed before CpS), and in the frame CpS changed it could act on values not yet updated</br>
- Bugfix: the golden cookie timer could show "NaN%" after loading, until the next golden cookie</br>
- Bugfix: importing a save while Cookie Monster was running could stop it loading its settings</br>`;

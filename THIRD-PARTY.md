# Third-party material

This repository holds material from other projects. Each part keeps its own license. The main README lists
the licenses of the mod, of its source and of the fonts.

## Cookie Clicker

*Cookie Clicker* is a game by Julien Thiennot (Orteil), published by DashNet. Its code and graphics are
copyright Orteil. The page of the game has this notice:

> Feel free to alter this code to your liking, but please do not re-host it, do not profit from it and do
> not present it as your own.

This repository does not hold the game, its scripts, its page, its style sheets, its images or its sounds.
The tools of the audit read an installed copy of version 2.053, and they check each file against a SHA-256
digest.

The audit holds these things that come from the game:

- Names and identifiers of achievements, upgrades, buildings and other items, in the catalogue files of
  `model/`, `paper/` and `lean/`.
- Single functions of the game in a parsed form, in files `lean/CookieClicker/JavaScript*Syntax.lean` and
  `lean/CookieClicker/JavaScript*Source.lean`. A tool `tools/generate-*.mjs` made each file from the
  installed game. With them, Lean checks statements about these functions. These files hold about
  10,000 syntax nodes. The main script of the game has about 121,000, so this is about 8% of it.
- Short quotations of code in the notes and in some data files.

Two files of one experiment hold the complete page, the style sheets and the parsed scripts of the game.
They are not in this repository: `request.json.gz` and `request-template.json` in
`model/experiments/cursor-cycle-source/`. The file `MANIFEST.json` in that folder has their digests.

## Chromium 87

`model/browser-source/chromium-87/` holds 105 source files of Chromium 87.0.4280.141 and its style sheet
`html.css`. The audit compares its model of the browser with them. The license files are in the same
folder: `LICENSE` for Chromium, and `COPYING.LIB` for the files that come from WebKit.

`source/` holds copies of three of these files (`css_parsing_utils.cc`, `css_tokenizer.cc`,
`longhands_custom.cc`), each also in a base64 form, and three lists of sources. Three audit tools read
them. The same licenses apply.

## Electron 11.5.0

`model/browser-source/chromium-87/electron-dom-storage-limits.patch` is a patch from Electron. Electron has
this license:

```text
Copyright (c) Electron contributors
Copyright (c) 2013-2020 GitHub Inc.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```

## V8 8.7 and Python

`model/semantics/v8-timsort.js` and `lean/CookieClicker/JavaScriptTimSortSyntax.lean` come from the array
sort of V8 8.7.220.31, which comes from the list sort of Python. The licenses are
`lean/licenses/V8-LICENSE` and `lean/licenses/PYTHON-LICENSE`.

## Unicode 13

`model/unicode13/` holds four data files of Unicode 13 and their license, `LICENSE.txt`.
`lean/CookieClicker/JavaScriptUnicodeData.lean` is made from them.

## WHATWG HTML Standard

`model/standards/html-entities.json` is the list of named character references of the HTML Standard,
from <https://html.spec.whatwg.org/entities.json> on 30 October 2026.
`lean/CookieClicker/JavaScriptHtmlEntities.lean` is made from it. The HTML Standard is copyright WHATWG
(Apple, Google, Mozilla, Microsoft), under the Creative Commons Attribution 4.0 International License.

## seedrandom

The game includes the library seedrandom.js by David Bau (<https://github.com/davidbau/seedrandom>). The
files `lean/CookieClicker/JavaScriptSeedrandom*.lean` hold functions of that library in a parsed form,
made from the copy in the game.

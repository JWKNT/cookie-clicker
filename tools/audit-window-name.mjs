/** Pin the current-frame Window.name binding and stored browsing-context state. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const files=['window.idl','dom_window.cc','local_dom_window.cc'];
const sources=files.map(file=>({file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/core/frame/${file}`,sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const idl=readFileSync(new URL('window.idl',directory),'utf8'),implementation=readFileSync(new URL('local_dom_window.cc',directory),'utf8');
assert.match(idl,/attribute DOMString name;/);assert.match(implementation,/return GetFrame\(\)->Tree\(\).GetName\(\);/);
assert.match(implementation,/GetFrame\(\)->Tree\(\).SetName\(name, FrameTree::kReplicate\);/);
const report={schema:1,scope:'current-active-browsing-context-name',chromiumVersion:'87.0.4280.141',sources,
  rules:{initial:'Explicit optional UTF16 fixture; unspecified initial reads stay unresolved.',get:'Read stored frame name independently of mutable own property descriptors.',set:'Native receiver validation precedes source DOMString conversion, then stored state changes; setter returns undefined.',receivers:'Current Window, undefined and null are accepted by the pinned native binding. Unrelated objects throw before conversion.',callbacks:'Source conversion callbacks can read or update the same state; their writes persist if conversion throws.',source:'Game.CalculateGains at main.js5112 assigns the lowercase bakery name through a sloppy global name binding before the Orteil/Ortiel production checks.'},
  validation:'node lean/check_javascript_window_name.mjs --engine',remaining:['Navigation and cross-window lifecycle','Detached or no-longer-displayed Window objects','Full source/native refinement'],navigationRefinementVerified:false};
writeFileSync(new URL('../model/window-name-witness.json',import.meta.url),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({sources:sources.length,navigationRefinementVerified:false}));

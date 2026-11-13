/** Source pins for explicit cookie-origin behavior; not a native refinement proof. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const files={
  'document.cc':'third_party/blink/renderer/core/dom/document.cc',
  'cookie_jar.cc':'third_party/blink/renderer/core/loader/cookie_jar.cc',
  'cookie_monster.cc':'net/cookies/cookie_monster.cc',
  'restricted_cookie_manager.cc':'services/network/restricted_cookie_manager.cc',
  'security_origin.cc':'third_party/blink/renderer/platform/weborigin/security_origin.cc',
  'security_origin.h':'third_party/blink/renderer/platform/weborigin/security_origin.h',
};
const sources=Object.entries(files).map(([file,path])=>({file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/${path}`,sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const document=readFileSync(new URL('document.cc',directory),'utf8'),monster=readFileSync(new URL('cookie_monster.cc',directory),'utf8');
assert.match(document,/String Document::cookie\(ExceptionState& exception_state\) const/);
assert.match(document,/void Document::setCookie\(const String& value, ExceptionState& exception_state\)/);
assert.match(document,/GetSecurityOrigin\(\)->CanAccessCookies\(\)/);
assert.match(monster,/kDefaultCookieableSchemes\[\] = \{"http", "https",\s*"ws", "wss"\}/);
assert.match(monster,/EXCLUDE_NONCOOKIEABLE_SCHEME/);
const witness={schema:1,scope:'file-and-opaque-origin-cookie-accessors-not-browser-refinement',chromiumVersion:'87.0.4280.141',sources,
  configuration:{initialCookieStore:'empty',cookieableSchemes:['http','https','ws','wss'],nativeSchemeRegistryChanges:'not modeled',origins:['file','opaque'],unconfigured:'explicit unresolved request'},
  rules:{fileGetter:'empty string',fileSetter:'performs source DOMString conversion and returns undefined; excluded file scheme cannot store cookie',opaqueAccess:'SecurityError after setter conversion; wrong receiver rejects before conversion',setterMissingArgument:'undefined is converted to DOMString'},
  validation:'node lean/check_javascript_cookies.mjs --engine; fresh temporary file/data profiles, no user cookie store',
  remaining:['HTTP cookie stores, expiry, domains, paths and SameSite','Native scheme-policy changes','Other Document origins and global native host refinement'],fullHostRefinement:false};
writeFileSync(new URL('../model/cookie-host-witness.json',import.meta.url),JSON.stringify(witness,null,2)+'\n');
console.log(JSON.stringify({sources:sources.length,fullHostRefinement:false}));

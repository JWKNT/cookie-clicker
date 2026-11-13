import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const data=JSON.parse(readFileSync(new URL('../model/css-properties.json',import.meta.url),'utf8'));
assert.equal(createHash('sha256').update(JSON.stringify(data.properties)).digest('hex'),data.propertiesSha256);
const string=value=>{assert(typeof value==='string' && /^[\x20-\x7e]*$/.test(value));return JSON.stringify(value);};
const list=values=>`[${values.map(string).join(', ')}]`;
const chunks=[];
for(let offset=0;offset<data.properties.length;offset+=80){
 const rows=data.properties.slice(offset,offset+80).map(row=>`  ⟨${string(row.javascriptName)}, ${row.cssName===null?'none':`some ${string(row.cssName)}`}, ${list(row.aliases)}, ${list(row.longhands)}⟩`);
 chunks.push(`private def chunk${chunks.length} : Array Property := #[\n${rows.join(',\n')}\n]\n`);
}
const output=`/-! Generated observed Chromium87 CSS property names and expansions.
Source: model/css-properties.json, SHA256 ${data.propertiesSha256}.
This table does not implement value parsing, shorthand reconstruction or layout. -/
namespace CookieClicker.JavaScript.CssProperties
structure Property where
  javascriptName : String
  cssName : Option String
  aliases : List String
  longhands : List String
  deriving Repr, DecidableEq
${chunks.join('\n')}
def properties : Array Property := ${chunks.map((_,index)=>`chunk${index}`).join(' ++ ')}
end CookieClicker.JavaScript.CssProperties
`;
const path=new URL('../lean/CookieClicker/JavaScriptCssProperties.lean',import.meta.url);
if(process.argv.includes('--check'))assert.equal(readFileSync(path,'utf8'),output,'Generated CSS property table is stale');
else writeFileSync(path,output);
console.log(JSON.stringify({properties:data.properties.length,mapped:data.properties.filter(row=>row.cssName!==null).length,propertiesSha256:data.propertiesSha256}));

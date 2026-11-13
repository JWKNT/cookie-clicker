import test from 'node:test';
import assert from 'node:assert/strict';
import {compileCss,compileCssSelector,compilePinnedStylesheets,tokenizeCss} from '../model/css-ast.mjs';
import {hasGameSource} from '../model/game-source.mjs';

test('CSS comments preserve lexical boundaries without creating descendant spaces',()=>{
  const tokens=tokenizeCss('.a/**/.b, url/**/(x)');
  assert.deepEqual(tokens.slice(0,4).map(t=>[t.kind,t.value]),[['delimiter','.'],['ident','a'],['delimiter','.'],['ident','b']]);
  assert.equal(tokens.find(t=>t.value==='url').kind,'ident');
  assert.equal(tokenizeCss('url(x)')[0].kind,'url');
  assert.deepEqual(tokenizeCss('co/**/lor').map(t=>t.value),['co','lor']);
});

test('CSS string and identifier escapes retain UTF16 values and source ranges',()=>{
  const slash=String.fromCharCode(92);
  const source='.'+slash+'61 b{content:"a;'+slash+'\n b'+slash+'26 c"}';
  const tokens=tokenizeCss(source),string=tokens.find(t=>t.kind==='string');
  assert.equal(tokens[1].value,'ab');
  assert.equal(String.fromCharCode(...string.units),'a; b&c');
  for(const token of tokens){assert.ok(token.start>=0);assert.ok(token.end<=source.length);assert.ok(token.end>token.start);}
});

test('unquoted URL punctuation cannot terminate rule or declaration syntax',()=>{
  const rule=compileCss('a{background:url(a}b;c.png);left:1px;}').rules[0];
  assert.equal(rule.declarations.length,2);
  assert.equal(String.fromCharCode(...rule.declarations[0].value[0].units),'a}b;c.png');
});

test('CSS declarations preserve duplicate order priorities and invalid syntax',()=>{
  const declarations=compileCss('a{left:1px;top:2px!important;left:3px; //disabled:1; width:4px ! IMPORTANT;}').rules[0].declarations;
  assert.deepEqual(declarations.map(d=>d.kind==='invalid'?'invalid':`${d.property}:${d.important}`),['left:false','top:true','left:false','invalid','width:true']);
  assert.equal(declarations[3].reason,'declaration-does-not-start-with-ident');
});

test('CSS component-value nesting preserves function semicolons and comma selectors',()=>{
  const rule=compileCss('a:not(.x),b:nth-child(2n+1){x:fn(a;b,c);width:calc(100% - 1px)}').rules[0];
  assert.equal(rule.selectors.length,2);
  assert.equal(rule.declarations.length,2);
  assert.equal(rule.declarations[0].value[0].kind,'function');
  assert.equal(rule.declarations[0].value[0].value,'fn');
});

test('CSS font and keyframe bodies retain separate rule types',()=>{
  const result=compileCss('@font-face{font-family:x;src:url(x.woff)}@keyframes move{0%,50%{left:0}to{left:1px}}');
  assert.deepEqual(result.rules.map(r=>r.kind),['font-face','keyframes']);
  assert.equal(result.rules[1].rules[0].selectors.length,2);
  assert.equal(result.rules[1].rules[1].kind,'keyframe');
});

test('CSS unsupported recovery or at-rules fail explicitly',()=>{
  for(const source of ['a{left:"bad\nvalue"}','a{left:url(a b)}','a{/*','@media print{a{left:0}}','a{left:1px','a{left:\u0000}'])assert.throws(()=>compileCss(source),SyntaxError);
});

test('CSS ASCII folding and identifier hash flags do not broaden syntax',()=>{
  assert.equal(compileCss('a{COLOR:red;Ä:1}').rules[0].declarations[1].property,'Ä');
  assert.throws(()=>compileCss('@Keyframes a{to{left:0}}'),/Unsupported CSS at-rule/);
  assert.equal(tokenizeCss('#123')[0].identifier,false);
  assert.equal(tokenizeCss('#'+String.fromCharCode(92)+'31 23')[0].identifier,true);
});

test('CSS selector syntax preserves combinators attributes and specificity',()=>{
  const selector=compileCssSelector('#wrapper.onWeb > div#game.x + span[data-x="A" i]:not(.off)');
  assert.deepEqual(selector.parts.map(p=>p.relation),[null,'child','next-sibling']);
  assert.deepEqual(selector.specificity,[2,4,2]);
  assert.equal(selector.parts[2].simple[1].flag,'ascii-insensitive');
  assert.equal(compileCssSelector('input::-moz-range-thumb').valid,false);
  assert.equal(compileCssSelector('div:-webkit-scrollbar').parts[0].simple[1].kind,'pseudo-element');
  assert.throws(()=>compileCssSelector('div:unknown-native-pseudo'),/Unsupported native pseudo/);
  for(const selector of ['div:root(x)','div:nth-child','div:not(:not(.x))'])assert.throws(()=>compileCssSelector(selector),/Unsupported/);
});

test('pinned stylesheets compile in source order without claiming CSS semantics',{skip:!hasGameSource()},()=>{
  const sheets=compilePinnedStylesheets();
  assert.deepEqual(sheets.map(s=>[s.name,s.rules.length]),[['style.css',522],['../steam/fonts.css',5]]);
  assert.equal(sheets[0].rules.filter(r=>r.kind==='style').length,492);
  assert.equal(sheets[0].rules.filter(r=>r.kind==='style'&&r.selectorAst.every(s=>s.valid)).length,486);
  assert.equal(sheets[0].rules.flatMap(r=>r.declarations||[]).filter(d=>d.kind==='invalid').length,2);
  assert.ok(sheets.every(s=>s.cssSemanticsVerified===false));
});

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve, dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const arg = name => { const at = process.argv.indexOf(name); return at < 0 ? null : process.argv[at + 1]; };
const root = resolve(arg('--root') || join(dirname(fileURLToPath(import.meta.url)), '..'));
const leanRoot = resolve(arg('--lean-root') || join(root, 'lean'));
const report = resolve(arg('--report') || join(root, 'model/natural-season-source.json'));
const require = createRequire(join(root, 'source/cookie-monster-plus/package.json'));
const acorn = require('acorn');
const { loadGameSource } = await import(pathToFileURL(join(root, 'model/game-source.mjs')));
const source = loadGameSource(arg('--source') || undefined);
const main = source.sources['main.js'];
const hash = value => createHash('sha256').update(value).digest('hex');
const begin = main.indexOf("Game.baseSeason='';");
const end = main.indexOf('Game.updateLog=', begin);
assert(begin >= 0 && end > begin);
const text = main.slice(begin, end);
const ast = acorn.parse(text, { ecmaVersion: 5 });
const clean = value => Array.isArray(value) ? value.map(clean) : value && typeof value === 'object'
  ? Object.fromEntries(Object.entries(value).filter(([key]) => !['start','end','raw'].includes(key)).map(([key,v]) => [key,clean(v)])) : value;
const expectedExpression = text => acorn.parseExpressionAt(text, 0, { ecmaVersion: 5 });
const sameExpression = (node, code) => assert.deepEqual(clean(node), clean(expectedExpression(code)), code);
const isMember = (node, object, property) => node?.type === 'MemberExpression' && !node.computed
  && node.object.type === 'Identifier' && node.object.name === object && node.property.name === property;
const declaration = (node, name) => {
  assert.equal(node.type, 'VariableDeclaration'); assert.equal(node.kind, 'var'); assert.equal(node.declarations.length, 1);
  assert.equal(node.declarations[0].id.name, name); return node.declarations[0].init;
};
const assignment = (node, name) => {
  assert.equal(node.type, 'ExpressionStatement'); assert.equal(node.expression.type, 'AssignmentExpression');
  assert.equal(node.expression.operator, '='); assert.equal(node.expression.left.name, name); return node.expression.right;
};
assert.equal(ast.body.length, 5);
sameExpression(ast.body[0].expression, "Game.baseSeason=''");
sameExpression(declaration(ast.body[1], 'year'), 'new Date().getFullYear()');
sameExpression(declaration(ast.body[2], 'leap'), '(((year%4==0)&&(year%100!=0))||(year%400==0))?1:0');
sameExpression(declaration(ast.body[3], 'day'), 'Math.floor((new Date()-new Date(year,0,0))/(1000*60*60*24))');
const rows = [], formulas = [];
const render = (node, names) => {
  if (node.type === 'Identifier') { assert(node.name in names, node.name); return names[node.name]; }
  if (node.type === 'Literal') { assert.equal(typeof node.value, 'number'); assert(Number.isInteger(node.value)); return String(node.value); }
  if (node.type === 'BinaryExpression' || node.type === 'LogicalExpression') {
    const op = { '+': '+', '-': '-', '*': '*', '>=': '≥', '<=': '≤', '&&': '∧', '||': '∨' }[node.operator];
    assert(op, `Unmapped operator ${node.operator}`); return `(${render(node.left,names)} ${op} ${render(node.right,names)})`;
  }
  if (node.type === 'CallExpression' && isMember(node.callee, 'Math', 'floor')) {
    assert.equal(node.arguments.length, 1); const x = node.arguments[0];
    assert.equal(x.type, 'BinaryExpression'); assert.equal(x.operator, '/');
    return `(${render(x.left,names)} / ${render(x.right,names)})`;
  }
  throw new Error(`Unmapped calendar expression ${node.type}`);
};
const add = (name, node, names, parameters = '(y : Int)') => {
  const formula = render(node,names); formulas.push(`def ${name} ${parameters} : Int := ${formula}`);
  rows.push({ name, nativeText: text.slice(node.start,node.end), sourceSha256: hash(text.slice(node.start,node.end)), integerFormula: formula });
};
let branch = ast.body[4]; const guards=[];
for (const season of ['valentines','fools','halloween','christmas']) {
  assert.equal(branch.type, 'IfStatement'); const assignment = branch.consequent.expression;
  assert.equal(assignment.type, 'AssignmentExpression'); assert.equal(assignment.operator, '=');
  assert(isMember(assignment.left, 'Game', 'baseSeason')); assert.equal(assignment.right.value, season);
  guards.push({ season, condition: render(branch.test,{year:'y',day:'day',leap:'(leap y)'}) });
  branch=branch.alternate;
}
assert.equal(branch.type,'BlockStatement'); assert.equal(branch.body.length,3);
const call = declaration(branch.body[0],'easterDay');
assert.equal(call.type,'CallExpression'); assert.equal(call.callee.type,'FunctionExpression');
assert.deepEqual(call.callee.params.map(x=>x.name),['Y']); assert.equal(call.arguments.length,1); assert.equal(call.arguments[0].name,'year');
const body=call.callee.body.body; assert.equal(body.length,12);
const names={Y:'y'};
for (const [index, native, name] of [[0,'C','century'],[1,'N','goldenNumber'],[2,'K','centuryCorrection'],[3,'I','rawEpact']]) {
  add(name,declaration(body[index],native),names); names[native]=`(${name} y)`;
}
add('epact0',assignment(body[4],'I'),names); names.I='(epact0 y)';
add('correctEpact',assignment(body[5],'I'),{I:'i',N:'n'},'(i n : Int)');
formulas.push('def epact (y : Int) : Int := correctEpact (epact0 y) (goldenNumber y)'); names.I='(epact y)';
add('rawWeekday',declaration(body[6],'J'),names); names.J='(rawWeekday y)';
add('easterWeekday',assignment(body[7],'J'),names); names.J='(easterWeekday y)';
for (const [index,native,name] of [[8,'L','easterOffset'],[9,'M','easterMonth'],[10,'D','easterMonthDay']]) {
  add(name,declaration(body[index],native),names); names[native]=`(${name} y)`;
}
sameExpression(body[11].argument,'new Date(Y,M-1,D)');
sameExpression(assignment(branch.body[1],'easterDay'),'Math.floor((easterDay-new Date(easterDay.getFullYear(),0,0))/(1000*60*60*24))');
assert.equal(branch.body[2].type,'IfStatement'); sameExpression(branch.body[2].consequent.expression,"Game.baseSeason='easter'");
assert.equal(branch.body[2].alternate,null);
guards.push({season:'easter',condition:render(branch.body[2].test,{day:'day',easterDay:'(easterOrdinal y)'})});
const output=`import CookieClicker.JavaScriptCalendar

/- Generated by tools/generate-natural-season-formula.mjs.
Pinned main.js SHA-256: ${source.hashes['main.js']}
This is the exact integer formula extracted from the native AST. Native Number
rounding, Date constructor/getter execution, heap bindings, and callbacks are
separate refinement obligations. Math.floor(a/b) maps to Int division here;
this extraction does not assert that the native operations have that value. -/
namespace CookieClicker.JavaScript.NaturalSeasons

def leap (y : Int) : Int := if Calendar.leapYear y then 1 else 0
${formulas.join('\n')}
def easterOrdinal (y : Int) : Int :=
  Calendar.monthStart y (easterMonth y - 1).toNat + easterMonthDay y

inductive Season where
  | none | valentines | fools | halloween | christmas | easter
  deriving Repr, DecidableEq

/-- Native guard order, including the leap-year Business-day mask. -/
def select (y day : Int) : Season :=
  ${guards.map((g,i)=>`${i?'else if':'if'} ${g.condition} then .${g.season}`).join('\n  ')}
  else .none

end CookieClicker.JavaScript.NaturalSeasons
`;
const snippets=[
  ['reset', 'Game.seasonT=0;\r\n\t\t\tGame.seasonUses=0;\r\n\t\t\tGame.season=Game.baseSeason;'],
  ['load', 'Game.seasonT=spl[20]?parseInt(spl[20]):0;\r\n\t\t\t\t\t\tGame.seasonUses=spl[21]?parseInt(spl[21]):0;\r\n\t\t\t\t\t\tGame.season=spl[22]?spl[22]:Game.baseSeason;'],
  ['offline', 'if (Game.seasonT>0) Game.seasonT=Math.max(Game.seasonT-framesElapsed,1);'],
  ['duration', 'Game.getSeasonDuration=function(){return Game.fps*60*60*24;}'],
];
const writerRows=snippets.map(([name,s])=>{const at=main.indexOf(s);assert(at>=0,name);return{name,startLine:main.slice(0,at).split('\n').length,sourceSha256:hash(s),text:s};});
const expirationStart=main.indexOf('if (Game.seasonT>0)',main.indexOf('//handle seasons'));
const expirationEnd=main.indexOf('//press ctrl',expirationStart);
assert(expirationStart>=0&&expirationEnd>expirationStart);
const expiration=main.slice(expirationStart,expirationEnd).trimEnd();
writerRows.push({name:'expiration',startLine:main.slice(0,expirationStart).split('\n').length,sourceSha256:hash(expiration),text:expiration});
const witness={schemaVersion:1,gameVersion:source.version,mainSha256:source.hashes['main.js'],
  launchFragment:{startLine:main.slice(0,begin).split('\n').length,sha256:hash(text),nodes:clean(ast)},
  extractedFormulas:rows,guards,seasonWriters:writerRows,
  generatedLeanSha256:hash(output),
  provedScope:'Universal integer guard recurrence with actual extended UTC year decoder; no native Number/Date/source-callback refinement asserted',
  calendarMillisecondsPerDay:86400000,recurrenceBoundDays:733,dailyScheduleDependsOnSeedOrOutcomes:false};
const target=join(leanRoot,'CookieClicker/JavaScriptNaturalSeasonFormula.lean');
const reportText=JSON.stringify(witness,null,2)+'\n';
if(process.argv.includes('--check')){assert.equal(readFileSync(target,'utf8'),output);assert.equal(readFileSync(report,'utf8'),reportText);}
else{writeFileSync(target,output);writeFileSync(report,reportText);}
console.log(JSON.stringify({check:process.argv.includes('--check'),formulas:rows.length,seasonGuards:guards.length,writerPaths:writerRows.length,generatedLeanSha256:hash(output)}));

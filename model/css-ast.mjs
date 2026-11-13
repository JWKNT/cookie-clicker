/** Closed CSS token/rule frontend. Parsing does not establish native CSS refinement.
 * Token structure follows the 2019 CSS Syntax 3 grammar; unsupported recovery is explicit.
 */
import {createHash} from 'node:crypto';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {defaultGameSourceDirectory} from './game-source.mjs';

export const CSS_SOURCE_HASHES=Object.freeze({
  'style.css':'90c1ad8750f88ad2f964b5910521e84a16f9ec4d9b30c26244625bc269c7f446',
  '../steam/fonts.css':'9bd20bc2e0a326d5c4801c83ee8b982ada6b1c3ff3d7ad36053a20b48582eebc',
});
const whitespace=c=>c!==undefined&&/[\t\n\r\f ]/.test(c);
const nameStart=c=>c!==undefined&&(/[A-Za-z_]/.test(c)||c.charCodeAt(0)>=128);
const nameChar=c=>nameStart(c)||(c!==undefined&&/[0-9-]/.test(c));
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const asciiLower=s=>s.replace(/[A-Z]/g,c=>String.fromCharCode(c.charCodeAt(0)+32));
const trim=tokens=>{let a=0,b=tokens.length;while(tokens[a]?.kind==='space')a++;while(b>a&&tokens[b-1].kind==='space')b--;return tokens.slice(a,b);};

export function tokenizeCss(source){
  if(typeof source!=='string')throw new TypeError('CSS source must be a string');
  if(/[\u0000\ud800-\udfff]/.test(source))throw new SyntaxError('Unsupported CSS input preprocessing');
  const tokens=[];let i=source.charCodeAt(0)===0xfeff?1:0;
  const fail=message=>{throw new SyntaxError(`${message} at UTF16 offset ${i}`);};
  const escape=()=>{
    i++;if(i>=source.length||/[\n\r\f]/.test(source[i]))fail('Unsupported invalid CSS escape');
    const match=/^[0-9a-fA-F]{1,6}/.exec(source.slice(i));
    if(match){i+=match[0].length;const value=parseInt(match[0],16);if(source[i]==='\r'&&source[i+1]==='\n')i+=2;else if(whitespace(source[i]))i++;return String.fromCodePoint(value===0||value>0x10ffff||(value>=0xd800&&value<=0xdfff)?0xfffd:value);}
    return source[i++];
  };
  const validEscape=at=>source[at]==='\\'&&source[at+1]!==undefined&&!/[\n\r\f]/.test(source[at+1]);
  const startsName=at=>nameStart(source[at])||validEscape(at)||(source[at]==='-'&&(nameStart(source[at+1])||source[at+1]==='-'||validEscape(at+1)));
  const consumeName=()=>{let value='';while(i<source.length){if(nameChar(source[i]))value+=source[i++];else if(validEscape(i))value+=escape();else break;}return value;};
  while(i<source.length){
    const start=i,c=source[i];
    if(c==='\0'||(c.charCodeAt(0)>=0xd800&&c.charCodeAt(0)<=0xdfff))fail('Unsupported CSS input preprocessing');
    if(source.startsWith('/*',i)){const end=source.indexOf('*/',i+2);if(end<0)fail('Unterminated CSS comment');i=end+2;continue;}
    if(whitespace(c)){while(whitespace(source[i]))i++;tokens.push({kind:'space',start,end:i});continue;}
    if(c==='"'||c==="'"){
      i++;let value='',closed=false;while(i<source.length){if(source[i]===c){i++;closed=true;break;}if(/[\n\r\f]/.test(source[i]))fail('Unsupported bad-string recovery');if(source[i]==='\\'){if(/[\n\r\f]/.test(source[i+1]??'')){i++;if(source[i]==='\r'&&source[i+1]==='\n')i+=2;else i++;}else value+=escape();}else value+=source[i++];}
      if(!closed)fail('Unterminated CSS string');tokens.push({kind:'string',units:units(value),start,end:i});continue;
    }
    const number=/^[+-]?(?:\d*\.\d+|\d+)(?:[eE][+-]?\d+)?/.exec(source.slice(i));
    if(number){i+=number[0].length;let kind='number',unit='';if(startsName(i)){kind='dimension';unit=consumeName();}else if(source[i]==='%'){kind='percentage';i++;}tokens.push({kind,number:number[0],...(unit?{unit}:{}),start,end:i});continue;}
    if(c==='#'&&(nameChar(source[i+1])||validEscape(i+1))){i++;const identifier=startsName(i);tokens.push({kind:'hash',value:consumeName(),identifier,start,end:i});continue;}
    if(c==='@'&&startsName(i+1)){i++;tokens.push({kind:'at',value:consumeName(),start,end:i});continue;}
    if(startsName(i)){
      const value=consumeName();
      if(source[i]==='('){
        i++;
        if(asciiLower(value)==='url'){
          let next=i;while(whitespace(source[next]))next++;
          if(source[next]!=="'"&&source[next]!=='"'){
            i=next;let url='',closed=false;
            while(i<source.length){
              if(source[i]===')'){i++;closed=true;break;}
              if(whitespace(source[i])){while(whitespace(source[i]))i++;if(source[i]!==')')fail('Unsupported bad-url recovery');i++;closed=true;break;}
              if(/["'(\u0000-\u0008\u000b\u000e-\u001f\u007f]/.test(source[i]))fail('Unsupported bad-url recovery');
              if(source[i]==='\\')url+=escape();else url+=source[i++];
            }
            if(!closed)fail('Unterminated CSS URL');tokens.push({kind:'url',units:units(url),start,end:i});continue;
          }
        }
        tokens.push({kind:'function',value,start,end:i});continue;
      }
      tokens.push({kind:'ident',value,start,end:i});continue;
    }
    i++;tokens.push({kind:'delimiter',value:c,start,end:i});
  }
  return tokens;
}

function splitTop(tokens,delimiter){
  const out=[];let start=0;const stack=[];
  const opens={'(':')','[':']','{':'}'};
  for(let i=0;i<tokens.length;i++){
    const t=tokens[i];if(t.kind==='function'){stack.push(')');continue;}if(t.kind!=='delimiter')continue;
    if(t.value===delimiter&&stack.length===0){out.push(trim(tokens.slice(start,i)));start=i+1;continue;}
    if(opens[t.value])stack.push(opens[t.value]);else if([')',']','}'].includes(t.value)){if(stack.pop()!==t.value)throw new SyntaxError(`Unmatched CSS delimiter at ${t.start}`);}
  }
  if(stack.length)throw new SyntaxError('Unclosed CSS component value');out.push(trim(tokens.slice(start)));return out;
}

/** Selector syntax is data. Dynamic pseudo-class truth and cascade are separate. */
export function compileCssSelector(input){
  const tokens=trim(typeof input==='string'?tokenizeCss(input):input),parts=[];let i=0,relation=null;
  const specificity=[0,0,0];let valid=true;
  const invalidPseudo=new Set(['-moz-range-track','-moz-range-thumb','-ms-track','-ms-thumb']);
  const supportedClasses=new Set(['active','focus','hover','visited','read-only','first-child','last-child','only-child','empty','root','nth-child','not']);
  const supportedElements=new Set(['before','after','first-line','first-letter','-webkit-slider-runnable-track','-webkit-slider-thumb','-webkit-scrollbar','-webkit-scrollbar-track','-webkit-scrollbar-thumb']);
  const takeGroup=(closing)=>{const out=[];let depth=1;while(i<tokens.length){const t=tokens[i++];if(t.kind==='function'||(t.kind==='delimiter'&&t.value===(closing===')'?'(': '[')))depth++;if(t.kind==='delimiter'&&t.value===closing){depth--;if(depth===0)return out;}out.push(t);}throw new SyntaxError('Unclosed CSS selector group');};
  const skip=()=>{let found=false;while(tokens[i]?.kind==='space'){i++;found=true;}return found;};
  while(i<tokens.length){
    const simple=[];let typeSeen=false;
    while(i<tokens.length){
      const token=tokens[i];if(token.kind==='space'||(token.kind==='delimiter'&&['>','+','~'].includes(token.value)))break;
      i++;
      if(token.kind==='ident'||(token.kind==='delimiter'&&token.value==='*')){
        if(typeSeen||simple.length)throw new SyntaxError('Unsupported type-selector position');typeSeen=true;
        simple.push(token.kind==='ident'?{kind:'type',name:asciiLower(token.value)}:{kind:'universal'});if(token.kind==='ident')specificity[2]++;continue;
      }
      if(token.kind==='hash'){simple.push({kind:'id',name:token.value});specificity[0]++;if(!token.identifier)valid=false;continue;}
      if(token.kind==='delimiter'&&token.value==='.'){
        const name=tokens[i++];if(name?.kind!=='ident')throw new SyntaxError('Unsupported invalid class selector');simple.push({kind:'class',name:name.value});specificity[1]++;continue;
      }
      if(token.kind==='delimiter'&&token.value==='['){
        const group=trim(takeGroup(']'));let j=0;const name=group[j++];if(name?.kind!=='ident')throw new SyntaxError('Unsupported attribute selector name');
        while(group[j]?.kind==='space')j++;let operator='present',value=[],flag='default';
        if(j<group.length){
          const first=group[j++];if(first.kind!=='delimiter')throw new SyntaxError('Unsupported attribute selector operator');operator=first.value;
          if(['~','|','^','$','*'].includes(operator)){if(group[j++]?.value!=='=')throw new SyntaxError('Invalid attribute selector operator');operator+='=';}
          if(!['=','~=','|=','^=','$=','*='].includes(operator))throw new SyntaxError('Unsupported attribute selector operator');while(group[j]?.kind==='space')j++;
          const supplied=group[j++];if(supplied?.kind==='ident')value=units(supplied.value);else if(supplied?.kind==='string')value=supplied.units;else throw new SyntaxError('Unsupported attribute selector value');
          while(group[j]?.kind==='space')j++;if(j<group.length){const f=group[j++];if(f.kind!=='ident'||asciiLower(f.value)!=='i')throw new SyntaxError('Unsupported attribute matching flag');flag='ascii-insensitive';while(group[j]?.kind==='space')j++;}
        }
        if(j!==group.length)throw new SyntaxError('Trailing attribute selector syntax');simple.push({kind:'attribute',name:asciiLower(name.value),operator,value,flag});specificity[1]++;continue;
      }
      if(token.kind==='delimiter'&&token.value===':'){
        let element=false;if(tokens[i]?.kind==='delimiter'&&tokens[i].value===':'){element=true;i++;}
        const supplied=tokens[i++];if(!['ident','function'].includes(supplied?.kind))throw new SyntaxError('Unsupported pseudo selector');const name=asciiLower(supplied.value);
        element||=supportedElements.has(name);if(invalidPseudo.has(name))valid=false;
        else if(!supportedClasses.has(name)&&!supportedElements.has(name))throw new SyntaxError(`Unsupported native pseudo selector ${name}`);
        else if(element&&!supportedElements.has(name))valid=false;
        if(supplied.kind==='function'&&!['not','nth-child'].includes(name))throw new SyntaxError(`Unsupported functional pseudo selector ${name}`);
        if(supplied.kind!=='function'&&['not','nth-child'].includes(name))throw new SyntaxError(`Unsupported non-functional pseudo selector ${name}`);
        if(name==='not'&&supplied.kind==='function'){
          if(element)throw new SyntaxError('Unsupported invalid negation pseudo-element');
          const nested=compileCssSelector(takeGroup(')'));if(nested.parts.length!==1||nested.parts[0].simple.some(s=>['pseudo-element','not'].includes(s.kind)))throw new SyntaxError('Unsupported CSS3 negation selector');
          simple.push({kind:'not',selector:nested});for(let k=0;k<3;k++)specificity[k]+=nested.specificity[k];valid&&=nested.valid;
        }else{
          simple.push({kind:element?'pseudo-element':'pseudo-class',name,arguments:supplied.kind==='function'?takeGroup(')'):null});specificity[element?2:1]++;
        }
        continue;
      }
      throw new SyntaxError(`Unsupported selector token ${token.kind}:${token.value??''}`);
    }
    if(!simple.length)throw new SyntaxError('Empty CSS compound selector');parts.push({relation,simple});const spaced=skip();if(i===tokens.length)break;
    if(tokens[i].kind==='delimiter'&&['>','+','~'].includes(tokens[i].value)){relation={'>':'child','+':'next-sibling','~':'following-sibling'}[tokens[i++].value];skip();}
    else if(spaced)relation='descendant';else throw new SyntaxError('Missing CSS selector combinator');
    if(i===tokens.length)throw new SyntaxError('Trailing CSS selector combinator');
  }
  if(!parts.length)throw new SyntaxError('Empty CSS selector');return{parts,specificity,valid};
}

export function parseCssDeclarations(tokens){
  const result=[];
  for(const part of splitTop(tokens,';')){
    if(!part.length)continue;
    let position=0;const property=part[position++];
    if(property.kind!=='ident'){
      if(property.kind==='at')throw new SyntaxError(`Unsupported nested declaration at-rule at ${property.start}`);
      result.push({kind:'invalid',reason:'declaration-does-not-start-with-ident',tokens:part,start:property.start,end:part.at(-1).end});continue;
    }
    while(part[position]?.kind==='space')position++;
    if(part[position]?.kind!=='delimiter'||part[position]?.value!==':'){
      result.push({kind:'invalid',reason:'missing-colon',tokens:part,start:property.start,end:part.at(-1).end});continue;
    }
    let value=trim(part.slice(position+1)),important=false;
    if(value.at(-1)?.kind==='ident'&&asciiLower(value.at(-1).value)==='important'){
      let bang=value.length-2;while(value[bang]?.kind==='space')bang--;
      if(value[bang]?.kind==='delimiter'&&value[bang].value==='!'){important=true;value=trim(value.slice(0,bang));}
    }
    if(!value.length)throw new SyntaxError(`Unsupported empty CSS declaration at ${property.start}`);
    result.push({kind:'declaration',property:property.value.startsWith('--')?property.value:asciiLower(property.value),important,value,start:property.start,end:part.at(-1).end});
  }
  return result;
}

function parseRules(tokens,{keyframes=false}={}){
  const rules=[];let position=0;
  while(position<tokens.length){
    if(tokens[position].kind==='space'){position++;continue;}
    const start=position;let depth=0;
    while(position<tokens.length){const t=tokens[position];if(t.kind==='function')depth++;if(t.kind==='delimiter'){if(t.value==='('||t.value==='[')depth++;else if(t.value===')'||t.value===']')depth--;else if(depth===0&&(t.value==='{'||t.value===';'))break;}position++;}
    if(position===tokens.length||tokens[position].value!== '{')throw new SyntaxError(`Unsupported CSS rule or recovery at ${tokens[start].start}`);
    const prelude=trim(tokens.slice(start,position));position++;const bodyStart=position;let braces=1;
    while(position<tokens.length&&braces){const t=tokens[position];if(t.kind==='delimiter'){if(t.value==='{')braces++;else if(t.value==='}')braces--;}if(braces)position++;}
    if(braces)throw new SyntaxError('Unclosed CSS rule body');const body=tokens.slice(bodyStart,position),end=tokens[position++].end;
    if(prelude[0]?.kind==='at'){
      const name=asciiLower(prelude[0].value);
      if(name==='font-face')rules.push({kind:'font-face',declarations:parseCssDeclarations(body),start:prelude[0].start,end});
      else if(['keyframes','-webkit-keyframes','-moz-keyframes'].includes(name)){
        const rest=trim(prelude.slice(1));if(rest.length!==1||rest[0].kind!=='ident')throw new SyntaxError('Unsupported CSS keyframe name');
        rules.push({kind:'keyframes',vendor:name,name:rest[0].value,rules:parseRules(body,{keyframes:true}),start:prelude[0].start,end});
      }else throw new SyntaxError(`Unsupported CSS at-rule ${name}`);
    }else{const selectors=splitTop(prelude,',');rules.push({kind:keyframes?'keyframe':'style',selectors,
      ...(keyframes?{}:{selectorAst:selectors.map(compileCssSelector)}),declarations:parseCssDeclarations(body),start:prelude[0]?.start??tokens[start].start,end});}
  }
  return rules;
}

export function compileCss(source,{name='stylesheet'}={}){
  const tokens=tokenizeCss(source),rules=parseRules(tokens);
  return {schema:'cookie-clicker-css-ast-v1',schemaVersion:1,name,sha256:createHash('sha256').update(source).digest('hex'),lengthUtf16:source.length,rules,cssSemanticsVerified:false};
}

export function compilePinnedStylesheets(directory=defaultGameSourceDirectory()){
  return Object.entries(CSS_SOURCE_HASHES).map(([name,expected])=>{
    const bytes=readFileSync(join(directory,name)),hash=createHash('sha256').update(bytes).digest('hex');
    if(hash!==expected)throw new Error(`Unsupported pinned stylesheet hash: ${name}`);
    return compileCss(bytes.toString('utf8'),{name});
  });
}

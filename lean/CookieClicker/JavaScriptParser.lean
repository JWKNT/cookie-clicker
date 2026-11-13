import CookieClicker.JavaScriptLexer
import CookieClicker.JavaScriptRegExp

/-! Source parsing into the shared interpreter syntax. The parser uses explicit
structural fuel, retains original function text, and distinguishes unsupported
grammar from recognized syntax errors. It does not assume that a native parser
returned a correct AST. Native-language correspondence remains a separate claim.
-/
namespace CookieClicker.JavaScript.Parser

abbrev Error := Lexer.Error

structure State where
  lexer : Lexer.State
  lookahead : Option Lexer.Token := none
  lastStop : Nat := 0
  strict : Bool := false
  legacySeen : Bool := false
  inFunction : Bool := false
  loopDepth : Nat := 0
  labels : List (String × Bool) := []
  deriving Repr

private def failAt (state : State) (message : String) (kind : Lexer.ErrorKind := .unsupported) : Except Error α :=
  .error ⟨kind,(state.lookahead.map (·.start)).getD state.lexer.offset,message⟩

private def exhausted (state : State) : Except Error α := failAt state "Parser structural fuel" .exhausted

private def peek (state : State) : Except Error (Lexer.Token × State) := do
  match state.lookahead with
  | some token => pure (token,state)
  | none =>
    let (token,lexer) ← Lexer.next state.lexer
    pure (token,{ state with lexer,lookahead := some token })

private def take (state : State) : Except Error (Lexer.Token × State) := do
  let (token,state) ← peek state
  if state.strict && token.legacy then failAt state "Legacy octal syntax in strict code" .syntax else
  pure (token,{ state with
    lookahead := none,lastStop := token.stop,legacySeen := state.legacySeen || token.legacy })

private def tokenText (token : Lexer.Token) : String :=
  match token.kind with | .identifier text | .punctuation text => text | _ => ""

private def expect (state : State) (text : String) : Except Error State := do
  let (token,state) ← take state
  if tokenText token == text then pure state else failAt state ("Expected " ++ text)

private def accept (state : State) (text : String) : Except Error (Bool × State) := do
  let (token,state) ← peek state
  if tokenText token == text then pure (true,(← take state).2) else pure (false,state)

private def reserved : List String :=
  ["break","case","catch","continue","debugger","default","delete","do","else","finally",
   "for","function","if","in","instanceof","new","return","switch","this","throw","try",
   "typeof","var","void","while","with","class","const","enum","export","extends","import",
   "super","null","true","false"]

private def strictReserved : List String :=
  ["implements","interface","let","package","private","protected","public","static","yield"]

private def bindingValid (strict : Bool) (name : String) : Bool :=
  !reserved.contains name && (!strict || (!strictReserved.contains name && name != "eval" && name != "arguments"))

private def identifierName (state : State) : Except Error (String × State) := do
  let (token,state) ← take state
  match token.kind with
  | .identifier name => pure (name,state)
  | _ => failAt state "Expected identifier name"

private def bindingName (state : State) : Except Error (String × State) := do
  let (name,state) ← identifierName state
  if bindingValid state.strict name then pure (name,state)
  else failAt state "Reserved or forbidden binding name" .syntax

private def labelName (state : State) : Except Error (String × State) := do
  let (name,state) ← identifierName state
  if reserved.contains name || (state.strict && strictReserved.contains name) then
    failAt state "Reserved statement label" .syntax
  else pure (name,state)

private def semicolon (state : State) : Except Error State := do
  let (token,state) ← peek state
  if tokenText token == ";" then pure (← take state).2
  else if token.kind == .eof || tokenText token == "}" || token.lineBreakBefore then pure state
  else failAt state "Expected statement terminator"

private def parenthesizedEnd (state : State) : Except Error State := expect state ")"

private def reference : Expr → Bool
  | .identifier _ | .member _ _ _ => true
  | _ => false

private def forbiddenStrictReference (strict : Bool) : Expr → Bool
  | .identifier name => strict && (name == "eval" || name == "arguments")
  | _ => false

private def assignmentOperator : String → Option AssignmentOp
  | "=" => some .assign | "+=" => some .add | "-=" => some .subtract
  | "*=" => some .multiply | "/=" => some .divide | "%=" => some .remainder
  | "<<=" => some .shiftLeft | ">>=" => some .shiftRight | ">>>=" => some .unsignedShiftRight
  | "|=" => some .bitOr | "^=" => some .bitXor | "&=" => some .bitAnd | _ => none

private def binaryOperator : String → Option (Nat × BinaryOp)
  | "|" => some (6,.bitOr) | "^" => some (7,.bitXor) | "&" => some (8,.bitAnd)
  | "==" => some (9,.equal) | "!=" => some (9,.notEqual)
  | "===" => some (9,.strictEqual) | "!==" => some (9,.strictNotEqual)
  | "<" => some (10,.less) | "<=" => some (10,.lessEqual)
  | ">" => some (10,.greater) | ">=" => some (10,.greaterEqual)
  | "in" => some (10,.inOp) | "instanceof" => some (10,.instanceOf)
  | "<<" => some (11,.shiftLeft) | ">>" => some (11,.shiftRight) | ">>>" => some (11,.unsignedShiftRight)
  | "+" => some (12,.add) | "-" => some (12,.subtract)
  | "*" => some (13,.multiply) | "/" => some (13,.divide) | "%" => some (13,.remainder)
  | _ => none

private def unaryOperator : String → Option UnaryOp
  | "delete" => some .delete | "void" => some .void | "typeof" => some .typeOf
  | "+" => some .plus | "-" => some .minus | "~" => some .bitNot | "!" => some .not | _ => none

private def propertyName (state : State) : Except Error (PropertyName × State) := do
  let (token,state) ← take state
  match token.kind with
  | .identifier name => pure (.identifier name,state)
  | .string text => pure (.string text,state)
  | .number bits => pure (.number bits,state)
  | _ => failAt state "Expected object property name"

private def regexLiteral (state : State) (token : Lexer.Token) : Except Error (Expr × State) := do
  let (token,lexer) ← Lexer.regexp state.lexer token
  let .regexp pattern flags := token.kind | failAt state "Regexp lexer result" .exhausted
  match RegExp.compile pattern flags with
  | .ok _ => pure (.regexp pattern flags,{ state with lexer,lookahead := none,lastStop := token.stop })
  | .error error => failAt state ("Regexp validation: " ++ reprStr error)

private def sequence (left right : Expr) : Expr :=
  match left with | .sequence prior => .sequence (prior ++ [right]) | _ => .sequence [left,right]

private def labelIteration : Nat → State → Except Error Bool
  | 0,state => exhausted state
  | fuel+1,state => do
    let (token,state) ← take state
    if ["while","do","for"].contains (tokenText token) then pure true else
    match token.kind with
    | .identifier _ =>
      let (colon,state) ← accept state ":"
      if colon then labelIteration fuel state else pure false
    | _ => pure false

structure FunctionParts where
  parameters : List String
  body : List Stmt
  strict : Bool
  sourceText : JSString
  deriving Repr

mutual
  private def expression : Nat → Nat → Bool → State → Except Error (Expr × State)
    | 0,_,_,state => exhausted state
    | fuel+1,minimum,allowIn,state => do
      let (left,state) ← prefixExpression fuel allowIn state
      infixLoop fuel minimum allowIn left state

  private def prefixExpression : Nat → Bool → State → Except Error (Expr × State)
    | 0,_,state => exhausted state
    | fuel+1,allowIn,state => do
      let (token,state) ← take state
      if token.escaped && reserved.contains (tokenText token) then failAt state "Escaped keyword" .syntax else
      match token.kind with
      | .number bits => pure (.literal (.number bits),state)
      | .string text => pure (.literal (.string text),state)
      | .identifier "null" => pure (.literal .null,state)
      | .identifier "true" => pure (.literal (.boolean true),state)
      | .identifier "false" => pure (.literal (.boolean false),state)
      | .identifier "this" => pure (.this,state)
      | .identifier "function" =>
        let (next,state) ← peek state
        let (name,state) ← if tokenText next == "(" then pure (none,state) else do
          let (name,state) ← bindingName state
          pure (some name,state)
        let (parts,state) ← functionParts fuel token.start name state
        pure (.function name parts.parameters parts.body parts.strict (some parts.sourceText),state)
      | .identifier "new" =>
        let (next,state) ← peek state
        if (unaryOperator (tokenText next)).isSome || ["++","--"].contains (tokenText next) then
          failAt state "Unary expression cannot be an unparenthesized new target" .syntax
        else
        let (target,state) ← expression fuel 17 allowIn state
        let (hasArguments,state) ← accept state "("
        let (arguments,state) ← if hasArguments then argumentsList fuel state [] else pure ([],state)
        pure (.construct target arguments,state)
      | .punctuation "(" =>
        let (inner,state) ← expression fuel 1 true state
        pure (inner,← parenthesizedEnd state)
      | .punctuation "[" => arrayElements fuel state []
      | .punctuation "{" => objectProperties fuel state []
      | .punctuation "/" | .punctuation "/=" => regexLiteral state token
      | _ =>
        if let some operator := unaryOperator (tokenText token) then
          let (argument,state) ← expression fuel 14 allowIn state
          if state.strict && operator == .delete && (match argument with | .identifier _ => true | _ => false) then
            failAt state "Delete of strict unqualified identifier" .syntax
          else pure (.unary operator argument,state)
        else if tokenText token == "++" || tokenText token == "--" then
          let (argument,state) ← expression fuel 14 allowIn state
          if !reference argument || forbiddenStrictReference state.strict argument then failAt state "Invalid update target" .syntax
          else pure (.update (if tokenText token == "++" then .increment else .decrement) argument true,state)
        else match token.kind with
          | .identifier name =>
            if reserved.contains name || (state.strict && strictReserved.contains name) then failAt state "Unsupported expression keyword"
            else pure (.identifier name,state)
          | .punctuation token =>
            if [")", "]", "}", ";", ":", ","].contains token then
              failAt state "Expected an expression" .syntax
            else failAt state "Unsupported expression prefix"
          | .eof => failAt state "Expected an expression before end of source" .syntax
          | _ => failAt state "Unsupported expression prefix"

  private def infixLoop (fuel minimum : Nat) (allowIn : Bool) (left : Expr) (state : State)
      (afterPostfix : Bool := false) : Except Error (Expr × State) :=
    match fuel with
    | 0 => exhausted state
    | fuel+1 => do
      let (token,state) ← peek state
      let text := tokenText token
      if text == "." && !afterPostfix then
        let state ← expect state "."
        let (name,state) ← identifierName state
        infixLoop fuel minimum allowIn (.member left (.identifier name) false) state
      else if text == "[" && !afterPostfix then
        let state ← expect state "["
        let (index,state) ← expression fuel 1 true state
        let state ← expect state "]"
        infixLoop fuel minimum allowIn (.member left index true) state
      else if text == "(" && minimum ≤ 16 && !afterPostfix then
        let state ← expect state "("
        let (arguments,state) ← argumentsList fuel state []
        infixLoop fuel minimum allowIn (.call left arguments) state
      else if (text == "++" || text == "--") && !token.lineBreakBefore && minimum ≤ 15 && !afterPostfix then
        if !reference left || forbiddenStrictReference state.strict left then failAt state "Invalid update target" .syntax else
        let state := (← take state).2
        infixLoop fuel minimum allowIn (.update (if text == "++" then .increment else .decrement) left false) state true
      else if text == "," && minimum ≤ 1 then
        let state ← expect state ","
        let (right,state) ← expression fuel 2 allowIn state
        infixLoop fuel minimum allowIn (sequence left right) state
      else if minimum ≤ 2 && (assignmentOperator text).isSome then
        if !reference left || forbiddenStrictReference state.strict left then failAt state "Invalid assignment target" .syntax else
        let state := (← take state).2
        let (right,state) ← expression fuel 2 allowIn state
        infixLoop fuel minimum allowIn (.assignment ((assignmentOperator text).getD .assign) left right) state
      else if text == "?" && minimum ≤ 3 then
        let state ← expect state "?"
        let (consequent,state) ← expression fuel 2 true state
        let state ← expect state ":"
        let (alternate,state) ← expression fuel 2 allowIn state
        infixLoop fuel minimum allowIn (.conditional left consequent alternate) state
      else if (text == "||" && minimum ≤ 4) || (text == "&&" && minimum ≤ 5) then
        let state := (← take state).2
        let (right,state) ← expression fuel (if text == "||" then 5 else 6) allowIn state
        infixLoop fuel minimum allowIn (.logical (if text == "||" then .or else .and) left right) state
      else match binaryOperator text with
        | some (precedence,operator) =>
          if precedence < minimum || (operator == .inOp && !allowIn) then pure (left,state) else
          if token.escaped then failAt state "Escaped operator keyword" .syntax else
          let state := (← take state).2
          let (right,state) ← expression fuel (precedence+1) allowIn state
          infixLoop fuel minimum allowIn (.binary operator left right) state
        | none => pure (left,state)

  private def argumentsList : Nat → State → List Expr → Except Error (List Expr × State)
    | 0,state,_ => exhausted state
    | fuel+1,state,reversed => do
      let (closed,state) ← accept state ")"
      if closed then pure (reversed.reverse,state) else
      let (argument,state) ← expression fuel 2 true state
      let (comma,state) ← accept state ","
      if comma then argumentsList fuel state (argument :: reversed)
      else pure ((argument :: reversed).reverse,← expect state ")")

  private def arrayElements : Nat → State → List (Option Expr) → Except Error (Expr × State)
    | 0,state,_ => exhausted state
    | fuel+1,state,reversed => do
      let (closed,state) ← accept state "]"
      if closed then pure (.array reversed.reverse,state) else
      let (hole,state) ← accept state ","
      if hole then arrayElements fuel state (none :: reversed) else
      let (element,state) ← expression fuel 2 true state
      let (comma,state) ← accept state ","
      if comma then arrayElements fuel state (some element :: reversed)
      else pure (.array (some element :: reversed).reverse,← expect state "]")

  private def objectProperties : Nat → State → List ObjectProperty → Except Error (Expr × State)
    | 0,state,_ => exhausted state
    | fuel+1,state,reversed => do
      let (closed,state) ← accept state "}"
      if closed then pure (.object reversed.reverse,state) else
      let (first,state) ← peek state
      let (name,state) ← propertyName state
      let (colon,state) ← accept state ":"
      let (property,state) ← if colon then do
        let (value,state) ← expression fuel 2 true state
        pure (ObjectProperty.mk name .init value,state)
      else
        let kind ← match name with
          | .identifier "get" => pure PropertyKind.get
          | .identifier "set" => pure PropertyKind.set
          | _ => failAt state "Object shorthand or method syntax"
        let (name,state) ← propertyName state
        let (parts,state) ← functionParts fuel first.start none state
        if parts.parameters.length != (if kind == .get then 0 else 1) then failAt state "Accessor parameter count" .syntax else
        pure (ObjectProperty.mk name kind (.function none parts.parameters parts.body parts.strict (some parts.sourceText)),state)
      let (comma,state) ← accept state ","
      if comma then objectProperties fuel state (property :: reversed)
      else pure (.object (property :: reversed).reverse,← expect state "}")

  private def parameters : Nat → State → List String → Except Error (List String × State)
    | 0,state,_ => exhausted state
    | fuel+1,state,reversed => do
      let (closed,state) ← accept state ")"
      if closed then pure (reversed.reverse,state) else
      let (name,state) ← bindingName state
      let (comma,state) ← accept state ","
      if comma then parameters fuel state (name :: reversed)
      else pure ((name :: reversed).reverse,← expect state ")")

  private def functionParts : Nat → Nat → Option String → State → Except Error (FunctionParts × State)
    | 0,_,_,state => exhausted state
    | fuel+1,start,name,state => do
      let outer := state
      let state := { state with inFunction := true,loopDepth := 0,labels := [],legacySeen := false }
      let state ← expect state "("
      let (names,state) ← parameters fuel state []
      let state ← expect state "{"
      let (body,state) ← statementList fuel true true state []
      let state ← expect state "}"
      if state.strict && ((!names.all (bindingValid true)) || name.any (!bindingValid true ·) || names.eraseDups.length != names.length) then
        failAt state "Strict function binding or duplicate parameter" .syntax
      else
        let parts : FunctionParts := ⟨names,body,state.strict,Lexer.slice state.lexer start state.lastStop⟩
        pure (parts,{ state with
          strict := outer.strict,legacySeen := outer.legacySeen,inFunction := outer.inFunction,
          loopDepth := outer.loopDepth,labels := outer.labels })

  private def declarations : Nat → Bool → State → List (String × Option Expr) → Except Error (List (String × Option Expr) × State)
    | 0,_,state,_ => exhausted state
    | fuel+1,allowIn,state,reversed => do
      let (name,state) ← bindingName state
      let (initialized,state) ← accept state "="
      let (value,state) ← if initialized then do
        let (value,state) ← expression fuel 2 allowIn state
        pure (some value,state)
        else pure (none,state)
      let (comma,state) ← accept state ","
      if comma then declarations fuel allowIn state ((name,value) :: reversed)
      else pure (((name,value) :: reversed).reverse,state)

  private def statementList : Nat → Bool → Bool → State → List Stmt → Except Error (List Stmt × State)
    | 0,_,_,state,_ => exhausted state
    | fuel+1,braced,prologue,state,reversed => do
      let (first,state) ← peek state
      if first.kind == .eof || (braced && tokenText first == "}") then pure (reversed.reverse,state) else
      let (item,state) ← statement fuel state
      let directive := prologue && (match first.kind,item with
        | .string _,.expression (.literal (.string _)) => true | _,_ => false)
      let strictDirective := directive && !first.escaped &&
        (match first.kind with | .string text => text == JSString.ofString "use strict" | _ => false)
      if strictDirective && state.legacySeen then failAt state "Legacy escape before strict directive" .syntax else
      statementList fuel braced directive { state with strict := state.strict || strictDirective } (item :: reversed)

  private def statement : Nat → State → Except Error (Stmt × State)
    | 0,state => exhausted state
    | fuel+1,state => do
      let (token,state) ← peek state
      if token.escaped && reserved.contains (tokenText token) then failAt state "Escaped statement keyword" .syntax else
      let text := tokenText token
      if text == ";" then pure (.empty,(← take state).2)
      else if text == "{" then
        let state ← expect state "{"
        let (body,state) ← statementList fuel true false state []
        pure (.block body,← expect state "}")
      else if text == "var" then
        let state ← expect state "var"
        let (variables,state) ← declarations fuel true state []
        pure (.variable variables,← semicolon state)
      else if text == "function" then
        let state ← expect state "function"
        let (name,state) ← bindingName state
        let (parts,state) ← functionParts fuel token.start (some name) state
        pure (.functionDeclaration name parts.parameters parts.body parts.strict (some parts.sourceText),state)
      else if text == "if" then
        let state ← expect (← expect state "if") "("
        let (test,state) ← expression fuel 1 true state
        let state ← expect state ")"
        let (yes,state) ← statement fuel state
        let (hasElse,state) ← accept state "else"
        let (no,state) ← if hasElse then do
          let (no,state) ← statement fuel state
          pure (some no,state)
          else pure (none,state)
        pure (.ifThenElse test yes no,state)
      else if text == "while" then
        let state ← expect (← expect state "while") "("
        let (test,state) ← expression fuel 1 true state
        let state ← expect state ")"
        let depth := state.loopDepth
        let (body,state) ← statement fuel { state with loopDepth := depth+1 }
        pure (.while test body,{ state with loopDepth := depth })
      else if text == "do" then
        let state ← expect state "do"
        let depth := state.loopDepth
        let (body,state) ← statement fuel { state with loopDepth := depth+1 }
        let state ← expect (← expect { state with loopDepth := depth } "while") "("
        let (test,state) ← expression fuel 1 true state
        let state ← expect state ")"
        pure (.doWhile body test,(← accept state ";").2)
      else if text == "for" then forStatement fuel (← expect (← expect state "for") "(")
      else if text == "return" || text == "throw" then
        let state := (← take state).2
        let (next,state) ← peek state
        if text == "return" && !state.inFunction then failAt state "Return outside function" .syntax else
        if text == "throw" && next.lineBreakBefore then failAt state "Line break after throw" .syntax else
        let empty := next.lineBreakBefore || next.kind == .eof || [";","}"].contains (tokenText next)
        if empty && text == "return" then pure (.return none,← semicolon state) else
        let (value,state) ← expression fuel 1 true state
        pure ((if text == "return" then .return (some value) else .throw value),← semicolon state)
      else if text == "break" || text == "continue" then
        let state := (← take state).2
        let (next,state) ← peek state
        let (label,state) ← match next.kind with
          | .identifier _ => do
            if next.lineBreakBefore then pure (none,state) else
            let (label,state) ← identifierName state
            pure (some label,state)
          | _ => pure (none,state)
        let valid := match label with
          | none => state.loopDepth > 0
          | some label => state.labels.any (fun entry => entry.1 == label && (text == "break" || entry.2))
        if !valid then failAt state "Invalid break or continue target" .syntax else
        pure ((if text == "break" then .break label else .continue label),← semicolon state)
      else if text == "try" then tryStatement fuel (← expect state "try")
      else if ["switch","with","debugger","class","const","import","export"].contains text then
        failAt state ("Statement grammar not implemented: " ++ text)
      else
        let candidate ← match token.kind with
          | .identifier _ => do
            let (_,after) ← take state
            pure (tokenText (← peek after).1 == ":")
          | _ => pure false
        if candidate then
          let (label,state) ← labelName state
          if state.labels.any (fun entry => entry.1 == label) then failAt state "Duplicate statement label" .syntax else
          let state ← expect state ":"
          let isIteration ← labelIteration fuel state
          let labels := state.labels
          let (body,state) ← statement fuel { state with labels := (label,isIteration) :: labels }
          pure (.labeled label body,{ state with labels })
        else
          let (value,state) ← expression fuel 1 true state
          pure (.expression value,← semicolon state)

  private def forStatement : Nat → State → Except Error (Stmt × State)
    | 0,state => exhausted state
    | fuel+1,state => do
      let (next,state) ← peek state
      let (initial,state) ← if tokenText next == ";" then pure (none,state)
        else if tokenText next == "var" then do
          let state ← expect state "var"
          let (variables,state) ← declarations fuel false state []
          pure (some (ForInit.variables variables),state)
        else do
          let (value,state) ← expression fuel 1 false state
          pure (some (ForInit.expression value),state)
      let (isIn,state) ← accept state "in"
      if isIn then
        let binding ← match initial with
          | some (.variables [(name,none)]) => pure (ForInBinding.variable name)
          | some (.expression value) =>
            if reference value && !forbiddenStrictReference state.strict value then pure (.reference value)
            else failAt state "Invalid for-in assignment target" .syntax
          | _ => failAt state "Unsupported for-in initializer"
        let (object,state) ← expression fuel 1 true state
        let state ← expect state ")"
        let depth := state.loopDepth
        let (body,state) ← statement fuel { state with loopDepth := depth+1 }
        pure (.forIn binding object body,{ state with loopDepth := depth })
      else
        let state ← expect state ";"
        let (next,state) ← peek state
        let (test,state) ← if tokenText next == ";" then pure (none,state) else do
          let (value,state) ← expression fuel 1 true state
          pure (some value,state)
        let state ← expect state ";"
        let (next,state) ← peek state
        let (update,state) ← if tokenText next == ")" then pure (none,state) else do
          let (value,state) ← expression fuel 1 true state
          pure (some value,state)
        let state ← expect state ")"
        let depth := state.loopDepth
        let (body,state) ← statement fuel { state with loopDepth := depth+1 }
        pure (.forLoop initial test update body,{ state with loopDepth := depth })

  private def blockStatement (fuel : Nat) (state : State) : Except Error (Stmt × State) := do
    let (next,state) ← peek state
    if tokenText next != "{" then failAt state "Expected statement block" else statement fuel state

  private def tryStatement : Nat → State → Except Error (Stmt × State)
    | 0,state => exhausted state
    | fuel+1,state => do
      let (body,state) ← blockStatement fuel state
      let (hasCatch,state) ← accept state "catch"
      let (handler,state) ← if hasCatch then do
        let state ← expect state "("
        let (name,state) ← bindingName state
        let state ← expect state ")"
        let (handler,state) ← blockStatement fuel state
        pure (some (name,handler),state)
        else pure (none,state)
      let (hasFinally,state) ← accept state "finally"
      let (finalizer,state) ← if hasFinally then do
        let (body,state) ← blockStatement fuel state
        pure (some body,state)
        else pure (none,state)
      if !hasCatch && !hasFinally then failAt state "Try requires catch or finally" .syntax else
      pure (.tryCatchFinally body handler finalizer,state)
end

/-- Parse a script with source-sized diagnostic fuel. No parser budget is a
bound on game actions or source execution time. -/
def parseSource (source : JSString) (inFunction : Bool) (fuel : Nat) : Except Error Program := do
  let (body,state) ← statementList fuel false true { lexer := Lexer.initial source,inFunction } []
  let (last,state) ← peek state
  if last.kind != .eof then failAt state "Source remains after parsed program" else
  pure { body,strict := state.strict }

def parse (source : JSString) (fuel : Nat := 16*source.length+64) : Except Error Program :=
  parseSource source false fuel

/-- Handler text and dynamic-function bodies permit top-level return. Their
lexical environment is supplied separately by the actual host operation. -/
def parseFunctionBody (source : JSString) (fuel : Nat := 16*source.length+64) : Except Error Program :=
  parseSource source true fuel

/-- Parse formal parameter text independently of a dynamic function body.
The terminating newline is the native Function-constructor boundary, so a
line comment may end a parameter string, but cannot consume the body. -/
def parseFormalParameters (source : JSString) (fuel : Nat := 16*source.length+64) : Except Error (List String) := do
  let (names,state) ← parameters fuel { lexer := Lexer.initial (source ++ JSString.ofString "\n)") } []
  let (last,state) ← peek state
  if last.kind != .eof then failAt state "Unexpected source after formal parameter list" .syntax else
  pure names

def formalParametersValid (strict : Bool) (names : List String) : Bool :=
  names.all (bindingValid strict) && (!strict || names.eraseDups.length == names.length)

end CookieClicker.JavaScript.Parser

import CookieClicker.JavaScriptHtmlEntities

/-! Explicit-context HTML fragment parser for ordinary source-generated markup.
Unsupported insertion modes and error-recovery rules return an unresolved parse
request. Parsed script text and event attributes are data, never callbacks.
This is not a claim of equivalence to the complete browser HTML parser.
-/
namespace CookieClicker.JavaScript.DomSyntax

structure Attribute where
  name : String
  value : JSString
  deriving Repr, DecidableEq

inductive Node where
  | text (value : JSString)
  | comment (value : JSString)
  | element (name : String) (attributes : List Attribute) (children : List Node)
  deriving Repr

inductive ParseError where
  | unsupported (message : String) (offset : Nat)
  | fuel
  deriving Repr, DecidableEq

private def asciiLower (unit : UInt16) : UInt16 :=
  if 65 ≤ unit.toNat && unit.toNat ≤ 90 then UInt16.ofNat (unit.toNat + 32) else unit
private def whitespace (unit : UInt16) := [9,10,12,13,32].contains unit.toNat
private def alphabetic (unit : UInt16) :=
  (65 ≤ unit.toNat && unit.toNat ≤ 90) || (97 ≤ unit.toNat && unit.toNat ≤ 122)
private def alphanumeric (unit : UInt16) := alphabetic unit || (48 ≤ unit.toNat && unit.toNat ≤ 57)
private def nameString (units : JSString) := String.ofList (units.map (fun u => Char.ofNat u.toNat))
private def key := JSString.ofString
private def starts (input : Array UInt16) (offset : Nat) (text : JSString) : Bool :=
  text.zipIdx.all (fun (unit, i) => input[offset + i]? == some unit)
private def startsLower (input : Array UInt16) (offset : Nat) (text : JSString) : Bool :=
  text.zipIdx.all (fun (unit, i) => (input[offset + i]?).map asciiLower == some unit)
private def slice (input : Array UInt16) (first last : Nat) : JSString :=
  (input.toList.drop first).take (last - first)

/-- HTML preprocessing folds literal CR/CRLF; references that decode to CR are
processed later and therefore retain that character. -/
def preprocess : JSString → JSString
  | [] => []
  | 13 :: 10 :: rest => 10 :: preprocess rest
  | 13 :: rest => 10 :: preprocess rest
  | first :: rest => first :: preprocess rest

private def numericReplacement (value : Nat) : JSString :=
  let value := if value == 0 || value > 0x10ffff || (0xd800 ≤ value && value ≤ 0xdfff) then 0xfffd
    else if value == 0x80 then 0x20ac else if value == 0x82 then 0x201a
    else if value == 0x83 then 0x192 else if value == 0x84 then 0x201e
    else if value == 0x85 then 0x2026 else if value == 0x86 then 0x2020
    else if value == 0x87 then 0x2021 else if value == 0x88 then 0x2c6
    else if value == 0x89 then 0x2030 else if value == 0x8a then 0x160
    else if value == 0x8b then 0x2039 else if value == 0x8c then 0x152
    else if value == 0x8e then 0x17d else if value == 0x91 then 0x2018
    else if value == 0x92 then 0x2019 else if value == 0x93 then 0x201c
    else if value == 0x94 then 0x201d else if value == 0x95 then 0x2022
    else if value == 0x96 then 0x2013 else if value == 0x97 then 0x2014
    else if value == 0x98 then 0x2dc else if value == 0x99 then 0x2122
    else if value == 0x9a then 0x161 else if value == 0x9b then 0x203a
    else if value == 0x9c then 0x153 else if value == 0x9e then 0x17e
    else if value == 0x9f then 0x178 else value
  if value < 0x10000 then [UInt16.ofNat value]
  else [UInt16.ofNat (0xd800 + (value - 0x10000) / 1024), UInt16.ofNat (0xdc00 + (value - 0x10000) % 1024)]

private def digit (hexadecimal : Bool) (unit : UInt16) : Option Nat :=
  if 48 ≤ unit.toNat && unit.toNat ≤ 57 then some (unit.toNat - 48)
  else if hexadecimal && 65 ≤ unit.toNat && unit.toNat ≤ 70 then some (unit.toNat - 55)
  else if hexadecimal && 97 ≤ unit.toNat && unit.toNat ≤ 102 then some (unit.toNat - 87)
  else none

private def readNumber (input : Array UInt16) (hexadecimal : Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, offset, value => (offset, value)
  | fuel + 1, offset, value => match input[offset]? >>= digit hexadecimal with
    | none => (offset, value)
    | some n => readNumber input hexadecimal fuel (offset + 1) ((if hexadecimal then 16 else 10) * value + n)

private def namedLookup (name : String) : Nat → Nat → Nat → Option JSString
  | 0, _, _ => none
  | fuel + 1, low, high =>
    if low ≥ high then none else
    let middle := (low + high) / 2
    let candidate := HtmlEntities.entries[middle]?.getD ("", [])
    if candidate.1 == name then some candidate.2
    else if candidate.1 < name then namedLookup name fuel (middle + 1) high
    else namedLookup name fuel low middle

private def namedPrefix (input : Array UInt16) (first : Nat) : Nat → Nat → JSString →
    (Nat × JSString × Bool) → Nat × JSString × Bool
  | 0, _, _, best => best
  | fuel + 1, offset, prefixUnits, best =>
    match input[offset]? with
    | none => best
    | some unit =>
      if !alphanumeric unit && unit != 59 then best else
      let prefixUnits := prefixUnits ++ [unit]
      let best := match namedLookup (nameString prefixUnits) (HtmlEntities.entries.size + 1) 0 HtmlEntities.entries.size with
        | none => best
        | some value => (offset + 1 - first, value, unit == 59)
      if unit == 59 then best else namedPrefix input first fuel (offset + 1) prefixUnits best

private def entity (input : Array UInt16) (offset : Nat) (inAttribute : Bool) : JSString × Nat :=
  if input[offset + 1]? == some 35 then
    let hexadecimal := input[offset + 2]? == some 120 || input[offset + 2]? == some 88
    let first := offset + if hexadecimal then 3 else 2
    let (after, value) := readNumber input hexadecimal input.size first 0
    if after == first then ([38], offset + 1)
    else (numericReplacement value, after + if input[after]? == some 59 then 1 else 0)
  else
    let best := namedPrefix input (offset + 1) (input.size + 1) (offset + 1) [] (0, [], false)
    if best.1 == 0 || (inAttribute && !best.2.2 &&
        (input[offset + 1 + best.1]?).any (fun u => alphanumeric u || u == 61)) then ([38], offset + 1)
    else (best.2.1, offset + 1 + best.1)

private def decodeLoop (input : Array UInt16) (inAttribute : Bool) : Nat → Nat → JSString → Except ParseError JSString
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, output =>
    if offset ≥ input.size then pure output
    else if input[offset]? == some 0 then throw (.unsupported "Literal null character requires tokenizer error recovery" offset)
    else if input[offset]? == some 38 then
      let (value, next) := entity input offset inAttribute
      decodeLoop input inAttribute fuel next (output ++ value)
    else decodeLoop input inAttribute fuel (offset + 1) (output ++ [input[offset]?.getD 0])

def decodeEntities (input : JSString) (inAttribute : Bool := false) : Except ParseError JSString :=
  decodeLoop input.toArray inAttribute (input.length + 2) 0 []

structure Tag where
  name : String
  attributes : List Attribute := []
  closing : Bool := false
  selfClosing : Bool := false
  after : Nat
  deriving Repr

private def skipSpace (input : Array UInt16) : Nat → Nat → Nat
  | 0, offset => offset
  | fuel + 1, offset => if (input[offset]?).any whitespace then skipSpace input fuel (offset + 1) else offset

private def readName (input : Array UInt16) (isAttribute : Bool) : Nat → Nat → JSString → Except ParseError (String × Nat)
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, units => do
    let some unit := input[offset]? | return (nameString units, offset)
    if whitespace unit || unit == 47 || unit == 62 || (isAttribute && unit == 61) then return (nameString units, offset)
    if unit.toNat > 127 || [0,34,39,60,96].contains unit.toNat then
      throw (.unsupported "Non-ASCII or malformed HTML name" offset)
    readName input isAttribute fuel (offset + 1) (units ++ [asciiLower unit])

private def quotedEnd (input : Array UInt16) (quote : UInt16) : Nat → Nat → Except ParseError Nat
  | 0, _ => throw .fuel
  | fuel + 1, offset =>
    if offset ≥ input.size then throw (.unsupported "Unclosed quoted attribute" offset)
    else if input[offset]? == some quote then pure offset
    else quotedEnd input quote fuel (offset + 1)

private def unquotedEnd (input : Array UInt16) : Nat → Nat → Except ParseError Nat
  | 0, _ => throw .fuel
  | fuel + 1, offset => do
    let some unit := input[offset]? | return offset
    if whitespace unit || unit == 62 then return offset
    if [0,34,39,60,61,96].contains unit.toNat then throw (.unsupported "Malformed unquoted attribute" offset)
    unquotedEnd input fuel (offset + 1)

private def attributes (input : Array UInt16) : Nat → Nat → List Attribute → Except ParseError (List Attribute × Bool × Nat)
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, found => do
    let offset := skipSpace input input.size offset
    if input[offset]? == some 62 then return (found, false, offset + 1)
    if starts input offset (key "/>") then return (found, true, offset + 2)
    if offset ≥ input.size then throw (.unsupported "Unclosed start tag" offset)
    let (name, afterName) ← readName input true (input.size + 1) offset []
    if name.isEmpty then throw (.unsupported "Malformed attribute boundary" offset)
    let beforeValue := skipSpace input input.size afterName
    let (value, after) ← if input[beforeValue]? == some 61 then do
      let first := skipSpace input input.size (beforeValue + 1)
      let quoted := input[first]? == some 34 || input[first]? == some 39
      let start := first + if quoted then 1 else 0
      let finish ← if quoted then quotedEnd input (input[first]?.getD 0) (input.size + 1) start
        else unquotedEnd input (input.size + 1) start
      let value ← decodeEntities (slice input start finish) true
      pure (value, finish + if quoted then 1 else 0)
    else pure ([], beforeValue)
    let found := if found.any (fun attr => attr.name == name) then found else found ++ [⟨name, value⟩]
    attributes input fuel after found

private def parseTag (input : Array UInt16) (offset : Nat) : Except ParseError Tag := do
  let closing := input[offset + 1]? == some 47
  let first := offset + if closing then 2 else 1
  let (name, afterName) ← readName input false (input.size + 1) first []
  if name.isEmpty then throw (.unsupported "Empty HTML tag name" offset)
  let (attrs, selfClosing, after) ← attributes input (input.size + 1) afterName []
  return ⟨name, attrs, closing, selfClosing, after⟩

private def voidNames := ["area","base","br","col","embed","hr","img","input","link","meta","param","source","track","wbr"]
private def rawNames := ["style","script","xmp","iframe","noembed","noframes"]
private def rcdataNames := ["textarea","title"]
private def supportedNames := ["a","b","i","u","q","div","span","small","h1","h2","h3","h4","h5","h6",
  "button","label","canvas","p","pre","listing","ul","ol","li","dl","dd","dt",
  "select","option","optgroup","sig","id","noclose"] ++ voidNames ++ rawNames ++ rcdataNames
private def unsupportedNames := ["html","head","body","table","tbody","thead","tfoot","tr","td","th","caption","colgroup","col","template","svg","math","frameset","frame","plaintext","noscript"]
private def formattingNames := ["a","b","big","code","em","font","i","nobr","s","small","strike","strong","tt","u"]
private def blockNames := ["address","article","aside","blockquote","center","details","dialog","dir","div","dl","fieldset","figcaption","figure","footer","header","hgroup","main","menu","nav","ol","p","section","summary","ul","h1","h2","h3","h4","h5","h6","pre","listing","hr"]

structure OpenElement where
  name : String
  attributes : List Attribute := []
  reversedChildren : List Node := []
  deriving Repr

private def appendNode (openElements : List OpenElement) (node : Node) : List OpenElement :=
  match openElements with
  | [] => []
  | head :: tail =>
    let children := match node, head.reversedChildren with
      | .text [], children => children
      | .text next, .text previous :: children => .text (previous ++ next) :: children
      | _, children => node :: children
    { head with reversedChildren := children } :: tail

private def closeTop : List OpenElement → List OpenElement
  | top :: parent :: rest => appendNode (parent :: rest) (.element top.name top.attributes top.reversedChildren.reverse)
  | other => other

private def finish : Nat → List OpenElement → Except ParseError (List Node)
  | 0, _ => throw .fuel
  | _, [] => pure []
  | _, [root] => pure root.reversedChildren.reverse
  | fuel + 1, elements => finish fuel (closeTop elements)

private def findTextEnd (input : Array UInt16) : Nat → Nat → Nat
  | 0, offset => offset
  | fuel + 1, offset =>
    if offset ≥ input.size || input[offset]? == some 60 then offset else findTextEnd input fuel (offset + 1)

private def findClosing (input : Array UInt16) (name : String) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, offset =>
    if offset ≥ input.size then none
    else if startsLower input offset (key ("</" ++ name)) &&
        (input[offset + name.length + 2]?).any (fun u => whitespace u || u == 47 || u == 62) then some offset
    else findClosing input name fuel (offset + 1)

private def commentEnd (input : Array UInt16) : Nat → Nat → Except ParseError (Nat × Nat)
  | 0, _ => throw .fuel
  | fuel + 1, offset =>
    if offset ≥ input.size then pure (offset, offset)
    else if starts input offset (key "-->") then pure (offset, offset + 3)
    else if starts input offset (key "--!") || starts input offset (key "<!--") then
      throw (.unsupported "Noncanonical comment tokenizer state" offset)
    else commentEnd input fuel (offset + 1)

private def parseLoop (input : Array UInt16) : Nat → Nat → List OpenElement → Except ParseError (List Node)
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, openElements => do
    if offset ≥ input.size then return ← finish (openElements.length + 1) openElements
    let current := (openElements.head?).map (·.name) |>.getD ""
    if input[offset]? != some 60 then
      let after := findTextEnd input input.size offset
      let value ← decodeEntities (slice input offset after)
      let initialPre := openElements.length > 1 && ["pre", "listing"].contains current &&
        (openElements.head?).any (fun element => element.reversedChildren.isEmpty)
      let value := if initialPre && value.head? == some 10 then value.drop 1 else value
      return ← parseLoop input fuel after (appendNode openElements (.text value))
    if starts input offset (key "<!--") then
      if starts input (offset + 4) (key ">") || starts input (offset + 4) (key "->") then
        throw (.unsupported "Abrupt comment start tokenizer state" offset)
      let (finish, after) ← commentEnd input (input.size + 1) (offset + 4)
      let text := slice input (offset + 4) finish
      if text.contains 0 then throw (.unsupported "Null in comment" offset)
      return ← parseLoop input fuel after (appendNode openElements (.comment text))
    let closing := input[offset + 1]? == some 47
    let nameStart := offset + if closing then 2 else 1
    if !(input[nameStart]?).any alphabetic then
      if (input[offset + 1]?).any (fun u => u == 33 || u == 63 || u == 47) then
        throw (.unsupported "Declaration or malformed tag tokenizer state" offset)
      return ← parseLoop input fuel (offset + 1) (appendNode openElements (.text [60]))
    let tag ← parseTag input offset
    if unsupportedNames.contains tag.name || !supportedNames.contains tag.name then
      throw (.unsupported ("Unsupported insertion mode for " ++ tag.name) offset)
    if tag.closing then
      if tag.name == "br" then return ← parseLoop input fuel tag.after (appendNode openElements (.element "br" [] []))
      if openElements.length > 1 && current == tag.name then
        return ← parseLoop input fuel tag.after (closeTop openElements)
      if openElements.any (fun element => element.name == tag.name) || formattingNames.contains tag.name || tag.name == "p" then
        throw (.unsupported "End tag needs scope or formatting error recovery" offset)
      return ← parseLoop input fuel tag.after openElements
    if current == "select" || current == "option" || current == "optgroup" then
      if !["option","optgroup"].contains tag.name then throw (.unsupported "Non-option token in select insertion mode" offset)
      if current == "option" || (current == "optgroup" && tag.name == "optgroup") then
        throw (.unsupported "Implicit option or optgroup close" offset)
    if (blockNames.contains tag.name && openElements.any (fun e => e.name == "p")) ||
        (["a","button","li","dd","dt","select"].contains tag.name && openElements.any (fun e => e.name == tag.name)) ||
        (["dd","dt"].contains tag.name && openElements.any (fun e => ["dd","dt"].contains e.name)) ||
        (tag.name == "xmp" && openElements.any (fun e => e.name == "p")) ||
        (["h1","h2","h3","h4","h5","h6"].contains tag.name && ["h1","h2","h3","h4","h5","h6"].contains current) then
      throw (.unsupported "Start tag needs implicit close or formatting reconstruction" offset)
    if voidNames.contains tag.name then
      return ← parseLoop input fuel tag.after (appendNode openElements (.element tag.name tag.attributes []))
    if rawNames.contains tag.name || rcdataNames.contains tag.name then
      let finish := (findClosing input tag.name (input.size + 1) tag.after).getD input.size
      let content := slice input tag.after finish
      if tag.name == "script" && content.toArray.toList.zipIdx.any (fun (_, i) => starts content.toArray i (key "<!--")) then
        throw (.unsupported "Escaped script tokenizer states" tag.after)
      let content ← if rcdataNames.contains tag.name then decodeEntities content
        else if content.contains 0 then throw (.unsupported "Null in raw text" tag.after) else pure content
      let content := if tag.name == "textarea" && content.head? == some 10 then content.drop 1 else content
      let after ← if finish == input.size then pure finish else do
        let closing ← parseTag input finish
        pure closing.after
      let children := if content.isEmpty then [] else [.text content]
      return ← parseLoop input fuel after (appendNode openElements (.element tag.name tag.attributes children))
    -- Self-closing syntax on ordinary HTML elements is ignored by the HTML parser.
    parseLoop input fuel tag.after (⟨tag.name, tag.attributes, []⟩ :: openElements)

def parseFragment (contextTag : String) (source : JSString) (fuel : Nat := 100000) : Except ParseError (List Node) := do
  let context := nameString ((key contextTag).map asciiLower)
  if unsupportedNames.contains context && context != "body" then throw (.unsupported ("Unsupported fragment context " ++ context) 0)
  let input := preprocess source
  if rawNames.contains context || rcdataNames.contains context then
    if (findClosing input.toArray context (input.length + 1) 0).isSome then
      throw (.unsupported "Context raw-text end token requires fragment tokenizer state" 0)
    let text ← if rcdataNames.contains context then decodeEntities input
      else if input.contains 0 then throw (.unsupported "Null in raw-text context" 0) else pure input
    return if text.isEmpty then [] else [.text text]
  parseLoop input.toArray fuel 0 [⟨context, [], []⟩]

inductive DocumentNode where
  | doctype
  | content (node : Node)
  deriving Repr

private def boundary (input : Array UInt16) (retainWhitespace : Bool) : Nat → Nat → List Node →
    Except ParseError (List Node × Nat)
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, nodes => do
    if offset ≥ input.size then return (nodes, offset)
    if (input[offset]?).any whitespace then
      let after := skipSpace input input.size offset
      let nodes := if retainWhitespace then nodes ++ [.text (slice input offset after)] else nodes
      return ← boundary input retainWhitespace fuel after nodes
    if starts input offset (key "<!--") then
      if starts input (offset + 4) (key ">") || starts input (offset + 4) (key "->") then
        throw (.unsupported "Abrupt document comment" offset)
      let (finish, after) ← commentEnd input (input.size + 1) (offset + 4)
      let text := slice input (offset + 4) finish
      if text.contains 0 then throw (.unsupported "Null in document comment" offset)
      return ← boundary input retainWhitespace fuel after (nodes ++ [.comment text])
    return (nodes, offset)

private def requireTag (input : Array UInt16) (offset : Nat) (name : String) (closing : Bool := false) : Except ParseError Tag := do
  if input[offset]? != some 60 then throw (.unsupported ("Expected explicit " ++ name ++ " document boundary") offset)
  let tag ← parseTag input offset
  if tag.name != name || tag.closing != closing then
    throw (.unsupported ("Expected explicit " ++ name ++ " document boundary") offset)
  return tag

private def scanDocumentClose (input : Array UInt16) (rootName : String) : Nat → Nat → List String → Except ParseError Nat
  | 0, _, _ => throw .fuel
  | fuel + 1, offset, stack => do
    if offset ≥ input.size then throw (.unsupported ("Missing explicit closing " ++ rootName) offset)
    if input[offset]? != some 60 then
      let after := findTextEnd input input.size offset
      if rootName == "head" then
        let value ← decodeEntities (slice input offset after)
        if !value.all whitespace then throw (.unsupported "Non-whitespace text requires implicit head closure" offset)
      return ← scanDocumentClose input rootName fuel after stack
    if starts input offset (key "<!--") then
      let (_, after) ← commentEnd input (input.size + 1) (offset + 4)
      return ← scanDocumentClose input rootName fuel after stack
    let nameStart := offset + if input[offset + 1]? == some 47 then 2 else 1
    if !(input[nameStart]?).any alphabetic then
      if rootName == "head" || (input[offset + 1]?).any (fun u => u == 33 || u == 63 || u == 47) then
        throw (.unsupported "Unsupported document token" offset)
      return ← scanDocumentClose input rootName fuel (offset + 1) stack
    let tag ← parseTag input offset
    if tag.closing then
      if tag.name == rootName && stack.isEmpty then return offset
      match stack with
      | first :: rest =>
        if first != tag.name then throw (.unsupported "Document needs mismatched-tag recovery" offset)
        scanDocumentClose input rootName fuel tag.after rest
      | [] => throw (.unsupported "Unexpected document end tag" offset)
    else
      if rootName == "head" && !["base","link","meta","title","style","script","noframes"].contains tag.name then
        throw (.unsupported "Head token requires another insertion mode" offset)
      if rawNames.contains tag.name || rcdataNames.contains tag.name then
        let some close := findClosing input tag.name (input.size + 1) tag.after |
          throw (.unsupported "Unclosed raw-text element in document" offset)
        let closing ← parseTag input close
        return ← scanDocumentClose input rootName fuel closing.after stack
      if voidNames.contains tag.name then
        return ← scanDocumentClose input rootName fuel tag.after stack
      scanDocumentClose input rootName fuel tag.after (tag.name :: stack)

private def appendNodes (children : List Node) (nodes : List Node) : List Node :=
  match nodes.foldl appendNode [⟨"", [], children.reverse⟩] with
  | [element] => element.reversedChildren.reverse
  | _ => children

/-- Chromium 87 switches from an after-body insertion mode to body insertion
when it sees whitespace. Subsequent comments therefore belong to the body;
comments before that whitespace retain their outer location. -/
private def splitTrailing (nodes : List Node) : List Node × List Node :=
  let (_, inside, outside) := nodes.foldl (fun (active, inside, outside) node =>
    match node with
    | .text _ => (true, inside ++ [node], outside)
    | _ => if active then (active, inside ++ [node], outside)
      else (active, inside, outside ++ [node])) (false, [], [])
  (inside, outside)

/-- Strict UTF-8 HTML-file path: consumes the initial decoded BOM and accepts
explicit HTML/head/body boundaries. Script text is inert here; ordered source
execution is a separate browser transition. Recovery outside this subset fails
closed. Whitespace after body/html is inserted in the body as in native parsing. -/
def parseDocument (source : JSString) (fuel : Nat := 100000) : Except ParseError (List DocumentNode) := do
  let source := if source.head? == some 0xfeff then source.drop 1 else source
  let input := (preprocess source).toArray
  let (beforeDoctype, start) ← boundary input false fuel 0 []
  if !startsLower input start (key "<!doctype html>") then
    throw (.unsupported "Expected the explicit HTML doctype" start)
  let (beforeHtml, htmlStart) ← boundary input false fuel (start + 15) []
  let html ← requireTag input htmlStart "html"
  let (beforeHead, headStart) ← boundary input false fuel html.after []
  let head ← requireTag input headStart "head"
  let headEnd ← scanDocumentClose input "head" fuel head.after []
  let headChildren ← parseFragment "div" (slice input head.after headEnd) fuel
  let headClose ← requireTag input headEnd "head" true
  let (between, bodyStart) ← boundary input true fuel headClose.after []
  let body ← requireTag input bodyStart "body"
  let bodyEnd ← scanDocumentClose input "body" fuel body.after []
  let bodyChildren ← parseFragment "body" (slice input body.after bodyEnd) fuel
  let bodyClose ← requireTag input bodyEnd "body" true
  let (afterBody, htmlEnd) ← boundary input true fuel bodyClose.after []
  let htmlClose ← requireTag input htmlEnd "html" true
  let (afterHtml, final) ← boundary input true fuel htmlClose.after []
  if final != input.size then throw (.unsupported "Unexpected content after document element" final)
  let (bodyTail, htmlComments) := splitTrailing afterBody
  let (bodyTailAfterHtml, documentComments) := splitTrailing afterHtml
  let bodyChildren := appendNodes bodyChildren (bodyTail ++ bodyTailAfterHtml)
  let htmlNode := Node.element "html" html.attributes
    (beforeHead ++ [.element "head" head.attributes headChildren] ++ between ++
      [.element "body" body.attributes bodyChildren] ++ htmlComments)
  return beforeDoctype.map DocumentNode.content ++ [.doctype] ++ beforeHtml.map DocumentNode.content ++
    [.content htmlNode] ++ documentComments.map DocumentNode.content

end CookieClicker.JavaScript.DomSyntax

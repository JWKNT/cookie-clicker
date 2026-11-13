import CookieClicker.JavaScriptCssSyntax

/-! Selector matching and author-rule ranking over explicit DOM data. Unknown
dynamic pseudo-classes stay unknown. A definite failed simple selector may rule
out a compound without guessing those dynamic states. -/
namespace CookieClicker.JavaScript.Css

structure Element where
  tag : JSString
  attributes : List (JSString × JSString)
  parent : Option Nat
  previous : Option Nat
  children : List Nat
  hasText : Bool
  documentRoot : Bool := false
  deriving Repr

abbrev Tree := Array (Option Element)

inductive Match where
  | yes | no | unknown (reason : String)
  deriving Repr, DecidableEq

def Match.and : Match → Match → Match
  | .no,_ | _,.no => .no
  | .yes,result | result,.yes => result
  | .unknown reason,.unknown _ => .unknown reason

def Match.or : Match → Match → Match
  | .yes,_ | _,.yes => .yes
  | .no,result | result,.no => result
  | .unknown reason,.unknown _ => .unknown reason

def Match.not : Match → Match
  | .yes => .no | .no => .yes | .unknown reason => .unknown reason

private def matchBool (b : Bool) : Match := if b then .yes else .no
private def key := JSString.ofString
private def attr (element : Element) (name : JSString) : Option JSString :=
  (element.attributes.find? (·.1 == name)).map (·.2)
private def lower (value : JSString) : JSString := value.map fun unit =>
  if 65 ≤ unit.toNat && unit.toNat ≤ 90 then UInt16.ofNat (unit.toNat+32) else unit
private def whitespace (unit : UInt16) : Bool := [9,10,12,13,32].contains unit.toNat
private def words (value : JSString) : List JSString :=
  (value.splitOnP whitespace).filter (!·.isEmpty)
private def starts (startText value : JSString) := value.take startText.length == startText
private def ends (suffix value : JSString) := value.drop (value.length-suffix.length) == suffix
private def contains (needle value : JSString) :=
  (List.range (value.length+1)).any (fun index => starts needle (value.drop index))

def specificityLE (a b : Specificity) : Bool :=
  a.ids < b.ids || (a.ids == b.ids && (a.classes < b.classes ||
    (a.classes == b.classes && a.types ≤ b.types)))

private def attrMatch (element : Element) (name : JSString) (operator : AttributeOperator)
    (value : JSString) (insensitive : Bool) : Match :=
  match attr element name with
  | none => .no
  | some actual =>
    if operator == .present then .yes else
    -- HTML has additional enumerated case-insensitive attribute values. Until
    -- those per-element tables are supplied, only explicit i or known textual
    -- attributes have a closed comparison here.
    if !insensitive && ![key "id",key "class",key "name",key "style",key "title"].contains name then
      .unknown "CSS HTML attribute-value case rules"
    else
      let actual := if insensitive then lower actual else actual
      let value := if insensitive then lower value else value
      match operator with
      | .present => .yes
      | .equal => matchBool (actual == value)
      | .word => matchBool (!value.isEmpty && !value.any whitespace && (words actual).contains value)
      | .prefixDash => matchBool (actual == value || starts (value ++ [45]) actual)
      | .prefix => matchBool (!value.isEmpty && starts value actual)
      | .suffix => matchBool (!value.isEmpty && ends value actual)
      | .substring => matchBool (!value.isEmpty && contains value actual)

private def nthIndex (tree : Tree) (id : Nat) (element : Element) : Option Nat := do
  let parent ← element.parent
  let parent ← (tree[parent]?).join
  let index ← parent.children.idxOf? id
  pure (index+1)

private def nthMatch (index : Nat) (arguments : Option (List Token)) : Match :=
  match arguments with
  | some [.ident name] =>
    if lower name == key "odd" then matchBool (index % 2 == 1)
    else if lower name == key "even" then matchBool (index % 2 == 0)
    else .unknown "CSS nth-child formula"
  | some [.number raw] =>
    match raw.toInt? with
    | some value => matchBool (value == Int.ofNat index)
    | none => .unknown "CSS nth-child numeric formula"
  | _ => .unknown "CSS nth-child formula"

mutual
  def matchSelector : Nat → Tree → Nat → Selector → Match
    | 0,_,_,_ => .unknown "CSS selector traversal fuel exhausted"
    | fuel+1,tree,id,.make parts _ valid =>
      if !valid then .no else matchParts fuel tree id parts.reverse

  def matchParts : Nat → Tree → Nat → List Compound → Match
    | 0,_,_,_ => .unknown "CSS selector traversal fuel exhausted"
    | _,_,_,[] => .yes
    | fuel+1,tree,id,.make relation simple :: rest =>
      match (tree[id]?).join with
      | none => .no
      | some element =>
        let own : Match := simple.foldl (fun result item => result.and (matchSimple fuel tree id element item)) Match.yes
        if own == .no then .no else
        let ancestors := match relation with
          | none => if rest.isEmpty then Match.yes else .unknown "CSS selector relation invariant"
          | some .child => match element.parent with
            | some parent => matchParts fuel tree parent rest | none => .no
          | some .nextSibling => match element.previous with
            | some previous => matchParts fuel tree previous rest | none => .no
          | some .descendant => matchRelated fuel tree element.parent rest true
          | some .followingSibling => matchRelated fuel tree element.previous rest false
        own.and ancestors

  def matchRelated : Nat → Tree → Option Nat → List Compound → Bool → Match
    | 0,_,_,_,_ => .unknown "CSS related-selector traversal fuel exhausted"
    | _,_,none,_,_ => .no
    | fuel+1,tree,some id,parts,ancestors =>
      let here := matchParts fuel tree id parts
      if here == .yes then .yes else
      match (tree[id]?).join with
      | none => here
      | some element => here.or (matchRelated fuel tree
        (if ancestors then element.parent else element.previous) parts ancestors)

  def matchSimple : Nat → Tree → Nat → Element → Simple → Match
    | 0,_,_,_,_ => .unknown "CSS simple-selector traversal fuel exhausted"
    | fuel+1,tree,id,element,simple =>
      match simple with
      | .universal => .yes
      | .type name => matchBool (element.tag == name)
      | .id name => matchBool (attr element (key "id") == some name)
      | .className name => matchBool ((words ((attr element (key "class")).getD [])).contains name)
      | .attribute name operator value insensitive => attrMatch element name operator value insensitive
      | .pseudoElement _ => .no
      | .negation selector => (matchSelector fuel tree id selector).not
      | .pseudoClass name arguments =>
        if name == "root" then matchBool element.documentRoot
        else if name == "empty" then matchBool (element.children.isEmpty && !element.hasText)
        else if name == "first-child" then matchBool element.previous.isNone
        else if name == "last-child" || name == "only-child" then
          let isLast := match element.parent with
            | none => true
            | some parent => ((tree[parent]?).join).any (fun parent => parent.children.getLast? == some id)
          matchBool (isLast && (name != "only-child" || element.previous.isNone))
        else if name == "nth-child" then
          match nthIndex tree id element with
          | some index => nthMatch index arguments
          | none => nthMatch 1 arguments
        else .unknown ("CSS dynamic pseudo-class: " ++ name)
end

structure Candidate where
  value : List Token
  important : Bool
  inline : Bool := false
  specificity : Specificity
  order : Nat
  deriving Repr

def candidateLE (a b : Candidate) : Bool :=
  if a.important != b.important then b.important
  else if a.inline != b.inline then b.inline
  else if a.specificity != b.specificity then specificityLE a.specificity b.specificity
  else a.order ≤ b.order

def winner (values : List Candidate) : Option Candidate :=
  values.foldl (fun best next => match best with
    | none => some next | some old => some (if candidateLE old next then next else old)) none

private def selectorSpecificity : Selector → Specificity
  | .make _ specificity _ => specificity
private def selectorValid : Selector → Bool
  | .make _ _ valid => valid

/-- Returns the greatest specificity of a matching selector. Unknown selectors
with no greater specificity than an already proved match cannot affect this. -/
def matchingSpecificity (tree : Tree) (id : Nat) (selectors : List Selector) : Except String (Option Specificity) := do
  if selectors.any (!selectorValid ·) then return none
  let outcomes := selectors.map fun selector =>
    (matchSelector (tree.size*4+1024) tree id selector,selectorSpecificity selector)
  let best : Option Specificity := outcomes.foldl (fun best pair => match pair.1,best with
    | .yes,none => some pair.2
    | .yes,some old => some (if specificityLE old pair.2 then pair.2 else old)
    | _,_ => best) none
  for (result,specificity) in outcomes do
    if let .unknown reason := result then
      if !best.any (specificityLE specificity ·) then throw reason
  return best

def ruleDeclarations : Rule → List Declaration
  | .style _ declarations => declarations | _ => []

/-- Only the caller's explicitly selected longhands are considered here. All
declarations, including invalid and duplicate source declarations, retain order.
Value grammar and shorthand expansion belong to the computed-style layer. -/
def collect (tree : Tree) (id : Nat) (sheets : List Stylesheet) (names : List String)
    : Except String (List (String × Candidate)) := do
  let mut output : List (String × Candidate) := []
  let mut order := 0
  for sheet in sheets do
    for rule in sheet.rules do
      match rule with
      | .style selectors declarations =>
        let relevant := declarations.any fun declaration => match declaration with
          | .valid name _ _ => names.contains name | _ => false
        if relevant then
          if let some specificity ← matchingSpecificity tree id selectors then
            for (declaration,index) in declarations.zipIdx do
              if let .valid name value important := declaration then
                if names.contains name then output := output ++ [(name,{ value := value,important := important,specificity := specificity,order := order+index })]
        order := order+declarations.length
      | _ => pure ()
  return output

theorem failed_simple_dominates_unknown (reason : String) :
    Match.and .no (.unknown reason) = .no := rfl

theorem proved_match_dominates_unknown (reason : String) :
    Match.or .yes (.unknown reason) = .yes := rfl

end CookieClicker.JavaScript.Css

import CookieClicker.JavaScriptSyntax

/-! Closed stylesheet data for source rules and positioned-box evaluation.
This syntax is distinct from the cascade and renderer semantics. -/
namespace CookieClicker.JavaScript.Css

inductive Token where
  | space
  | ident (value : JSString)
  | function (name : JSString)
  | number (raw : String)
  | dimension (raw : String) (unitName : JSString)
  | percentage (raw : String)
  | string (value : JSString)
  | url (value : JSString)
  | hash (name : JSString) (identifier : Bool)
  | delimiter (value : UInt16)
  | atKeyword (name : JSString)
  deriving Repr, DecidableEq

inductive Combinator where
  | descendant | child | nextSibling | followingSibling
  deriving Repr, DecidableEq

inductive AttributeOperator where
  | present | equal | word | prefixDash | prefix | suffix | substring
  deriving Repr, DecidableEq

structure Specificity where
  ids : Nat
  classes : Nat
  types : Nat
  deriving Repr, DecidableEq

mutual
  inductive Selector where
    | make (parts : List Compound) (specificity : Specificity) (valid : Bool)
    deriving Repr
  inductive Compound where
    | make (relation : Option Combinator) (simple : List Simple)
    deriving Repr
  inductive Simple where
    | universal
    | type (name : JSString)
    | id (name : JSString)
    | className (name : JSString)
    | attribute (name : JSString) (operator : AttributeOperator) (value : JSString) (asciiInsensitive : Bool)
    | pseudoClass (name : String) (arguments : Option (List Token))
    | pseudoElement (name : String)
    | negation (selector : Selector)
    deriving Repr
end

inductive Declaration where
  | valid (name : String) (value : List Token) (important : Bool)
  | invalid (tokens : List Token)
  deriving Repr

structure Keyframe where
  selectors : List (List Token)
  declarations : List Declaration
  deriving Repr

inductive Rule where
  | style (selectors : List Selector) (declarations : List Declaration)
  | fontFace (declarations : List Declaration)
  | keyframes (vendor : String) (name : JSString) (frames : List Keyframe)
  deriving Repr

structure Stylesheet where
  name : String
  sourceHash : String
  sourceLength : Nat
  rules : List Rule
  deriving Repr

end CookieClicker.JavaScript.Css

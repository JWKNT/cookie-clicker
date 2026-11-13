import CookieClicker.JavaScriptLocLocals

namespace CookieClicker.JavaScript.LocPrefix
open LocLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def body : List Stmt := LocSource.body
def selected : Expr := .member (.identifier "locStrings") (.identifier "id") true
def foundFrames (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (slotIndex leading) "found",false⟩ none::
    .variableWrite []::.statementList (body.drop 2) none::continuation

def inner : List Stmt := match (body.drop 3).headD .empty with
  | .ifThenElse _ (.block statements) _=>statements | _=>[]
def call : Expr := .call (.identifier "parseLoc") [(.identifier "found"),(.identifier "params")]
def callFrames (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (slotIndex leading) "str",false⟩ none::
    .expressionStatement::.statementList (inner.drop 2) none::.statementList (body.drop 4) none::continuation

def foundValues (v : Values) : Values := {v with fallback:=.boolean false}
def callValues (v : Values) : Values := {v with fallback:=.boolean false,found:=.string text,str:=.string []}

attribute [local cbv_opaque] LocLocals.heap slotIndex checkedEnvironment readBinding setBinding
attribute [local cbv_eval] checked_local read_id read_params read_baseline read_arguments read_fallback
  read_found read_str set_fallback set_found set_str

theorem to_selected (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (8+fuel) {state base objects leading outer v suffix with
      control:=.statement LocalizationSyntax.locBody}=
      Builtins.run fuel {state base objects leading outer (foundValues v) suffix with
        control:=.expression selected
        continuation:=foundFrames leading base.continuation} := by
  rw [Nat.add_comm 8 fuel]
  cbv

theorem found_to_call (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (28+fuel) {state base objects leading outer (foundValues v) suffix with
      control:=.expressionResult (.value (.string text))
      continuation:=foundFrames leading base.continuation}=
      Builtins.run fuel {state base objects leading outer (callValues v) suffix with
        control:=.expression call
        continuation:=callFrames leading base.continuation} := by
  rw [Nat.add_comm 28 fuel]
  cbv

/-- Both source fallback guards and the actual local initializers execute.
The sole input read is the native locStrings[id] data lookup. -/
theorem source_prefix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (read : Reads (state base objects leading outer (foundValues v) suffix) selected (.string text) 11)
    (fuel : Nat) :
    Builtins.run (47+fuel) {state base objects leading outer v suffix with
      control:=.statement LocalizationSyntax.locBody}=
      Builtins.run fuel {state base objects leading outer (callValues v) suffix with
        control:=.expression call
        continuation:=callFrames leading base.continuation} := by
  rw [show 47+fuel=8+(11+(28+fuel)) by omega,to_selected,read _ (by rfl)]
  exact found_to_call base objects leading outer v suffix fuel

end CookieClicker.JavaScript.LocPrefix

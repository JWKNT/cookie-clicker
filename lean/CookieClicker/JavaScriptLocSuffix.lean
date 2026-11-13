import CookieClicker.JavaScriptLocParseCall
import CookieClicker.JavaScriptStringConstructor

namespace CookieClicker.JavaScript.LocSuffix
open LocLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def values (v : Values) : Values := {LocPrefix.callValues v with str:=.string text}
def constructorExpression : Expr := .member (.identifier "str") (.identifier "constructor") false
def constructorFrames (continuation : List Frame) : List Frame :=
  .binaryLeft .strictEqual (.identifier "Array")::
    .ifTest (.return (some (.identifier "str"))) none::
    .statementList (LocPrefix.inner.drop 3) (some (.string text))::
    .statementList (LocPrefix.body.drop 4) none::continuation
def arrayFrames (constructor : ObjectId) (continuation : List Frame) : List Frame :=
  .binaryRight .strictEqual (.object constructor)::(constructorFrames continuation).drop 1
def blinkConsequent : Stmt := match (LocPrefix.inner.drop 3).headD .empty with
  | .ifThenElse _ statement _=>statement | _=>.empty
def blinkFrames (continuation : List Frame) : List Frame :=
  .logical .and (.unary .not (.identifier "fallback"))::
    .ifTest blinkConsequent none::.statementList [] (some (.string text))::
    .statementList (LocPrefix.body.drop 4) none::continuation

attribute [local cbv_opaque] LocLocals.heap slotIndex checkedEnvironment readBinding setBinding
attribute [local cbv_eval] checked_local read_id read_params read_baseline read_arguments read_fallback
  read_found read_str set_fallback set_found set_str

theorem to_constructor (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (6+fuel) {state base objects leading outer (LocPrefix.callValues v) suffix with
      control:=.expressionResult (.value (.string text))
      continuation:=LocPrefix.callFrames leading base.continuation}=
      Builtins.run fuel {state base objects leading outer (values v) suffix with
        control:=.expression constructorExpression
        continuation:=constructorFrames base.continuation} := by
  rw [Nat.add_comm 6 fuel]
  cbv

theorem to_array (base : Machine) (constructor : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.expressionResult (.value (.object constructor))
      continuation:=constructorFrames base.continuation}=
      Builtins.run fuel {base with
        control:=.expression (.identifier "Array")
        continuation:=arrayFrames constructor base.continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem objects_differ (heap : Heap) (constructor array : ObjectId) (different : constructor≠array) :
    binaryWithHeap heap .strictEqual (.object constructor) (.object array)=.ok (.boolean false) := by
  simp [binaryWithHeap,binary,strictEqual,different,Except.pure,pure]

theorem array_to_blink (base : Machine) (constructor array : ObjectId) (different : constructor≠array)
    (fuel : Nat) :
    Builtins.run (5+fuel) {base with
      control:=.expressionResult (.value (.object array))
      continuation:=arrayFrames constructor base.continuation}=
      Builtins.run fuel {base with
        control:=.expression (.identifier "locBlink")
        continuation:=blinkFrames base.continuation} := by
  rw [show 5+fuel=1+(4+fuel) by omega,Nat.add_comm 1 (4+fuel)]
  change Builtins.run (4+fuel) {checked {base with continuation:=(constructorFrames base.continuation).drop 1}
    (binaryWithHeap base.heap .strictEqual (.object constructor) (.object array))
    (result {base with continuation:=(constructorFrames base.continuation).drop 1})
      with elapsed:=base.elapsed}=_
  rw [objects_differ base.heap constructor array different,Nat.add_comm 4 fuel]
  cbv

theorem blink_returns (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (15+fuel) {state base objects leading outer (values v) suffix with
      control:=.expressionResult (.value (.boolean false))
      continuation:=blinkFrames base.continuation}=
      Builtins.run fuel {state base objects leading outer (values v) suffix with
        control:=.completion (.return (.string text))} := by
  rw [Nat.add_comm 15 fuel]
  cbv

def afterObjects (base : Machine) (objects : Array JSObject) : Array JSObject :=
  objects.push (StringConstructor.wrapper base text)

theorem local_str (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (state base objects leading outer (values v) suffix) (.identifier "str") (.string text) 3 := by
  apply local_identifier _ "str" (.string text) (bindings (values v)) (some outer)
  · exact checked_local objects leading outer _ suffix
  · simp [bindings]
  · exact read_str objects leading outer _ suffix

/-- The actual String wrapper, Array identity test, false locBlink read and
source return execute. The wrapper remains allocated in the final heap. -/
theorem source_suffix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (prototype constructor array : ObjectId) (different : constructor≠array)
    (installed : base.stringPrototype=some prototype)
    (found : lookupProperty (state base objects leading outer (values v) suffix).heap
      prototype (JSString.ofString "constructor")=.ok (some (.data (.object constructor) true false true)))
    (arrayRead : Reads (state base (afterObjects base objects) leading outer (values v) suffix)
      (.identifier "Array") (.object array) 3)
    (blinkRead : Reads (state base (afterObjects base objects) leading outer (values v) suffix)
      (.identifier "locBlink") (.boolean false) 3) (fuel : Nat) :
    Builtins.run (40+fuel) {state base objects leading outer (LocPrefix.callValues v) suffix with
      control:=.expressionResult (.value (.string text))
      continuation:=LocPrefix.callFrames leading base.continuation}=
      Builtins.run fuel {state base (afterObjects base objects) leading outer (values v) suffix with
        control:=.completion (.return (.string text))} := by
  rw [show 40+fuel=6+(7+(1+(3+(5+(3+(15+fuel)))))) by omega,to_constructor]
  let before:=state base objects leading outer (values v) suffix
  let after:=state base (afterObjects base objects) leading outer (values v) suffix
  have member:=StringConstructor.expression {before with continuation:=constructorFrames base.continuation}
    text prototype constructor installed found (local_str base objects leading outer v suffix) (by rfl)
    (1+(3+(5+(3+(15+fuel)))))
  refine member.trans ?_
  change Builtins.run (1+(3+(5+(3+(15+fuel))))) {after with
    control:=.expressionResult (.value (.object constructor))
    continuation:=constructorFrames base.continuation}=_
  refine (to_array after constructor (3+(5+(3+(15+fuel))))).trans ?_
  refine (arrayRead _ (by rfl) (5+(3+(15+fuel)))).trans ?_
  refine (array_to_blink after constructor array different (3+(15+fuel))).trans ?_
  refine (blinkRead _ (by rfl) (15+fuel)).trans ?_
  exact blink_returns base (afterObjects base objects) leading outer v suffix fuel

end CookieClicker.JavaScript.LocSuffix

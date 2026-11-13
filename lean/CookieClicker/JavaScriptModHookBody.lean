import CookieClicker.JavaScriptModHookLocals
import CookieClicker.JavaScriptReadCombinators
import CookieClicker.JavaScriptDescriptorRead

/-! The retained runModHookOnValue body with an empty native hook array. -/
namespace CookieClicker.JavaScript.ModHookBody
open ModHookLocals SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def test : Expr := .binary .less (.identifier "i")
  (.member (.member (.member (.identifier "Game") (.identifier "modHooks") false)
    (.identifier "hook") true) (.identifier "length") false)
def update : Expr := .update .increment (.identifier "i") false
def loopBody : Stmt := .block [.expression (.assignment .assign (.identifier "val")
  (.call (.member (.member (.member (.identifier "Game") (.identifier "modHooks") false)
    (.identifier "hook") true) (.identifier "i") true) [(.identifier "val")]))]

theorem source_body : GainHelpersSyntax.runModHookOnValueBody=.block [
    .forLoop (some (.variables [("i",some (.literal (.number 0)))]))
      (some test) (some update) loopBody,.return (some (.identifier "val"))] := rfl

theorem local_hook (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer v suffix) (.identifier "hook") v.hook 3 := by
  apply local_identifier _ "hook" v.hook (bindings v) (some outer)
  · exact checked_local objects leading outer v suffix
  · simp [bindings]
  · exact read_hook objects leading outer v suffix

theorem local_val (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer v suffix) (.identifier "val") v.val 3 := by
  apply local_identifier _ "val" v.val (bindings v) (some outer)
  · exact checked_local objects leading outer v suffix
  · simp [bindings]
  · exact read_val objects leading outer v suffix

theorem local_i (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer v suffix) (.identifier "i") v.i 3 := by
  apply local_identifier _ "i" v.i (bindings v) (some outer)
  · exact checked_local objects leading outer v suffix
  · exact has_i v
  · exact read_i objects leading outer v suffix

structure EmptyHook (base : Machine) (name : JSString) where
  game : ObjectId
  table : ObjectId
  hooks : ObjectId
  tableEdge : DataEdge base game (JSString.ofString "modHooks") (.object table)
  selectedEdge : DataEdge base table name (.object hooks)
  array : JSObject
  present : checkedObject base.heap hooks=.ok array
  kind : array.kind=.array
  length : lookupProperty base.heap hooks (JSString.ofString "length")=
    .ok (some (.data (.number 0) true false false))

theorem array_length (base : Machine) (name : JSString) (world : EmptyHook base name)
    (game : Reads base (.identifier "Game") (.object world.game) 3)
    (parameter : Reads base (.identifier "hook") (.string name) 3) :
    Reads base (.member (.member (.member (.identifier "Game") (.identifier "modHooks") false)
      (.identifier "hook") true) (.identifier "length") false) (.number 0) 19 := by
  apply dot_descriptor base _ world.hooks "length" (.number 0) world.array true false false 15
  · exact world.selectedEdge.key _ _ (.string name) 7 3
      (world.tableEdge.dot _ 3 game) parameter rfl rfl
  · exact world.present
  · exact Or.inr world.kind
  · exact world.length

theorem false_test (base : Machine) (name : JSString) (world : EmptyHook base name)
    (game : Reads base (.identifier "Game") (.object world.game) 3)
    (parameter : Reads base (.identifier "hook") (.string name) 3)
    (index : Reads base (.identifier "i") (.number 0) 3) :
    Reads base test (.boolean false) 25 := by
  exact binary_value base .less _ _ (.number 0) (.number 0) (.boolean false) 3 19
    index (array_length base name world game parameter) rfl rfl (by decide) (by rfl)

def loopFrames (base : Machine) : List Frame :=
  .forTest (some test) (some update) loopBody [] none::
    .statementList [.return (some (.identifier "val"))] none::base.continuation

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding
attribute [local cbv_eval] checked_local set_i has_i

theorem initialize_index (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (8+fuel) (start base objects leading outer v suffix)=
      Builtins.run fuel {start base objects leading outer {v with i:=.number 0} suffix with
        control:=.expression test,continuation:=loopFrames base} := by
  rw [Nat.add_comm 8 fuel]
  cbv

theorem return_after_guard (base : Machine) (value : Value)
    (localVal : Reads base (.identifier "val") value 3) (fuel : Nat) :
    Builtins.run (8+fuel) {base with
      control:=.expressionResult (.value (.boolean false)),continuation:=loopFrames base}=
      Builtins.run fuel {base with control:=.completion (.return value)} := by
  rw [show 8+fuel=2+(5+(1+fuel)) by omega,Nat.add_comm 2 (5+(1+fuel))]
  change Builtins.run (3+2+(1+fuel)) {base with
    control:=.statement (.return (some (.identifier "val")))
    continuation:=.statementList [] none::base.continuation}=_
  rw [return_read {base with continuation:=.statementList [] none::base.continuation}
    (.identifier "val") value 3 localVal,Nat.add_comm 1 fuel]
  rfl

theorem native_body (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (name : JSString)
    (parameter : v.hook=.string name)
    (world : EmptyHook (start base objects leading outer {v with i:=.number 0} suffix) name)
    (game : Reads (start base objects leading outer {v with i:=.number 0} suffix)
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (41+fuel) (start base objects leading outer v suffix)=
      Builtins.run fuel {start base objects leading outer {v with i:=.number 0} suffix with
        control:=.completion (.return v.val)} := by
  rw [show 41+fuel=8+(25+(8+fuel)) by omega,initialize_index]
  rw [false_test _ name world game
    (by simpa only [parameter] using local_hook base objects leading outer {v with i:=.number 0} suffix)
    (local_i base objects leading outer {v with i:=.number 0} suffix) _ (by rfl)]
  exact return_after_guard (start base objects leading outer {v with i:=.number 0} suffix)
    v.val (local_val base objects leading outer {v with i:=.number 0} suffix) fuel

end CookieClicker.JavaScript.ModHookBody

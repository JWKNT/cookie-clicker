import CookieClicker.JavaScriptLocPrefix
import CookieClicker.JavaScriptParseLocBody
import CookieClicker.JavaScriptGlobalCall

namespace CookieClicker.JavaScript.LocParseCall
open LocLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def caller (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  state base objects leading outer (LocPrefix.callValues v) suffix with
  continuation:=LocPrefix.callFrames leading base.continuation }

theorem found_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (caller base objects leading outer v suffix) (.identifier "found") (.string text) 3 := by
  apply local_identifier _ "found" (.string text) (bindings (LocPrefix.callValues v)) (some outer)
  · exact checked_local objects leading outer _ suffix
  · simp [bindings]
  · exact read_found objects leading outer _ suffix

theorem params_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (caller base objects leading outer v suffix) (.identifier "params") .undefined 3 := by
  apply local_identifier _ "params" .undefined (bindings (LocPrefix.callValues v)) (some outer)
  · exact checked_local objects leading outer _ suffix
  · simp [bindings]
  · exact read_params objects leading outer _ suffix

theorem source_call (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (scope function : Nat)
    (source : Option JSString) (functionObject : JSObject)
    (callee : GlobalCall.Callee (caller base objects leading outer v suffix) "parseLoc" function)
    (present : checkedObject (caller base objects leading outer v suffix).heap function=.ok functionObject)
    (kind : functionObject.kind=.function (ParseLocCall.closure scope source)) (fuel : Nat) :
    Builtins.run (109+fuel) {caller base objects leading outer v suffix with control:=.expression LocPrefix.call}=
      Builtins.run fuel (ParseLocCall.returned (caller base objects leading outer v suffix) scope function) := by
  rw [show 109+fuel=13+(96+fuel) by omega]
  refine (GlobalCall.source_two (caller base objects leading outer v suffix) "parseLoc" function callee
    (.identifier "found") (.identifier "params") (.string text) .undefined 3 3
    (found_read base objects leading outer v suffix) (params_read base objects leading outer v suffix) (96+fuel)).trans ?_
  exact ParseLocBody.native_call _ scope function source functionObject present kind fuel

def afterObjects (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (function : ObjectId) : Array JSObject :=
  let current:=caller base objects leading outer v suffix
  (objects.push (ParseLocCall.argumentObject current function)).push (ParseLocCall.emptyArray current)

def afterSuffix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (scope : EnvId) : Array LexicalEnvironment :=
  suffix.push ⟨.declarative (ParseLocCall.finalLocals (caller base objects leading outer v suffix)),some scope⟩

theorem returned_layout (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (scope function : Nat) :
    ParseLocCall.returned (caller base objects leading outer v suffix) scope function=
      {state base (afterObjects base objects leading outer v suffix function) leading outer
        (LocPrefix.callValues v) (afterSuffix base objects leading outer v suffix scope) with
        control:=.expressionResult (.value (.string text))
        continuation:=LocPrefix.callFrames leading base.continuation} := by
  simp only [ParseLocCall.returned,caller,state,heap,afterObjects,afterSuffix,Array.append_push]
  rfl

end CookieClicker.JavaScript.LocParseCall

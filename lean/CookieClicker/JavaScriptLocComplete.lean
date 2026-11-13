import CookieClicker.JavaScriptLocSuffix
import CookieClicker.JavaScriptGlobalData

namespace CookieClicker.JavaScript.LocComplete
open LocLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

structure Input (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) where
  strings : ObjectId
  stringsGlobal : GlobalData.Input (state base objects leading outer (LocPrefix.foundValues v) suffix)
    "locStrings" (.object strings)
  translation : TieredRead.DataEdge (state base objects leading outer (LocPrefix.foundValues v) suffix)
    strings text (.string text)
  scope : EnvId
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  callee : GlobalCall.Callee (LocParseCall.caller base objects leading outer v suffix) "parseLoc" function
  present : checkedObject (LocParseCall.caller base objects leading outer v suffix).heap function=.ok functionObject
  kind : functionObject.kind=.function (ParseLocCall.closure scope source)
  prototype : ObjectId
  constructor : ObjectId
  array : ObjectId
  different : constructor≠array
  installed : base.stringPrototype=some prototype
  constructorProperty : lookupProperty
    (state base (LocParseCall.afterObjects base objects leading outer v suffix function) leading outer
      (LocSuffix.values v) (LocParseCall.afterSuffix base objects leading outer v suffix scope)).heap
      prototype (JSString.ofString "constructor")=.ok (some (.data (.object constructor) true false true))
  arrayGlobal : GlobalData.Input
    (state base (LocSuffix.afterObjects base (LocParseCall.afterObjects base objects leading outer v suffix function))
      leading outer (LocSuffix.values v) (LocParseCall.afterSuffix base objects leading outer v suffix scope))
    "Array" (.object array)
  blinkGlobal : GlobalData.Input
    (state base (LocSuffix.afterObjects base (LocParseCall.afterObjects base objects leading outer v suffix function))
      leading outer (LocSuffix.values v) (LocParseCall.afterSuffix base objects leading outer v suffix scope))
    "locBlink" (.boolean false)

def Input.after {base : Machine} {objects : Array JSObject} {leading : Array LexicalEnvironment}
    {outer : EnvId} {v : Values} {suffix : Array LexicalEnvironment}
    (input : Input base objects leading outer v suffix) : Machine := {
  state base (LocSuffix.afterObjects base (LocParseCall.afterObjects base objects leading outer v suffix input.function))
    leading outer (LocSuffix.values v) (LocParseCall.afterSuffix base objects leading outer v suffix input.scope) with
  control:=.completion (.return (.string text)) }

theorem id_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (state base objects leading outer v suffix) (.identifier "id") (.string text) 3 := by
  apply local_identifier _ "id" (.string text) (bindings v) (some outer)
  · exact checked_local objects leading outer v suffix
  · simp [bindings]
  · exact read_id objects leading outer v suffix

theorem Input.translation_read {base : Machine} {objects : Array JSObject} {leading : Array LexicalEnvironment}
    {outer : EnvId} {v : Values} {suffix : Array LexicalEnvironment}
    (input : Input base objects leading outer v suffix) :
    Reads (state base objects leading outer (LocPrefix.foundValues v) suffix) LocPrefix.selected (.string text) 11 :=
  computed_string _ (.identifier "locStrings") (.identifier "id") input.strings text (.string text)
    input.translation.object 3 3 input.stringsGlobal.read (id_read base objects leading outer _ suffix)
    input.translation.present input.translation.kind input.translation.property

/-- The complete intact loc body on the initialized English entry. Both source
functions execute, with native arguments, local writes, arrays, boxing, guards
and completion propagation retained. Inputs describe actual data and closures. -/
theorem source_body (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (input : Input base objects leading outer v suffix) (fuel : Nat) :
    Builtins.run (196+fuel) {state base objects leading outer v suffix with
      control:=.statement LocalizationSyntax.locBody}=
      Builtins.run fuel input.after := by
  rw [show 196+fuel=47+(109+(40+fuel)) by omega,
    LocPrefix.source_prefix base objects leading outer v suffix input.translation_read]
  have called:=LocParseCall.source_call base objects leading outer v suffix input.scope input.function
    input.source input.functionObject input.callee input.present input.kind (40+fuel)
  refine called.trans ?_
  rw [LocParseCall.returned_layout]
  exact LocSuffix.source_suffix base (LocParseCall.afterObjects base objects leading outer v suffix input.function)
    leading outer v (LocParseCall.afterSuffix base objects leading outer v suffix input.scope)
    input.prototype input.constructor input.array input.different input.installed input.constructorProperty
    input.arrayGlobal.read input.blinkGlobal.read fuel

end CookieClicker.JavaScript.LocComplete

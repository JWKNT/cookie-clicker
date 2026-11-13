import CookieClicker.JavaScriptGlobalCall

namespace CookieClicker.JavaScript.GlobalData
structure Input (base : Machine) (name : String) (value : Value) where
  target : EnvId
  depth : Nat
  window : ObjectId
  object : JSObject
  writable : Bool
  enumerable : Bool
  configurable : Bool
  chain : HasEnvironment.DeclarativePath base.heap.environments name base.context.lexicalEnvironment target depth
  room : depth≤base.heap.environments.size
  globalRead : checkedEnvironment base.heap target=.ok ⟨.object window false,none⟩
  objectRead : checkedObject base.heap window=.ok object
  kind : object.kind=.host "Window" 0
  property : lookupProperty base.heap window (JSString.ofString name)=
    .ok (some (.data value writable enumerable configurable))
  exclusions : base.objectEnvironmentExclusions=[]

theorem Input.read {base : Machine} {name : String} {value : Value} (input : Input base name value) :
    SourceRead.Reads base (.identifier name) value 3 :=
  SourceRead.global_identifier base name input.target input.depth input.window input.object value
    input.writable input.enumerable input.configurable input.chain input.room input.globalRead
    input.objectRead input.kind input.property input.exclusions
end CookieClicker.JavaScript.GlobalData

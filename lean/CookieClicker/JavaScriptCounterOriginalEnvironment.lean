import CookieClicker.JavaScriptCounterObjects

/-! Counter parameters and Game resolve through the retained closure path.
Property writes do not replace any lexical environment. -/
namespace CookieClicker.JavaScript.CounterOriginalEnvironment
open HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def localIndex {window : ObjectId} (scopes : Scopes window) : EnvId := scopes.environments.size

def locals (amount : UInt64) (arguments : ObjectId) : List Binding :=
  [{name:="howmuch",value:=.number amount},{name:="arguments",value:=.object arguments}]

def environments {window : ObjectId} (scopes : Scopes window) (amount : UInt64) (arguments : ObjectId) :=
  scopes.environments.push ⟨.declarative (locals amount arguments),some scopes.closureScope⟩

def ambient {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : Scopes frame.window) (amount : UInt64) (arguments : ObjectId) : Machine := {
  base with
  heap := CounterObjects.heap frame (environments scopes amount arguments)
  context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem checked_local {window : ObjectId} (objects : Array JSObject) (scopes : Scopes window)
    (amount : UInt64) (arguments : ObjectId) :
    checkedEnvironment ⟨objects,environments scopes amount arguments⟩ (localIndex scopes) =
      .ok ⟨.declarative (locals amount arguments),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,environments,localIndex,Heap.environment?]

theorem checked_global {window : ObjectId} (objects : Array JSObject) (scopes : Scopes window)
    (amount : UInt64) (arguments : ObjectId) :
    checkedEnvironment ⟨objects,environments scopes amount arguments⟩ scopes.globalScope =
      .ok ⟨.object window false,none⟩ := by
  have read := append_old_read scopes.environments
    ⟨.declarative (locals amount arguments),some scopes.closureScope⟩
    ⟨.object window false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,environments,Heap.environment?,read]

theorem game_path {window : ObjectId} (scopes : Scopes window) (amount : UInt64) (arguments : ObjectId) :
    DeclarativePath (environments scopes amount arguments) "Game"
      (localIndex scopes) scopes.globalScope (scopes.depth+1) := by
  apply DeclarativePath.next (localIndex scopes) scopes.closureScope scopes.globalScope scopes.depth
    (locals amount arguments)
  · simp [environments,localIndex]
  · simp [locals]
  · exact append_path scopes.environments _ "Game" _ _ _ scopes.chain

theorem read_amount {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : Scopes frame.window) (amount : UInt64) (arguments : ObjectId) :
    SourceRead.Reads (ambient base frame scopes amount arguments) (.identifier "howmuch") (.number amount) 3 := by
  apply SourceRead.local_identifier _ "howmuch" (.number amount) (locals amount arguments) (some scopes.closureScope)
  · exact checked_local frame.objects scopes amount arguments
  · simp [locals]
  · simp [ambient,CounterObjects.heap,environments,readBinding,checkedEnvironment,Heap.environment?,
      localIndex,locals,Except.bind,Except.pure,bind,pure]

theorem read_game {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : Scopes frame.window) (amount : UInt64) (arguments : ObjectId) :
    SourceRead.Reads (ambient base frame scopes amount arguments) (.identifier "Game") (.object frame.game) 3 := by
  intro continuation consumer fuel
  let start := {ambient base frame scopes amount arguments with control:=.expression (.identifier "Game"),continuation}
  have chain : DeclarativePath start.heap.environments "Game" start.context.lexicalEnvironment
      scopes.globalScope (scopes.depth+1) := game_path scopes amount arguments
  have room : scopes.depth+1≤start.heap.environments.size := by
    change scopes.depth+1≤(environments scopes amount arguments).size
    simp only [environments,Array.size_push]
    have bound:=scopes.depthBound;omega
  have globalRead : checkedEnvironment start.heap scopes.globalScope=.ok ⟨.object frame.window false,none⟩ :=
    checked_global frame.objects scopes amount arguments
  have objectRead : checkedObject start.heap frame.window=.ok frame.windowObject :=
    CounterObjects.checked_window frame _
  have property : lookupProperty start.heap frame.window (JSString.ofString "Game")=
      .ok (some (.data (.object frame.game) true true false)) := CounterObjects.game_binding frame _
  have identified := IdentifierPath.identifier start "Game" scopes.globalScope (scopes.depth+1)
    frame.window _ chain room globalRead property rfl
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Environment.identifier start "Game")=_
  rw [identified]
  apply SourceRead.reference_value _ _ _ consumer
  rcases frame.windowKind with kind|kind <;>
    simp [getReference,globalRead,JavaScript.checked,readProperty,toObject,readObjectProperty,
      objectRead,kind,property,result]

end CookieClicker.JavaScript.CounterOriginalEnvironment

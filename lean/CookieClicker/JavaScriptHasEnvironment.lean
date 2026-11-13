import CookieClicker.JavaScriptHasFrame
/-! The native Game.Has body through an arbitrary declarative closure path.
The path does not shadow Game and ends at the actual Window object environment.
The native local environment is appended, with arbitrary other bindings that
do not shadow what, it, or Game. All heap objects and caller state are retained.
Mapping initialized callbacks to these explicit hypotheses remains separate. -/

namespace CookieClicker.JavaScript.HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

inductive DeclarativePath (environments : Array LexicalEnvironment) (name : String) :
    EnvId → EnvId → Nat → Prop where
  | done (id : EnvId) : DeclarativePath environments name id id 0
  | next (id following target depth : Nat) (bindings : List Binding)
      (read : environments[id]? = some ⟨.declarative bindings,some following⟩)
      (absent : bindings.any (fun binding => binding.name == name) = false)
      (rest : DeclarativePath environments name following target depth) :
      DeclarativePath environments name id target (depth+1)

theorem resolve_path (machine : Machine) (name : String) (strict : Bool)
    (start target depth fuel : Nat)
    (path : DeclarativePath machine.heap.environments name start target depth) :
    Environment.resolve (depth+fuel) machine start name strict =
      Environment.resolve fuel machine target name strict := by
  induction path with
  | done id => simp
  | next id following target depth bindings read absent rest ih =>
    have checked : checkedEnvironment machine.heap id =
        .ok ⟨.declarative bindings,some following⟩ := by
      simp [checkedEnvironment,Heap.environment?,read]
    rw [show depth+1+fuel = (depth+fuel)+1 by omega]
    simp only [Environment.resolve,checked,JavaScript.checked,absent,Bool.false_eq_true,↓reduceIte]
    exact ih

structure Locals where
  before : List Binding := []
  between : List Binding := []
  after : List Binding := []
  clean : ∀ b ∈ before ++ between ++ after,
    b.name ≠ "what" ∧ b.name ≠ "it" ∧ b.name ≠ "Game"

def bindings (locals : Locals) (what : JSString) (it : Value) : List Binding :=
  locals.before ++ [{name := "what",value := .string what}] ++ locals.between ++
    [{name := "it",value := it}] ++ locals.after

theorem find_clean (xs : List Binding) (name : String)
    (clean : ∀ b ∈ xs, b.name ≠ name) :
    xs.find? (fun b => b.name == name) = none := by
  apply List.find?_eq_none.mpr
  intro b member
  simpa only [beq_iff_eq] using clean b member

theorem find_what (locals : Locals) (what : JSString) (it : Value) :
    (bindings locals what it).find? (fun b => b.name == "what") =
      some {name := "what",value := .string what} := by
  have before := find_clean locals.before "what" (by
    intro b member; exact (locals.clean b (by simp [member])).1)
  simp [bindings,List.find?_append,before]

theorem find_it (locals : Locals) (what : JSString) (it : Value) :
    (bindings locals what it).find? (fun b => b.name == "it") =
      some {name := "it",value := it} := by
  have before := find_clean locals.before "it" (by
    intro b member; exact (locals.clean b (by simp [member])).2.1)
  have between := find_clean locals.between "it" (by
    intro b member; exact (locals.clean b (by simp [member])).2.1)
  simp [bindings,List.find?_append,before,between]

theorem no_game (locals : Locals) (what : JSString) (it : Value) :
    (bindings locals what it).any (fun b => b.name == "Game") = false := by
  apply List.any_eq_false.mpr
  intro b member
  simp only [bindings,List.mem_append,List.mem_singleton] at member
  rcases member with (((before | chosenWhat) | between) | chosenIt) | after
  · exact by simpa using (locals.clean b (by simp [before])).2.2
  · subst b; simp
  · exact by simpa using (locals.clean b (by simp [between])).2.2
  · subst b; simp
  · exact by simpa using (locals.clean b (by simp [after])).2.2

theorem write_clean (xs : List Binding) (it : Value)
    (clean : ∀ b ∈ xs, b.name ≠ "it") :
    xs.map (fun b => if b.name == "it" then {b with value := it,initialized := true} else b) = xs := by
  calc
    _ = xs.map id := List.map_congr_left (by intro b member; simp [clean b member])
    _ = xs := List.map_id xs

theorem write_it (locals : Locals) (what : JSString) (it next : Value) :
    (bindings locals what it).map
      (fun b => if b.name == "it" then {b with value := next,initialized := true} else b) =
      bindings locals what next := by
  have before := write_clean locals.before next (by
    intro b member; exact (locals.clean b (by simp [member])).2.1)
  have between := write_clean locals.between next (by
    intro b member; exact (locals.clean b (by simp [member])).2.1)
  have after := write_clean locals.after next (by
    intro b member; exact (locals.clean b (by simp [member])).2.1)
  simp only [beq_iff_eq] at before between after
  simp [bindings,before,between,after]

structure Scopes (window : ObjectId) where
  environments : Array LexicalEnvironment
  closureScope : EnvId
  globalScope : EnvId
  depth : Nat
  chain : DeclarativePath environments "Game" closureScope globalScope depth
  globalRead : environments[globalScope]? = some ⟨.object window false,none⟩
  depthBound : depth < environments.size

def localIndex {window : ObjectId} (scopes : Scopes window) : EnvId := scopes.environments.size

def heap {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) : Heap := {
  objects := frame.objects
  environments := scopes.environments.push
    ⟨.declarative (bindings locals what it),some scopes.closureScope⟩ }

theorem append_old_read (environments : Array LexicalEnvironment) (added env : LexicalEnvironment)
    (id : EnvId) (read : environments[id]? = some env) :
    (environments.push added)[id]? = some env := by
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp read
  have distinct : id ≠ environments.size := Nat.ne_of_lt bound
  simp only [Array.getElem?_push,if_neg distinct,read]

theorem append_path (environments : Array LexicalEnvironment) (added : LexicalEnvironment)
    (name : String) (start target depth : Nat)
    (path : DeclarativePath environments name start target depth) :
    DeclarativePath (environments.push added) name start target depth := by
  induction path with
  | done id => exact .done id
  | next id following target depth bindings read absent rest ih =>
    exact .next id following target depth bindings
      (append_old_read environments added _ id read) absent ih

theorem checked_local {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedEnvironment (heap frame scopes locals it) (localIndex scopes) =
      .ok ⟨.declarative (bindings locals what it),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem checked_global {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedEnvironment (heap frame scopes locals it) scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := by
  have read := append_old_read scopes.environments
    ⟨.declarative (bindings locals what it),some scopes.closureScope⟩
    ⟨.object frame.window false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,heap,Heap.environment?,read]

theorem write_local {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it next : Value) :
    replaceEnvironment (heap frame scopes locals it) (localIndex scopes)
      ⟨.declarative (bindings locals what next),some scopes.closureScope⟩ =
      .ok (heap frame scopes locals next) := by
  simp [replaceEnvironment,Heap.writeEnvironment,heap,localIndex,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_push]

theorem window_binding {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    lookupProperty (heap frame scopes locals it) frame.window (JSString.ofString "Game") =
      .ok (some (.data (.object frame.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.windowRead,
    frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

def ambient {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value) : Machine := {
  base with
  heap := heap frame scopes locals it
  context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem identifier_game {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    Environment.identifier (ambient base frame scopes locals it) "Game" =
      {ambient base frame scopes locals it with
        control := .expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  let machine := ambient base frame scopes locals it
  have localRead : checkedEnvironment machine.heap (localIndex scopes) =
      .ok ⟨.declarative (bindings locals what it),some scopes.closureScope⟩ :=
    checked_local frame scopes locals it
  have globalRead : checkedEnvironment machine.heap scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := checked_global frame scopes locals it
  have chain : DeclarativePath machine.heap.environments "Game"
      scopes.closureScope scopes.globalScope scopes.depth :=
    append_path scopes.environments _ "Game" _ _ _ scopes.chain
  have count : scopes.environments.size+1 = scopes.depth+(scopes.environments.size-scopes.depth+1) := by
    have bound := scopes.depthBound; omega
  change Environment.resolve ((heap frame scopes locals it).environments.size+1)
    machine (localIndex scopes) "Game" false = _
  simp only [heap,Array.size_push]
  rw [Environment.resolve,localRead]
  simp only [JavaScript.checked,no_game,Bool.false_eq_true,↓reduceIte]
  rw [count,resolve_path machine "Game" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [JavaScript.checked,machine,ambient,window_binding]
  rfl

theorem has_what (locals : Locals) (what : JSString) (it : Value) :
    (bindings locals what it).any (fun b => b.name == "what") = true := by
  simp [bindings,List.any_append]

theorem has_it (locals : Locals) (what : JSString) (it : Value) :
    (bindings locals what it).any (fun b => b.name == "it") = true := by
  simp [bindings,List.any_append]

theorem identifier_what {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    Environment.identifier (ambient base frame scopes locals it) "what" =
      {ambient base frame scopes locals it with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "what",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes locals it) (has_what locals what it)

theorem identifier_it {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    Environment.identifier (ambient base frame scopes locals it) "it" =
      {ambient base frame scopes locals it with
        control := .expressionResult (.reference ⟨.environment (localIndex scopes) "it",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes locals it) (has_it locals what it)

theorem it_reference {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    identifierReference (ambient base frame scopes locals it) "it" =
      .ok ⟨.environment (localIndex scopes) "it",false⟩ := by
  simp only [identifierReference,ambient,heap,Array.size_push]
  change resolveName (heap frame scopes locals it) false (scopes.environments.size+1+1)
    (localIndex scopes) "it" = _
  rw [resolveName,checked_local]
  simp only [bind,Except.bind,pure,Except.pure,has_it,↓reduceIte]

theorem read_what {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    readBinding (heap frame scopes locals it) (localIndex scopes) "what" = .ok (.string what) := by
  simp [readBinding,checked_local,find_what,bind,Except.bind,pure,Except.pure]

theorem read_it {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    readBinding (heap frame scopes locals it) (localIndex scopes) "it" = .ok it := by
  simp [readBinding,checked_local,find_it,bind,Except.bind,pure,Except.pure]

theorem set_it {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it next : Value) :
    setBinding (heap frame scopes locals it) (localIndex scopes) "it" next false =
      .ok (heap frame scopes locals next) := by
  have written := write_it locals what it next
  simp only [beq_iff_eq] at written
  simp [setBinding,checked_local,find_it,written,write_local,bind,Except.bind]


theorem game_table {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    lookupProperty (heap frame scopes locals it) frame.game (JSString.ofString "Upgrades") =
      .ok (some (.data (.object frame.table) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.gameRead,
    frame.gameKnown,frame.gameTable,Except.bind,Except.pure,bind,pure]

theorem normal_mode {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    lookupProperty (heap frame scopes locals it) frame.game (JSString.ofString "ascensionMode") =
      .ok (some (.data (.number 0) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.gameRead,
    frame.gameKnown,frame.normalMode,Except.bind,Except.pure,bind,pure]

theorem selected_upgrade {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    lookupProperty (heap frame scopes locals it) frame.table what =
      .ok (some (.data (.object frame.upgrade) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.tableRead,
    frame.tableKnown,frame.selectedUpgrade,Except.bind,Except.pure,bind,pure]

theorem bought_value {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    lookupProperty (heap frame scopes locals it) frame.upgrade (JSString.ofString "bought") =
      .ok (some (.data bought true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,frame.upgradeRead,
    frame.upgradeKnown,frame.boughtValue,Except.bind,Except.pure,bind,pure]

theorem checked_game {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedObject (heap frame scopes locals it) frame.game = .ok frame.gameObject := by
  simp [checkedObject,heap,Heap.object?,frame.gameRead]

theorem game_kind {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought) :
    frame.gameObject.kind = .ordinary := frame.gameKind

theorem checked_window {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedObject (heap frame scopes locals it) frame.window = .ok frame.windowObject := by
  simp [checkedObject,heap,Heap.object?,frame.windowRead]

theorem window_kind {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought) :
    frame.windowObject.kind = .host "Window" 0 := frame.windowKind

theorem checked_table {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedObject (heap frame scopes locals it) frame.table = .ok frame.tableObject := by
  simp [checkedObject,heap,Heap.object?,frame.tableRead]

theorem table_kind {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought) :
    frame.tableObject.kind = .ordinary := frame.tableKind

theorem checked_upgrade {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought)
    (scopes : Scopes frame.window) (locals : Locals) (it : Value) :
    checkedObject (heap frame scopes locals it) frame.upgrade = .ok frame.upgradeObject := by
  simp [checkedObject,heap,Heap.object?,frame.upgradeRead]

theorem upgrade_kind {what : JSString} {bought : Value} (frame : HasFrame.Frame what bought) :
    frame.upgradeObject.kind = .ordinary := frame.upgradeKind


theorem identifier_game_explicit {what : JSString} {bought : Value}
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "Game" =
      {({
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  exact identifier_game {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} frame scopes locals it

theorem identifier_what_explicit {what : JSString} {bought : Value}
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "what" =
      {({
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "what",false⟩)} := by
  exact identifier_what {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} frame scopes locals it

theorem identifier_it_explicit {what : JSString} {bought : Value}
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    Environment.identifier {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "it" =
      {({
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} : Machine) with control := .expressionResult (.reference ⟨.environment (localIndex scopes) "it",false⟩)} := by
  exact identifier_it {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} frame scopes locals it

theorem it_reference_explicit {what : JSString} {bought : Value}
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (it : Value)
    (control : Control)
    (continuation : List Frame)
    (objectPrototype : Option ObjectId)
    (functionPrototype : Option ObjectId)
    (arrayPrototype : Option ObjectId)
    (stringPrototype : Option ObjectId)
    (numberPrototype : Option ObjectId)
    (booleanPrototype : Option ObjectId)
    (regexpPrototype : Option ObjectId)
    (datePrototype : Option ObjectId)
    (throwTypeErrorIntrinsic : Option ObjectId)
    (events : List ScheduledEvent)
    (nextEventId : EventId)
    (elapsed : Rat)
    (epochMilliseconds : Int)
    (freeDrawCount : Nat) :
    identifierReference {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} "it" =
      .ok ⟨.environment (localIndex scopes) "it",false⟩ := by
  exact it_reference {
      heap := heap frame scopes locals it
      context := ⟨localIndex scopes,localIndex scopes,.object frame.game,false⟩
      globalObject := frame.window
      objectEnvironmentExclusions := []
      control := control
      continuation := continuation
      objectPrototype := objectPrototype
      functionPrototype := functionPrototype
      arrayPrototype := arrayPrototype
      stringPrototype := stringPrototype
      numberPrototype := numberPrototype
      booleanPrototype := booleanPrototype
      regexpPrototype := regexpPrototype
      datePrototype := datePrototype
      throwTypeErrorIntrinsic := throwTypeErrorIntrinsic
      events := events
      nextEventId := nextEventId
      elapsed := elapsed
      epochMilliseconds := epochMilliseconds
      freeDrawCount := freeDrawCount} frame scopes locals it

attribute [local cbv_opaque] heap lookupProperty checkedObject checkedEnvironment
attribute [local cbv_opaque] replaceEnvironment readBinding setBinding Environment.identifier identifierReference
attribute [local cbv_opaque] localIndex bindings Number.equal JSString.ofString
attribute [local cbv_eval] window_binding game_table normal_mode selected_upgrade bought_value
attribute [local cbv_eval] checked_local checked_global read_what read_it set_it
attribute [local cbv_eval] identifier_game_explicit identifier_what_explicit identifier_it_explicit it_reference_explicit
attribute [local cbv_eval] checked_game checked_window checked_table checked_upgrade
attribute [local cbv_eval] game_kind window_kind table_kind upgrade_kind HasFrame.zero_not_one

def state {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) : Machine :=
  {ambient base frame scopes locals .undefined with control := .statement LumpSyntax.HasBody}

set_option linter.unusedSimpArgs false in
theorem native_has_body_prefix {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) (fuel : Nat) :
    let before := state base frame scopes locals
    Builtins.run (59+fuel) before = Builtins.run fuel {before with
      heap := heap frame scopes locals (.object frame.upgrade)
      control := .completion (.return bought)} := by
  rw [Nat.add_comm 59 fuel]
  cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv
  try simp only [it_reference_explicit, identifier_game_explicit, identifier_what_explicit, identifier_it_explicit, checked_local, checked_global, read_what, read_it, set_it, window_binding, game_table, normal_mode, selected_upgrade, bought_value, checked_game, checked_window, checked_table, checked_upgrade, game_kind, window_kind, table_kind, upgrade_kind, HasFrame.zero_not_one]
  try cbv

set_option linter.unusedSimpArgs false in
theorem native_has_body {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : Scopes frame.window) (locals : Locals) :
    let before := state base frame scopes locals
    Builtins.run 59 before = {before with
      heap := heap frame scopes locals (.object frame.upgrade)
      control := .completion (.return bought)} := by
  simpa only [Nat.add_zero,Builtins.run] using
    native_has_body_prefix base frame scopes locals 0

end CookieClicker.JavaScript.HasEnvironment

import CookieClicker.JavaScriptCounterOriginalCall

namespace CookieClicker.JavaScript.CounterOriginalPreservation
open CounterOriginalCall CounterOriginalInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private theorem append_read {α : Type} (items : Array α) (id : Nat) (value extra : α)
    (present : items[id]?=some value) : (items.push extra)[id]?=some value := by
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp present
  simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using present

theorem updated_other_object {cookies earned : UInt64} (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (amount : UInt64) (id : ObjectId)
    (distinct : id≠frame.game) : (updatedFrame op frame amount).objects[id]?=frame.objects[id]? := by
  cases op with
  | earn =>
    exact (CounterObjects.writeEarned_other_object
      (CounterObjects.writeCookies frame (Number.add cookies amount)) (Number.add earned amount) id distinct).trans
      (CounterObjects.writeCookies_other_object frame (Number.add cookies amount) id distinct)
  | spend => exact CounterObjects.writeCookies_other_object _ _ _ distinct

theorem returned_objects {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).heap.objects=
      (updatedFrame op (CounterObjects.append frame (argumentObject (caller base frame scopes) amount callee)) amount).objects := by
  cases op <;> rfl

theorem returned_environments {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).heap.environments=
      CounterOriginalEnvironment.environments scopes amount frame.objects.size := by
  cases op <;> rfl

theorem returned_old_object {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) (id : ObjectId) (object : JSObject)
    (distinct : id≠frame.game) (present : frame.objects[id]?=some object) :
    (returned base op frame scopes amount callee).heap.objects[id]?=some object := by
  rw [returned_objects,updated_other_object op (CounterObjects.append frame (argumentObject (caller base frame scopes) amount callee)) amount _ distinct]
  exact append_read _ _ _ _ present

theorem returned_old_environment {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) (id : EnvId) (env : LexicalEnvironment)
    (present : scopes.environments[id]?=some env) :
    (returned base op frame scopes amount callee).heap.environments[id]?=some env := by
  rw [returned_environments]
  exact append_read _ _ _ _ present

theorem returned_cookies {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    lookupProperty (returned base op frame scopes amount callee).heap frame.game (JSString.ofString "cookies")=
      .ok (some (.data (.number (cookiesAfter op cookies amount)) true true true)) := by
  cases op <;> exact CounterObjects.cookies_lookup _ _

theorem returned_earned {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    lookupProperty (returned base op frame scopes amount callee).heap frame.game (JSString.ofString "cookiesEarned")=
      .ok (some (.data (.number (earnedAfter op earned amount)) true true true)) := by
  cases op <;> exact CounterObjects.earned_lookup _ _

theorem returned_game_object {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).heap.objects[frame.game]?=
      some (updatedFrame op frame amount).gameObject := by
  cases op with
  | earn => exact (updatedFrame .earn (CounterObjects.append frame (argumentObject (caller base frame scopes) amount callee)) amount).gameRead
  | spend => exact (updatedFrame .spend (CounterObjects.append frame (argumentObject (caller base frame scopes) amount callee)) amount).gameRead

theorem returned_other_game_field {cookies earned : UInt64} (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (amount : UInt64) (name : JSString)
    (cookiesDistinct : JSString.ofString "cookies"≠name)
    (earnedDistinct : JSString.ofString "cookiesEarned"≠name) :
    ownProperty (updatedFrame op frame amount).gameObject name=ownProperty frame.gameObject name := by
  cases op with
  | earn =>
    exact (CounterObjects.writeEarned_other_field _ _ _ earnedDistinct).trans
      (CounterObjects.writeCookies_other_field _ _ _ cookiesDistinct)
  | spend => exact CounterObjects.writeCookies_other_field _ _ _ cookiesDistinct

theorem returned_arguments {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).heap.objects[frame.objects.size]?=
      some (argumentObject (caller base frame scopes) amount callee) := by
  have distinct : frame.objects.size≠frame.game := by
    have bounded:=(Array.getElem?_eq_some_iff.mp frame.gameRead).1
    omega
  rw [returned_objects,updated_other_object op (CounterObjects.append frame (argumentObject (caller base frame scopes) amount callee)) amount _ distinct]
  simp [CounterObjects.append]

theorem returned_parameter {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    readBinding (returned base op frame scopes amount callee).heap scopes.environments.size "howmuch"=.ok (.number amount) := by
  simp [readBinding,checkedEnvironment,Heap.environment?,returned_environments,
    CounterOriginalEnvironment.environments,CounterOriginalEnvironment.locals,Except.bind,Except.pure,bind,pure]

theorem returned_mapped_argument {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    readProperty (returned base op frame scopes amount callee) (.object frame.objects.size) (JSString.ofString "0")=
      result (returned base op frame scopes amount callee) (.number amount) := by
  have objectRead : checkedObject (returned base op frame scopes amount callee).heap frame.objects.size=
      .ok (argumentObject (caller base frame scopes) amount callee) := by
    simp [checkedObject,Heap.object?,returned_arguments]
  simp [readProperty,toObject,checked,readObjectProperty,objectRead,argumentObject,
    localIndex,caller,returned_parameter]

theorem returned_elapsed {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).elapsed=base.elapsed := by
  cases op <;> rfl

theorem returned_free_draw_count {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).freeDrawCount=base.freeDrawCount := by
  cases op <;> rfl

theorem returned_context {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).context=base.context := by
  cases op <;> rfl

theorem returned_continuation {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).continuation=base.continuation := by
  cases op <;> rfl

theorem returned_events {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).events=base.events := by
  cases op <;> rfl

theorem returned_epoch {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    (returned base op frame scopes amount callee).epochMilliseconds=base.epochMilliseconds := by
  cases op <;> rfl

end CookieClicker.JavaScript.CounterOriginalPreservation

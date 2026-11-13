import CookieClicker.JavaScriptCounterFrame

/-! Actual counter bodies with arbitrary heap placement and property order.
The two writable data properties may occur in either order, with arbitrary
other fields between them. All unrelated objects, environments, metadata,
and machine fields are retained. Entry still uses explicit declarative
Game/howmuch bindings; correspondence to the initialized call environment
and its invariants is a separate obligation.
-/
namespace CookieClicker.JavaScript.CounterLens
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
private def cookieName := JSString.ofString "cookies"
private def earnedName := JSString.ofString "cookiesEarned"
structure Fields where
  before : List OwnProperty
  between : List OwnProperty
  after : List OwnProperty
  clean : ∀ p ∈ before ++ between ++ after, p.name ≠ cookieName ∧ p.name ≠ earnedName
  cookiesFirst : Bool := true
  prototype : Option ObjectId := none
  extensible : Bool := true
  propertiesComplete : Bool := true

def object (frame : Fields) (cookies earned : UInt64) : JSObject := {
  prototype := frame.prototype
  extensible := frame.extensible
  propertiesComplete := frame.propertiesComplete
  properties := frame.before ++
    (if frame.cookiesFirst then
      [⟨cookieName,.data (.number cookies) true true true⟩] ++ frame.between ++
        [⟨earnedName,.data (.number earned) true true true⟩]
    else
      [⟨earnedName,.data (.number earned) true true true⟩] ++ frame.between ++
        [⟨cookieName,.data (.number cookies) true true true⟩]) ++ frame.after }

theorem find_before_cookie (frame : Fields) : frame.before.find? (fun p => p.name == cookieName) = none := by
  apply List.find?_eq_none.mpr
  intro p mem
  simp only [beq_iff_eq]
  exact (frame.clean p (by simp [mem])).1

theorem find_before_earned (frame : Fields) : frame.before.find? (fun p => p.name == earnedName) = none := by
  apply List.find?_eq_none.mpr
  intro p mem
  simp only [beq_iff_eq]
  exact (frame.clean p (by simp [mem])).2

theorem find_between_earned (frame : Fields) : frame.between.find? (fun p => p.name == earnedName) = none := by
  apply List.find?_eq_none.mpr
  intro p mem
  simp only [beq_iff_eq]
  exact (frame.clean p (by simp [mem])).2

theorem find_between_cookie (frame : Fields) : frame.between.find? (fun p => p.name == cookieName) = none := by
  apply List.find?_eq_none.mpr
  intro p mem
  simp only [beq_iff_eq]
  exact (frame.clean p (by simp [mem])).1

theorem own_cookie (frame : Fields) (cookies earned : UInt64) :
    ownProperty (object frame cookies earned) cookieName = some (.data (.number cookies) true true true) := by
  have distinct : earnedName ≠ cookieName := by decide +kernel
  cases order : frame.cookiesFirst <;>
    simp [ownProperty,object,List.find?_append,find_before_cookie,find_between_cookie,order,distinct]

theorem own_earned (frame : Fields) (cookies earned : UInt64) :
    ownProperty (object frame cookies earned) earnedName = some (.data (.number earned) true true true) := by
  have distinct : cookieName ≠ earnedName := by decide +kernel
  cases order : frame.cookiesFirst <;>
    simp [ownProperty,object,List.find?_append,find_before_earned,find_between_earned,order,distinct]

theorem set_cookie (frame : Fields) (cookies earned value : UInt64) :
    setOwnProperty (object frame cookies earned) cookieName
      (.data (.number value) true true true) = object frame value earned := by
  have first := CounterSource.map_other_fields frame.before cookieName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).1)
  have middle := CounterSource.map_other_fields frame.between cookieName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).1)
  have last := CounterSource.map_other_fields frame.after cookieName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).1)
  have distinct : earnedName ≠ cookieName := by decide +kernel
  simp only [beq_iff_eq] at first middle last
  cases order : frame.cookiesFirst <;>
    simp [setOwnProperty,object,distinct,first,middle,last,order]

theorem set_earned (frame : Fields) (cookies earned value : UInt64) :
    setOwnProperty (object frame cookies earned) earnedName
      (.data (.number value) true true true) = object frame cookies value := by
  have first := CounterSource.map_other_fields frame.before earnedName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).2)
  have middle := CounterSource.map_other_fields frame.between earnedName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).2)
  have last := CounterSource.map_other_fields frame.after earnedName
    (.data (.number value) true true true) (by
      intro p mem; exact (frame.clean p (by simp [mem])).2)
  have distinct : cookieName ≠ earnedName := by decide +kernel
  simp only [beq_iff_eq] at first middle last
  cases order : frame.cookiesFirst <;>
    simp [setOwnProperty,object,distinct,first,middle,last,order]


theorem kind_object (frame : Fields) (cookies earned : UInt64) :
    (object frame cookies earned).kind = .ordinary := rfl

theorem no_unresolved_fields (frame : Fields) (cookies earned : UInt64) :
    (object frame cookies earned).unresolvedOwnNames = [] := rfl
attribute [local cbv_eval] no_unresolved_fields

attribute [local cbv_opaque] Number.add Number.sub Number.ofNat JSString.ofString cookieName earnedName object ownProperty setOwnProperty
theorem cookie_key : JSString.ofString "cookies" = cookieName := rfl
theorem earned_key : JSString.ofString "cookiesEarned" = earnedName := rfl
attribute [local cbv_eval] cookie_key earned_key own_cookie own_earned set_cookie set_earned kind_object

def sourceState (base : Machine) (body : Stmt) (frame : Fields) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) : Machine := {
  base with
  heap := {
    objects := ⟨object frame cookies earned :: objects.toList⟩
    environments := ⟨⟨.declarative [
      { name := "Game", value := .object 0 },
      { name := "howmuch", value := .number amount }],none⟩ :: environments.toList⟩ }
  context := ⟨0,0,.object 0,false⟩
  control := .statement body
  continuation := [] }

theorem actual_earn_layout (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) :
    let before := sourceState base CounterSyntax.earnBody frame cookies earned amount objects environments
    run 37 before = { before with
      heap := { before.heap with
        objects := ⟨object frame (Number.add cookies amount) (Number.add earned amount) :: objects.toList⟩ }
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  cbv


def slotHeap (leading : List JSObject) (game : JSObject) (suffix : List JSObject)
    (environments : Array LexicalEnvironment) : Heap := {
  objects := ⟨leading ++ game :: suffix⟩
  environments }

theorem slot_size (leading : List JSObject) (game : JSObject) (suffix : List JSObject)
    (environments : Array LexicalEnvironment) :
    (slotHeap leading game suffix environments).objects.size = leading.length + suffix.length + 1 := by
  simp [slotHeap,Array.size,Nat.add_assoc]

theorem slot_read (leading : List JSObject) (game : JSObject) (suffix : List JSObject)
    (environments : Array LexicalEnvironment) :
    (slotHeap leading game suffix environments).object? leading.length = some game := by
  simp [slotHeap,Heap.object? ]

theorem slot_environments (leading : List JSObject) (game : JSObject) (suffix : List JSObject)
    (environments : Array LexicalEnvironment) :
    (slotHeap leading game suffix environments).environments = environments := rfl

theorem slot_write (leading : List JSObject) (game next : JSObject) (suffix : List JSObject)
    (environments : Array LexicalEnvironment) :
    replaceObject (slotHeap leading game suffix environments) leading.length next =
      .ok (slotHeap leading next suffix environments) := by
  simp [replaceObject,Heap.writeObject,slotHeap,Array.size ]


attribute [local cbv_opaque] slotHeap Heap.object? replaceObject List.length
attribute [local cbv_eval] slot_size slot_read slot_environments slot_write List.length_cons List.length_nil

def relocatedState (base : Machine) (body : Stmt) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (environments : Array LexicalEnvironment) : Machine := {
  base with
  heap := slotHeap leading (object frame cookies earned) trailing
    ⟨⟨.declarative [
      { name := "Game", value := .object leading.length },
      { name := "howmuch", value := .number amount }],none⟩ :: environments.toList⟩
  context := ⟨0,0,.object leading.length,false⟩
  control := .statement body
  continuation := [] }

theorem actual_earn_relocated (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (environments : Array LexicalEnvironment) :
    let before := relocatedState base CounterSyntax.earnBody frame cookies earned amount leading trailing environments
    run 37 before = { before with
      heap := slotHeap leading (object frame (Number.add cookies amount) (Number.add earned amount)) trailing
        before.heap.environments
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  cbv

theorem actual_spend_relocated (base : Machine) (frame : Fields) (cookies earned amount : UInt64)
    (leading trailing : List JSObject) (environments : Array LexicalEnvironment) :
    let before := relocatedState base CounterSyntax.spendBody frame cookies earned amount leading trailing environments
    run 20 before = { before with
      heap := slotHeap leading (object frame (Number.sub cookies amount) earned) trailing
        before.heap.environments
      control := .completion (.normal (some (.number (Number.sub cookies amount)))) } := by
  cbv

end CookieClicker.JavaScript.CounterLens




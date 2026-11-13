import CookieClicker.JavaScriptCounterSource

/-! Counter body execution with an explicit heap frame.
Extra objects, environments, and non-counter fields are retained, as are all
unrelated machine fields. These layouts put Game at object zero and its two
counter properties first. Relocation and the initialized source heap invariant
remain separate requirements; the theorems do not assume them silently.
-/
namespace CookieClicker.JavaScript.CounterSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local cbv_opaque] Number.add Number.sub Number.ofNat

def withFields (cookies earned : UInt64) (fields : List OwnProperty) : JSObject :=
  { properties := [⟨JSString.ofString "cookies", .data (.number cookies) true true true⟩,
    ⟨JSString.ofString "cookiesEarned", .data (.number earned) true true true⟩] ++ fields }

def framedState (base : Machine) (body : Stmt) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) (fields : List OwnProperty) : Machine := {
  base with
  heap := {
    objects := ⟨withFields cookies earned fields :: objects.toList⟩
    environments := ⟨⟨.declarative [
      { name := "Game", value := .object 0 },
      { name := "howmuch", value := .number amount }],none⟩ :: environments.toList⟩ }
  context := ⟨0,0,.object 0,false⟩
  control := .statement body
  continuation := [] }

theorem actual_earn_framed (base : Machine) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) (fields : List OwnProperty) :
    let before := framedState base CounterSyntax.earnBody cookies earned amount objects environments fields
    run 37 before = { before with
      heap := { before.heap with
        objects := ⟨setOwnProperty (setOwnProperty (withFields cookies earned fields) (JSString.ofString "cookies") (.data (.number (Number.add cookies amount)) true true true)) (JSString.ofString "cookiesEarned") (.data (.number (Number.add earned amount)) true true true) :: objects.toList⟩ }
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  cbv

theorem actual_spend_framed (base : Machine) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) (fields : List OwnProperty) :
    let before := framedState base CounterSyntax.spendBody cookies earned amount objects environments fields
    run 20 before = { before with
      heap := { before.heap with
        objects := ⟨setOwnProperty (withFields cookies earned fields) (JSString.ofString "cookies") (.data (.number (Number.sub cookies amount)) true true true) :: objects.toList⟩ }
      control := .completion (.normal (some (.number (Number.sub cookies amount)))) } := by
  cbv


theorem map_other_fields (fields : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor)
    (other : ∀ field ∈ fields, field.name ≠ name) :
    fields.map (fun field => if field.name == name then { field with descriptor } else field) = fields := by
  calc
    _ = fields.map id := List.map_congr_left (by
      intro field member
      simp [other field member])
    _ = fields := List.map_id fields

theorem set_cookie_other_fields (cookies earned value : UInt64) (fields : List OwnProperty)
    (other : ∀ field ∈ fields, field.name ≠ JSString.ofString "cookies") :
    setOwnProperty (withFields cookies earned fields) (JSString.ofString "cookies")
      (.data (.number value) true true true) = withFields value earned fields := by
  simp [setOwnProperty,withFields,JSString.ofString]
  simpa [JSString.ofString] using map_other_fields fields (JSString.ofString "cookies")
    (.data (.number value) true true true) other


theorem set_earned_other_fields (cookies earned value : UInt64) (fields : List OwnProperty)
    (other : ∀ field ∈ fields, field.name ≠ JSString.ofString "cookiesEarned") :
    setOwnProperty (withFields cookies earned fields) (JSString.ofString "cookiesEarned")
      (.data (.number value) true true true) = withFields cookies value fields := by
  simp [setOwnProperty,withFields,JSString.ofString]
  simpa [JSString.ofString] using map_other_fields fields (JSString.ofString "cookiesEarned")
    (.data (.number value) true true true) other

theorem actual_earn_preserves_frame (base : Machine) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) (fields : List OwnProperty)
    (noCookie : ∀ field ∈ fields, field.name ≠ JSString.ofString "cookies")
    (noEarned : ∀ field ∈ fields, field.name ≠ JSString.ofString "cookiesEarned") :
    let before := framedState base CounterSyntax.earnBody cookies earned amount objects environments fields
    run 37 before = { before with
      heap := { before.heap with
        objects := ⟨withFields (Number.add cookies amount) (Number.add earned amount) fields :: objects.toList⟩ }
      control := .completion (.normal (some (.number (Number.add earned amount)))) } := by
  dsimp only
  rw [actual_earn_framed, set_cookie_other_fields cookies earned _ fields noCookie,
    set_earned_other_fields _ earned _ fields noEarned]

theorem actual_spend_preserves_frame (base : Machine) (cookies earned amount : UInt64)
    (objects : Array JSObject) (environments : Array LexicalEnvironment) (fields : List OwnProperty)
    (noCookie : ∀ field ∈ fields, field.name ≠ JSString.ofString "cookies") :
    let before := framedState base CounterSyntax.spendBody cookies earned amount objects environments fields
    run 20 before = { before with
      heap := { before.heap with
        objects := ⟨withFields (Number.sub cookies amount) earned fields :: objects.toList⟩ }
      control := .completion (.normal (some (.number (Number.sub cookies amount)))) } := by
  dsimp only
  rw [actual_spend_framed, set_cookie_other_fields cookies earned _ fields noCookie]

end CookieClicker.JavaScript.CounterSource

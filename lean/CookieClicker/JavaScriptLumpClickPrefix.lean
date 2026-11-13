import CookieClicker.JavaScriptLumpEligibility
import CookieClicker.JavaScriptLumpChoice
/-! Source continuity from clickLump's eligibility statement to its free draw.
The clock-derived age, native eligibility closure, allocation and local writes
are retained. The two preceding DOM animations and the initialized entry frame
remain separate obligations. This result does not select a seeded outcome. -/
namespace CookieClicker.JavaScript.LumpClickPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure AgeWindow (base : Machine) (i : LumpEligibility.Inputs) where
  mature : UInt64
  ripe : UInt64
  gameMature : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpMatureAge") =
    .ok (some (.data (.number mature) true true true))
  gameRipe : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpRipeAge") =
    .ok (some (.data (.number ripe) true true true))
  isMature : Number.lessThan (LumpAge.ageValue base i.age) mature = false
  isUnripe : Number.lessThan (LumpAge.ageValue base i.age) ripe = true

def ready (base : Machine) (i : LumpEligibility.Inputs) (w : AgeWindow base i) : LumpHandPicked.Inputs :=
  LumpEligibility.branchInputs base i w.mature w.ripe w.gameMature w.gameRipe w.isMature w.isUnripe

def guardBase (base : Machine) : Machine := LumpAge.guardBase base

theorem native_eligibility_to_guard (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) (fuel : Nat) :
    Builtins.run (69+fuel) (LumpEligibility.start base i) =
      Builtins.run fuel (LumpHandPicked.start (guardBase base) (ready base i w)) :=
  LumpEligibility.native_eligibility_to_guard base i w.mature w.ripe
    w.gameMature w.gameRipe w.isMature w.isUnripe fuel

theorem ready_extends (base : Machine) (i : LumpEligibility.Inputs) (w : AgeWindow base i) :
    HeapExtension.Extends i.age.heap (ready base i w).heap :=
  HeapExtension.trans (LumpEligibility.retained_extends base i)
    (LumpAge.changed_extends base (LumpEligibility.retainedInputs base i))

theorem native_preserves_existing_objects (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) (id : ObjectId) (object : JSObject)
    (found : i.age.heap.object? id = some object) :
    (Builtins.run 69 (LumpEligibility.start base i)).heap.object? id = some object := by
  rw [show (69 : Nat) = 69+0 from rfl,native_eligibility_to_guard base i w]
  exact (ready_extends base i w).read id object found

theorem native_preserves_won (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) (achievement : ObjectId) (value : UInt64)
    (found : lookupProperty i.age.heap achievement (JSString.ofString "won") =
      .ok (some (.data (.number value) true true true))) :
    lookupProperty (Builtins.run 69 (LumpEligibility.start base i)).heap achievement (JSString.ofString "won") =
      .ok (some (.data (.number value) true true true)) := by
  rw [show (69 : Nat) = 69+0 from rfl,native_eligibility_to_guard base i w]
  exact HeapExtension.lookup_property (ready_extends base i w) _ _ _ found

theorem native_computed_age (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) :
    readBinding (Builtins.run 69 (LumpEligibility.start base i)).heap i.age.localScope "age" =
      .ok (.number ((ClockValue.Timestamp.now base.epochMilliseconds base.elapsed).difference i.age.birth)) := by
  rw [show (69 : Nat) = 69+0 from rfl,native_eligibility_to_guard base i w]
  exact (ready base i w).ageRead

theorem native_elapsed (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) :
    (Builtins.run 69 (LumpEligibility.start base i)).elapsed = base.elapsed := by
  rw [show (69 : Nat) = 69+0 from rfl,native_eligibility_to_guard base i w]
  rfl

theorem native_no_draw (base : Machine) (i : LumpEligibility.Inputs)
    (w : AgeWindow base i) :
    (Builtins.run 69 (LumpEligibility.start base i)).freeDrawCount = base.freeDrawCount := by
  rw [show (69 : Nat) = 69+0 from rfl,native_eligibility_to_guard base i w]
  rfl

def choiceCaller (base : Machine) (i : LumpEligibility.Inputs) (w : AgeWindow base i) : Machine :=
  LumpChoice.caller (guardBase base) (ready base i w)

theorem native_request (base : Machine) (i : LumpEligibility.Inputs) (w : AgeWindow base i)
    (c : ChoicePrelude.Context (choiceCaller base i w)) (target depth : Nat) (function : ObjectId)
    (chain : HasEnvironment.DeclarativePath (ready base i w).heap.environments "choose" i.age.localScope target depth)
    (room : depth ≤ (ready base i w).heap.environments.size)
    (globalRead : checkedEnvironment (ready base i w).heap target = .ok ⟨.object i.age.window false,none⟩)
    (property : lookupProperty (ready base i w).heap i.age.window (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false)))
    (source : Option JSString) (object : JSObject)
    (functionRead : checkedObject (ready base i w).heap function = .ok object)
    (functionKind : object.kind = .function (ChoiceInvocation.closure c.scope source)) :
    Builtins.run 144 (LumpEligibility.start base i) = ChoicePrelude.request (choiceCaller base i w) c function := by
  rw [show (144 : Nat) = 69+75 from rfl,native_eligibility_to_guard base i w]
  exact LumpChoice.native_request (guardBase base) (ready base i w) c target depth function
    chain room globalRead property source object functionRead functionKind

end CookieClicker.JavaScript.LumpClickPrefix

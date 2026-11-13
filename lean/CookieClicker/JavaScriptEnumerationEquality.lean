import CookieClicker.JavaScriptState

/-! Structural equality for the complete for-in fingerprint. Every object ID,
prototype link, raw name, enumerability flag and virtual string length is
compared. The Boolean implementation is proved equal to ordinary equality;
it does not cache fingerprints or allow shape mutation. -/
namespace CookieClicker.JavaScript.EnumerationEquality
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def shape (a b : EnumerationShape) : Bool :=
  a.object == b.object && a.prototype == b.prototype &&
    a.rawKeys == b.rawKeys && a.stringLength == b.stringLength

theorem shape_iff (a b : EnumerationShape) : shape a b = true ↔ a=b := by
  cases a; cases b
  simp only [shape, Bool.and_eq_true, beq_iff_eq, EnumerationShape.mk.injEq]
  simp only [and_assoc]

def same : List EnumerationShape → List EnumerationShape → Bool
  | [],[] => true
  | a :: left,b :: right => shape a b && same left right
  | _,_ => false

theorem same_iff (a b : List EnumerationShape) : same a b=true ↔ a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp [same]
  | cons head rest ih =>
    cases b with
    | nil => simp [same]
    | cons other tail => simp only [same,Bool.and_eq_true,shape_iff,ih,List.cons.injEq]

theorem same_eq_decide (a b : List EnumerationShape) : same a b=decide (a=b) := by
  cases result : same a b
  · have unequal : a≠b := by intro eq;have := (same_iff a b).mpr eq;rw [result] at this;cases this
    simp [unequal]
  · have equal : a=b := (same_iff a b).mp result
    simp [equal]

theorem same_eq_beq (a b : List EnumerationShape) : same a b=(a==b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [same_iff,beq_iff_eq]

/-- The logical definition keeps the old guard definitionally unchanged. -/
def check (a b : List EnumerationShape) : Bool := a == b

/-- Only compilation uses the faster implementation, justified by equality. -/
@[csimp] theorem check_eq_same : check = same := by
  funext a b
  exact (same_eq_beq a b).symm

theorem check_guard (a b : List EnumerationShape) : (!check a b) = (a != b) := rfl

end CookieClicker.JavaScript.EnumerationEquality

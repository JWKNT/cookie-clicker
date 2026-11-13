import CookieClicker.JavaScriptTimestampSeedSetupFactory
import CookieClicker.JavaScriptSyntaxEquality

/-! Finite structural checks of the retained seed-library source bodies.
Accepted checks carry exact syntax equality, including all literal bits. -/
namespace CookieClicker.JavaScript.SeedrandomBodyChecks
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

theorem statements_sound (fuel : Nat) (actual expected : List Stmt)
    (accepted : (SyntaxEquality.statements fuel actual expected).isSome=true) : actual=expected := by
  cases checked : SyntaxEquality.statements fuel actual expected with
  | none => simp [checked] at accepted
  | some same => exact same.down

def seedrandom (body : List Stmt) : Bool := (SyntaxEquality.statements 128 body SeedrandomInvocation.body).isSome

theorem seedrandom_sound (body : List Stmt) (accepted : seedrandom body=true) : body=SeedrandomInvocation.body :=
  statements_sound 128 body SeedrandomInvocation.body accepted

theorem seedrandom_self : seedrandom SeedrandomInvocation.body=true := by decide +kernel

def constructor (body : List Stmt) : Bool := (SyntaxEquality.statements 128 body Arc4ConstructorEntry.body).isSome

theorem constructor_sound (body : List Stmt) (accepted : constructor body=true) : body=Arc4ConstructorEntry.body :=
  statements_sound 128 body Arc4ConstructorEntry.body accepted

theorem constructor_self : constructor Arc4ConstructorEntry.body=true := by decide +kernel

def flatten (body : List Stmt) : Bool := (SyntaxEquality.statements 128 body TimestampSeedFlatten.body).isSome

theorem flatten_sound (body : List Stmt) (accepted : flatten body=true) : body=TimestampSeedFlatten.body :=
  statements_sound 128 body TimestampSeedFlatten.body accepted

theorem flatten_self : flatten TimestampSeedFlatten.body=true := by decide +kernel

def toString (body : List Stmt) : Bool := (SyntaxEquality.statements 128 body MixkeyToString.body).isSome

theorem toString_sound (body : List Stmt) (accepted : toString body=true) : body=MixkeyToString.body :=
  statements_sound 128 body MixkeyToString.body accepted

theorem toString_self : toString MixkeyToString.body=true := by decide +kernel

def closureCheck (actual expected : FunctionClosure) (bodyCheck : List Stmt → Bool) : Bool :=
  decide (actual.name=expected.name ∧ actual.parameters=expected.parameters ∧ actual.scope=expected.scope ∧
    actual.strict=expected.strict ∧ actual.sourceText=expected.sourceText) && bodyCheck actual.body

theorem closureCheck_sound (actual expected : FunctionClosure) (bodyCheck : List Stmt → Bool)
    (bodySound : ∀ body, bodyCheck body=true → body=expected.body)
    (accepted : closureCheck actual expected bodyCheck=true) : actual=expected := by
  simp only [closureCheck,Bool.and_eq_true,decide_eq_true_eq] at accepted
  have body := bodySound actual.body accepted.2
  rcases actual with ⟨name,parameters,statements,scope,strict,sourceText⟩
  rcases expected with ⟨name',parameters',statements',scope',strict',sourceText'⟩
  rcases accepted.1 with ⟨rfl,rfl,rfl,rfl,rfl⟩
  cases body
  rfl

def inspectClosure (actual expected : FunctionClosure) (bodyCheck : List Stmt → Bool)
    (bodySound : ∀ body, bodyCheck body=true → body=expected.body) : Except String (PLift (actual=expected)) :=
  if accepted : closureCheck actual expected bodyCheck=true then
    .ok ⟨closureCheck_sound actual expected bodyCheck bodySound accepted⟩
  else .error "Source closure does not match the retained syntax"

end CookieClicker.JavaScript.SeedrandomBodyChecks

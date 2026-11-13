import CookieClicker.JavaScriptSyntax

/-! A finite structural syntax check returns ordinary equality proof fields.
The fuel bound limits inspection; acceptance proves exact syntax equality. -/
namespace CookieClicker.JavaScript.SyntaxEquality
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def atom {α : Type} [DecidableEq α] (actual expected : α) : Option (PLift (actual=expected)) :=
  if same : actual=expected then some ⟨same⟩ else none

def checkList {α : Type} (check : (actual expected : α) → Option (PLift (actual=expected))) :
    (actual expected : List α) → Option (PLift (actual=expected))
  | [],[] => some ⟨rfl⟩
  | a::as,b::bs => do
    let ⟨head⟩ ← check a b
    let ⟨tail⟩ ← checkList check as bs
    pure ⟨by cases head; cases tail; rfl⟩
  | _,_ => none

def checkOption {α : Type} (check : (actual expected : α) → Option (PLift (actual=expected))) :
    (actual expected : Option α) → Option (PLift (actual=expected))
  | none,none => some ⟨rfl⟩
  | some a,some b => do
    let ⟨same⟩ ← check a b
    pure ⟨by cases same; rfl⟩
  | _,_ => none

def checkPair {α β : Type} (left : (actual expected : α) → Option (PLift (actual=expected)))
    (right : (actual expected : β) → Option (PLift (actual=expected)))
    (actual expected : α × β) : Option (PLift (actual=expected)) := do
  let ⟨first⟩ ← left actual.1 expected.1
  let ⟨second⟩ ← right actual.2 expected.2
  pure ⟨Prod.ext first second⟩

mutual
  def expr : (fuel : Nat) → (actual expected : Expr) → Option (PLift (actual=expected))
    | 0,_,_ => none
    | fuel+1,actual,expected =>
      match actual,expected with
      | .identifier a0,.identifier b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .this,.this => some ⟨rfl⟩
      | .literal a0,.literal b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .regexp a0 a1,.regexp b0 b1 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (atom) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .array a0,.array b0 => do
        let ⟨same0⟩ ← (checkList (checkOption (expr fuel))) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .object a0,.object b0 => do
        let ⟨same0⟩ ← (checkList (property fuel)) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .function a0 a1 a2 a3 a4,.function b0 b1 b2 b3 b4 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (atom) a1 b1
        let ⟨same2⟩ ← (checkList (stmt fuel)) a2 b2
        let ⟨same3⟩ ← (atom) a3 b3
        let ⟨same4⟩ ← (atom) a4 b4
        pure ⟨by cases same0; cases same1; cases same2; cases same3; cases same4; rfl⟩
      | .sequence a0,.sequence b0 => do
        let ⟨same0⟩ ← (checkList (expr fuel)) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .unary a0 a1,.unary b0 b1 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .update a0 a1 a2,.update b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (atom) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .binary a0 a1 a2,.binary b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .logical a0 a1 a2,.logical b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .assignment a0 a1 a2,.assignment b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .conditional a0 a1 a2,.conditional b0 b1 b2 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .member a0 a1 a2,.member b0 b1 b2 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (atom) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .call a0 a1,.call b0 b1 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (checkList (expr fuel)) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .clockRead a0 a1 a2,.clockRead b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .clockZero,.clockZero => some ⟨rfl⟩
      | .textIndexZero,.textIndexZero => some ⟨rfl⟩
      | .construct a0 a1,.construct b0 b1 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (checkList (expr fuel)) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .unsupported a0,.unsupported b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | _,_ => none

  def stmt : (fuel : Nat) → (actual expected : Stmt) → Option (PLift (actual=expected))
    | 0,_,_ => none
    | fuel+1,actual,expected =>
      match actual,expected with
      | .empty,.empty => some ⟨rfl⟩
      | .expression a0,.expression b0 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .block a0,.block b0 => do
        let ⟨same0⟩ ← (checkList (stmt fuel)) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .variable a0,.variable b0 => do
        let ⟨same0⟩ ← (checkList (checkPair atom (checkOption (expr fuel)))) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .functionDeclaration a0 a1 a2 a3 a4,.functionDeclaration b0 b1 b2 b3 b4 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (atom) a1 b1
        let ⟨same2⟩ ← (checkList (stmt fuel)) a2 b2
        let ⟨same3⟩ ← (atom) a3 b3
        let ⟨same4⟩ ← (atom) a4 b4
        pure ⟨by cases same0; cases same1; cases same2; cases same3; cases same4; rfl⟩
      | .ifThenElse a0 a1 a2,.ifThenElse b0 b1 b2 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (stmt fuel) a1 b1
        let ⟨same2⟩ ← (checkOption (stmt fuel)) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .while a0 a1,.while b0 b1 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        let ⟨same1⟩ ← (stmt fuel) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .doWhile a0 a1,.doWhile b0 b1 => do
        let ⟨same0⟩ ← (stmt fuel) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .forLoop a0 a1 a2 a3,.forLoop b0 b1 b2 b3 => do
        let ⟨same0⟩ ← (checkOption (forInit fuel)) a0 b0
        let ⟨same1⟩ ← (checkOption (expr fuel)) a1 b1
        let ⟨same2⟩ ← (checkOption (expr fuel)) a2 b2
        let ⟨same3⟩ ← (stmt fuel) a3 b3
        pure ⟨by cases same0; cases same1; cases same2; cases same3; rfl⟩
      | .forIn a0 a1 a2,.forIn b0 b1 b2 => do
        let ⟨same0⟩ ← (forInBinding fuel) a0 b0
        let ⟨same1⟩ ← (expr fuel) a1 b1
        let ⟨same2⟩ ← (stmt fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .return a0,.return b0 => do
        let ⟨same0⟩ ← (checkOption (expr fuel)) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .throw a0,.throw b0 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .break a0,.break b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .continue a0,.continue b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .labeled a0 a1,.labeled b0 b1 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (stmt fuel) a1 b1
        pure ⟨by cases same0; cases same1; rfl⟩
      | .tryCatchFinally a0 a1 a2,.tryCatchFinally b0 b1 b2 => do
        let ⟨same0⟩ ← (stmt fuel) a0 b0
        let ⟨same1⟩ ← (checkOption (checkPair atom (stmt fuel))) a1 b1
        let ⟨same2⟩ ← (checkOption (stmt fuel)) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩
      | .unsupported a0,.unsupported b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | _,_ => none

  def property : (fuel : Nat) → (actual expected : ObjectProperty) → Option (PLift (actual=expected))
    | 0,_,_ => none
    | fuel+1,actual,expected =>
      match actual,expected with
      | .mk a0 a1 a2,.mk b0 b1 b2 => do
        let ⟨same0⟩ ← (atom) a0 b0
        let ⟨same1⟩ ← (atom) a1 b1
        let ⟨same2⟩ ← (expr fuel) a2 b2
        pure ⟨by cases same0; cases same1; cases same2; rfl⟩

  def forInit : (fuel : Nat) → (actual expected : ForInit) → Option (PLift (actual=expected))
    | 0,_,_ => none
    | fuel+1,actual,expected =>
      match actual,expected with
      | .expression a0,.expression b0 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .variables a0,.variables b0 => do
        let ⟨same0⟩ ← (checkList (checkPair atom (checkOption (expr fuel)))) a0 b0
        pure ⟨by cases same0; rfl⟩
      | _,_ => none

  def forInBinding : (fuel : Nat) → (actual expected : ForInBinding) → Option (PLift (actual=expected))
    | 0,_,_ => none
    | fuel+1,actual,expected =>
      match actual,expected with
      | .variable a0,.variable b0 => do
        let ⟨same0⟩ ← (atom) a0 b0
        pure ⟨by cases same0; rfl⟩
      | .reference a0,.reference b0 => do
        let ⟨same0⟩ ← (expr fuel) a0 b0
        pure ⟨by cases same0; rfl⟩
      | _,_ => none

end

def statements (fuel : Nat) (actual expected : List Stmt) := checkList (stmt fuel) actual expected

end CookieClicker.JavaScript.SyntaxEquality

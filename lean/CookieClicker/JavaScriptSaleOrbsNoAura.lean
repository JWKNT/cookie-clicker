import CookieClicker.JavaScriptAuraOriginal
import CookieClicker.JavaScriptLocalAssign
import CookieClicker.JavaScriptGodzamokLocalTransport
import CookieClicker.JavaScriptGodzamokSyntax

namespace CookieClicker.JavaScript.SaleOrbsNoAura
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def branch : Stmt := match GodzamokSyntax.sellBody with
  | .block statements=>(statements[7]?).getD .empty | _=>.empty
def consequence : Stmt := match branch with | .ifThenElse _ yes _=>yes | _=>.empty
def what : JSString := JSString.ofString "Dragon Orbs"
def countExpression : Expr := .member (.member (.member (.identifier "Game") (.identifier "shimmerTypes") false)
  (.literal (.string (JSString.ofString "golden"))) true) (.identifier "n") false
def countTest : Expr := .binary .lessEqual countExpression (.literal (.number 0))
def firstTest : Expr := .logical .and (.identifier "success") countTest
def auraExpression : Expr := MemberCall.expression "auraMult" (.literal (.string what))
def auraTest : Expr := .binary .greater auraExpression (.literal (.number 0))
def condition : Expr := .logical .and firstTest auraTest

theorem source_shape : branch=.ifThenElse condition consequence none := rfl

structure Entry (base : Machine) where
  aura : AuraOriginal.Entry base
  successValue : Value
  success : DevastationWrite.Local base "success" successValue
  successful : truthy successValue=true
  shimmerTypes : ObjectId
  golden : ObjectId
  count : UInt64
  table : TieredRead.DataEdge base aura.world.game (JSString.ofString "shimmerTypes") (.object shimmerTypes)
  goldenEdge : TieredRead.DataEdge base shimmerTypes (JSString.ofString "golden") (.object golden)
  countEdge : TieredRead.DataEdge base golden (JSString.ofString "n") (.number count)

namespace Entry
variable {base : Machine}

def allowed (entry : Entry base) : Bool := Number.lessEqual entry.count 0
def steps (entry : Entry base) : Nat := if entry.allowed then 197 else 31

theorem countRead (entry : Entry base) : Reads base countExpression (.number entry.count) 17 := by
  apply entry.countEdge.dot _ 13
  apply entry.goldenEdge.key _ _ (.string (JSString.ofString "golden")) 7 1
    (entry.table.dot _ 3 entry.aura.callerRead) (literal base _) rfl
  rfl

theorem countTestRead (entry : Entry base) : Reads base countTest (.boolean entry.allowed) 21 :=
  binary_value base .lessEqual _ _ (.number entry.count) (.number 0) (.boolean entry.allowed)
    17 1 entry.countRead (literal base _) rfl rfl (by decide) rfl

theorem firstRead (entry : Entry base) : Reads base firstTest (.boolean entry.allowed) 27 :=
  LocalAssign.true_and base _ _ entry.successValue (.boolean entry.allowed) 3 21 entry.success.reads entry.countTestRead entry.successful

def changed (entry : Entry base) : Machine := if entry.allowed then
  {entry.aura.returned what with control:=.completion (.normal none)} else
  {base with control:=.completion (.normal none)}

def callFrames (base : Machine) : List Frame :=
  .binaryLeft .greater (.literal (.number 0))::.valueBoundary::.ifTest consequence none::base.continuation

theorem count_blocks (entry : Entry base) (blocked : entry.allowed=false) (fuel : Nat) :
    Builtins.run (31+fuel) {base with control:=.statement branch}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  have firstPart : Reads base firstTest (.boolean false) 27:=by simpa only [blocked] using entry.firstRead
  rw [source_shape]
  exact false_branch base condition consequence (.boolean false) 29
    (false_and base firstTest auraTest (.boolean false) 27 firstPart rfl) rfl fuel

theorem aura_blocks (entry : Entry base) (allowed : entry.allowed=true) (fuel : Nat) :
    Builtins.run (197+fuel) {base with control:=.statement branch}=
      Builtins.run fuel {entry.aura.returned what with control:=.completion (.normal none)} := by
  have firstPart : Reads base firstTest (.boolean true) 27:=by simpa only [allowed] using entry.firstRead
  conv => lhs;arg 1;rw [show 197+fuel=2+(27+(2+(161+(5+fuel)))) by omega,Nat.add_comm 2 (27+(2+(161+(5+fuel))))]
  change Builtins.run (27+(2+(161+(5+fuel)))) {base with
    control:=.expression firstTest
    continuation:=.logical .and auraTest::.ifTest consequence none::base.continuation}=_
  rw [firstPart _ (by rfl)]
  conv => lhs;arg 1;rw [Nat.add_comm 2 (161+(5+fuel))]
  change Builtins.run (161+(5+fuel)) {base with control:=.expression auraExpression,continuation:=callFrames base}=_
  refine ((entry.aura.withContinuation (callFrames base)).actual_source_call what (by decide) (5+fuel)).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 5 fuel]
  rfl

theorem actual_guard (entry : Entry base) (fuel : Nat) :
    Builtins.run (entry.steps+fuel) {base with control:=.statement branch}=Builtins.run fuel entry.changed := by
  cases gate:entry.allowed with
  | false => simpa only [steps,changed,gate,Bool.false_eq_true,ite_false] using entry.count_blocks gate fuel
  | true => simpa only [steps,changed,gate,ite_true] using entry.aura_blocks gate fuel

end Entry
end CookieClicker.JavaScript.SaleOrbsNoAura

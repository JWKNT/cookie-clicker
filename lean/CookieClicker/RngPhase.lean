import Std

/-! Source control-flow projection for free versus explicitly seeded draws.
Branches are nondeterministic, loops can run any finite number of times, and
return exits remain separate from fallthrough. The native extractor must retain
every phase change and supply sound call effects. Exceptions are separate exits.
-/
namespace CookieClicker.FullGame.RngPhase

abbrev Phase := Bool
def free : Phase := false
def seeded : Phase := true

structure Relation where
  ff : Bool
  fs : Bool
  sf : Bool
  ss : Bool
  deriving DecidableEq, Repr

def Relation.has (r : Relation) (input output : Phase) : Bool :=
  match input, output with
  | false, false => r.ff
  | false, true => r.fs
  | true, false => r.sf
  | true, true => r.ss

def zero : Relation := ⟨false, false, false, false⟩
def identity : Relation := ⟨true, false, false, true⟩
def reset : Relation := ⟨true, false, true, false⟩
def seed : Relation := ⟨false, true, false, true⟩
def unknown : Relation := ⟨true, true, true, true⟩

def union (a b : Relation) : Relation :=
  ⟨a.ff || b.ff, a.fs || b.fs, a.sf || b.sf, a.ss || b.ss⟩

def compose (a b : Relation) : Relation :=
  ⟨(a.ff && b.ff) || (a.fs && b.sf), (a.ff && b.fs) || (a.fs && b.ss),
   (a.sf && b.ff) || (a.ss && b.sf), (a.sf && b.fs) || (a.ss && b.ss)⟩

/-- In a two-state graph every path between distinct states includes the
direct crossing edge. The reflexive transitive closure therefore adds only loops. -/
def star (r : Relation) : Relation := ⟨true, r.fs, r.sf, true⟩

theorem union_left (a b : Relation) (p q : Phase) (h : a.has p q = true) :
    (union a b).has p q = true := by
  cases p <;> cases q <;> simp_all [Relation.has, union]

theorem union_right (a b : Relation) (p q : Phase) (h : b.has p q = true) :
    (union a b).has p q = true := by
  cases p <;> cases q <;> simp_all [Relation.has, union]

theorem compose_path (a b : Relation) (p m q : Phase)
    (left : a.has p m = true) (right : b.has m q = true) :
    (compose a b).has p q = true := by
  cases p <;> cases m <;> cases q <;> simp_all [Relation.has, compose]

theorem star_self (r : Relation) (p : Phase) : (star r).has p p = true := by
  cases p <;> rfl

theorem star_edge (r : Relation) (p q : Phase) (h : r.has p q = true) :
    (star r).has p q = true := by
  cases p <;> cases q <;> simp_all [Relation.has, star]

theorem star_trans (r : Relation) (p m q : Phase)
    (left : (star r).has p m = true) (right : (star r).has m q = true) :
    (star r).has p q = true := by
  cases p <;> cases m <;> cases q <;> simp_all [Relation.has, star]

inductive Exit where
  | normal | returned
  deriving DecidableEq

structure Flow where
  normal : Relation
  returned : Relation
  deriving DecidableEq, Repr

def Flow.has (flow : Flow) (exit : Exit) (p q : Phase) : Bool :=
  match exit with
  | .normal => flow.normal.has p q
  | .returned => flow.returned.has p q

inductive Code where
  | effect (relation : Relation)
  | ret
  | seq (first second : Code)
  | branch (yes no : Code)
  | loop (body : Code)
  | invoke (body : Code)
  deriving Repr

def analyze : Code → Flow
  | .effect relation => ⟨relation, zero⟩
  | .ret => ⟨zero, identity⟩
  | .seq first second =>
    let a := analyze first
    let b := analyze second
    ⟨compose a.normal b.normal, union a.returned (compose a.normal b.returned)⟩
  | .branch yes no =>
    let a := analyze yes
    let b := analyze no
    ⟨union a.normal b.normal, union a.returned b.returned⟩
  | .loop body =>
    let a := analyze body
    ⟨star a.normal, compose (star a.normal) a.returned⟩
  | .invoke body =>
    let a := analyze body
    ⟨union a.normal a.returned, zero⟩

/-- Finite execution of the projected source control flow. An effect may be
a verified source helper or an unresolved overapproximation, never an omitted call. -/
inductive Executes : Code → Phase → Exit → Phase → Prop where
  | effect {relation p q} (allowed : relation.has p q = true) :
      Executes (.effect relation) p .normal q
  | ret {p} : Executes .ret p .returned p
  | seqReturn {first second p q} (firstReturns : Executes first p .returned q) :
      Executes (.seq first second) p .returned q
  | seqNext {first second p m exit q}
      (firstDone : Executes first p .normal m) (secondDone : Executes second m exit q) :
      Executes (.seq first second) p exit q
  | branchYes {yes no p exit q} (selected : Executes yes p exit q) :
      Executes (.branch yes no) p exit q
  | branchNo {yes no p exit q} (selected : Executes no p exit q) :
      Executes (.branch yes no) p exit q
  | loopDone {body p} : Executes (.loop body) p .normal p
  | loopReturn {body p q} (bodyReturns : Executes body p .returned q) :
      Executes (.loop body) p .returned q
  | loopNext {body p m exit q}
      (bodyDone : Executes body p .normal m) (rest : Executes (.loop body) m exit q) :
      Executes (.loop body) p exit q
  | invoke {body p exit q} (called : Executes body p exit q) :
      Executes (.invoke body) p .normal q

theorem compose_star_left (r b : Relation) (p m q : Phase)
    (first : r.has p m = true) (rest : (compose (star r) b).has m q = true) :
    (compose (star r) b).has p q = true := by
  cases p <;> cases m <;> cases q <;>
    simp_all [compose, star, Relation.has] <;> grind

theorem analysis_sound {code : Code} {p q : Phase} {exit : Exit}
    (execution : Executes code p exit q) : (analyze code).has exit p q = true := by
  induction execution with
  | effect allowed => exact allowed
  | @ret phase => cases phase <;> rfl
  | seqReturn _ ih => exact union_left _ _ _ _ ih
  | @seqNext first second input middle outcome output _ _ ih₁ ih₂ =>
      cases outcome with
      | normal => exact compose_path _ _ _ _ _ ih₁ ih₂
      | returned => exact union_right _ _ _ _ (compose_path _ _ _ _ _ ih₁ ih₂)
  | @branchYes yes no input outcome output _ ih => cases outcome <;> exact union_left _ _ _ _ ih
  | @branchNo yes no input outcome output _ ih => cases outcome <;> exact union_right _ _ _ _ ih
  | loopDone => exact star_self _ _
  | loopReturn _ ih => exact compose_path _ _ _ _ _ (star_self _ _) ih
  | @loopNext body input middle outcome output _ _ ih₁ ih₂ =>
      cases outcome with
      | normal => exact star_trans _ _ _ _ (star_edge _ _ _ ih₁) ih₂
      | returned => exact compose_star_left _ _ _ _ _ ih₁ ih₂
  | @invoke body input outcome output _ ih =>
      cases outcome with
      | normal => exact union_left _ _ _ _ ih
      | returned => exact union_right _ _ _ _ ih

def restoresFree (code : Code) : Bool :=
  !((analyze code).normal.has free seeded || (analyze code).returned.has free seeded)

theorem restores_free_sound (code : Code) (checked : restoresFree code = true)
    (exit : Exit) (q : Phase) (execution : Executes code free exit q) : q = free := by
  have sound := analysis_sound execution
  cases q with
  | false => rfl
  | true =>
    cases exit <;> simp_all [restoresFree, Flow.has, free, seeded, Relation.has]

theorem unknown_after_reset_rejected :
    restoresFree (.seq (.effect reset) (.effect unknown)) = false := by decide +kernel

theorem reset_after_unknown_restores :
    restoresFree (.seq (.effect unknown) (.effect reset)) = true := by decide +kernel

theorem early_return_leak_rejected :
    restoresFree (.seq (.effect seed)
      (.seq (.branch .ret (.effect identity)) (.effect reset))) = false := by decide +kernel

theorem loop_return_leak_rejected :
    restoresFree (.loop (.seq (.effect seed)
      (.seq (.branch .ret (.effect identity)) (.effect reset)))) = false := by decide +kernel

end CookieClicker.FullGame.RngPhase

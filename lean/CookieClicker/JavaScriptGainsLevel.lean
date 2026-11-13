import CookieClicker.JavaScriptGainsCacheWrites

namespace CookieClicker.JavaScript.GainsLevel
open SourceRead TieredRead GainsCacheWrites
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def statement : Stmt := (GainsCommonCache.body.drop 2).headD .empty

def condition : Expr := .binary .notEqual
  (.member (.identifier "Game") (.identifier "ascensionMode") false)
  (.literal (.number Number.one))

def factor : Expr := .binary .multiply (.binary .add (.literal (.number Number.one))
  (.binary .multiply (.member (.identifier "me") (.identifier "level") false)
    (.literal (.number 4576918229304087675)))) (.identifier "buildMult")

def update : Stmt := .expression (.assignment .multiply
  (.member (.identifier "me") (.identifier "storedCps") false) factor)

theorem source_statement : statement=.ifThenElse condition update none := rfl

theorem condition_read (base : Machine) (game : ObjectId)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (mode : DataEdge base game (JSString.ofString "ascensionMode") (.number Number.positiveZero)) :
    Reads base condition (.boolean true) 11 := by
  apply binary_value base .notEqual _ _ (.number Number.positiveZero) (.number Number.one) _ 7 1
    (mode.dot _ _ gameRead) (literal base (.number Number.one)) rfl rfl (by decide)
  rfl

theorem factor_read (base : Machine) (me : ObjectId)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (level : DataEdge base me (JSString.ofString "level") (.number Number.positiveZero))
    (buildMult : Reads base (.identifier "buildMult") (.number Number.one) 3) :
    Reads base factor (.number Number.one) 21 := by
  have first : Reads base (.binary .multiply
      (.member (.identifier "me") (.identifier "level") false)
      (.literal (.number 4576918229304087675))) (.number Number.positiveZero) 11 := by
    apply binary_value base .multiply _ _ (.number Number.positiveZero) (.number 4576918229304087675)
      _ 7 1 (level.dot _ _ meRead) (literal base (.number 4576918229304087675)) rfl rfl (by decide)
    change (Except.ok (.number (Number.mul 0 4576918229304087675)) : Checked Value)=.ok (.number 0)
    exact congrArg Except.ok (congrArg Value.number (by decide +kernel))
  have second : Reads base (.binary .add (.literal (.number Number.one))
      (.binary .multiply (.member (.identifier "me") (.identifier "level") false)
        (.literal (.number 4576918229304087675)))) (.number Number.one) 15 := by
    apply binary_value base .add _ _ (.number Number.one) (.number Number.positiveZero)
      _ 1 11 (literal base (.number Number.one)) first rfl rfl (by decide)
    change (Except.ok (.number (Number.add Number.one 0)) : Checked Value)=.ok (.number Number.one)
    exact congrArg Except.ok (congrArg Value.number (by decide +kernel))
  apply binary_value base .multiply _ _ (.number Number.one) (.number Number.one)
    _ 15 3 second buildMult rfl rfl (by decide)
  change (Except.ok (.number (Number.mul Number.one Number.one)) : Checked Value)=.ok (.number Number.one)
  exact congrArg Except.ok (congrArg Value.number (by decide +kernel))

/-- Normal ascension applies the native level multiplier even at level zero;
the resulting cache write and its descriptor effects are retained. -/
theorem native_statement (base : Machine) (game me : ObjectId) (cps : UInt64)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (mode : DataEdge base game (JSString.ofString "ascensionMode") (.number Number.positiveZero))
    (level : DataEdge base me (JSString.ofString "level") (.number Number.positiveZero))
    (buildMult : Reads base (.identifier "buildMult") (.number Number.one) 3)
    (write : Writable base me (JSString.ofString "storedCps"))
    (previous : write.previous=.number cps) (fuel : Nat) :
    Builtins.run (48+fuel) {base with control:=.statement statement}=
      Builtins.run fuel (write.after (.number (Number.mul cps Number.one))) := by
  rw [source_statement,show 48+fuel=1+(11+(1+(10+(21+(4+fuel))))) by omega,
    Nat.add_comm 1 (11+(1+(10+(21+(4+fuel)))))]
  change Builtins.run (11+(1+(10+(21+(4+fuel))))) {base with
    control:=.expression condition,continuation:=.ifTest update none::base.continuation}=_
  rw [condition_read base game gameRead mode _ (by rfl),Nat.add_comm 1 (10+(21+(4+fuel)))]
  change Builtins.run (10+(21+(4+fuel))) {base with control:=.statement update}=_
  have present : checkedObject base.heap me=.ok write.object := by simp [checkedObject,write.present]
  have lookup : lookupProperty base.heap me (JSString.ofString "storedCps")=
      .ok (some (.data (.number cps) true true true)) := by simpa only [previous] using write.lookup
  have own : ownProperty write.object (JSString.ofString "storedCps")=
      some (.data (.number cps) true true true) := by simpa only [previous] using write.own
  have prelude :=  PropertyCompound.dot_prefix base (.identifier "me") factor me "storedCps" .multiply
    (by decide) (.number cps) write.object 3 meRead present write.ordinary lookup (21+(4+fuel))
  refine prelude.trans ?_
  have rhs := factor_read base me meRead level buildMult
  refine (rhs _ (by rfl) (4+fuel)).trans ?_
  exact PropertyCompound.dot_suffix base me "storedCps" .multiply .multiply rfl write.object
    (.number cps) (.number Number.one) (.number (Number.mul cps Number.one)) rfl rfl (by decide) rfl
    write.present write.ordinary own lookup fuel

end CookieClicker.JavaScript.GainsLevel

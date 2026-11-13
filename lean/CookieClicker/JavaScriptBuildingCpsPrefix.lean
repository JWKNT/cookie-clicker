import CookieClicker.JavaScriptBuildingDigits

namespace CookieClicker.JavaScript.BuildingCpsPrefix
open SourceRead BuildingCpsArithmetic BuildingCpsRead
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Inputs (base : Machine) (n : UInt64) where
  cps : BuildingStore.Slot base (JSString.ofString "baseCps")
  thisCps : base.context.thisValue=.object cps.id
  known : cps.object.unresolvedOwnNames=[]
  nSlot : BuildingStore.Slot base (JSString.ofString "n")
  thisN : base.context.thisValue=.object nSlot.id
  nValue : nSlot.oldValue=.number n
  power : BuildingMathRead.Binding base "pow"
  ceiling : BuildingMathRead.Binding base "ceil"
  localDigits : BuildingDigits.Slot (cps.after (.number (raw n)))
  scalePower : BuildingMathRead.Binding (cps.after (.number (raw n))) "pow"
  scaleCeiling : BuildingMathRead.Binding (cps.after (.number (raw n))) "ceil"
  scaleLog : BuildingMathRead.Binding (cps.after (.number (raw n))) "log"
  ln10Constant : BuildingMathRead.Constant (cps.after (.number (raw n))) "LN10" ln10
  rounding : BuildingMathRead.Binding (localDigits.after (.number (digits (raw n)))) "round"

def Inputs.afterRaw {base : Machine} {n : UInt64} (input : Inputs base n) : Machine :=
  input.cps.after (.number (raw n))
def Inputs.afterDigits {base : Machine} {n : UInt64} (input : Inputs base n) : Machine :=
  input.localDigits.after (.number (digits (raw n)))
def Inputs.finalSlot {base : Machine} {n : UInt64} (input : Inputs base n) :
    BuildingStore.Slot input.afterDigits (JSString.ofString "baseCps") :=
  (input.cps.next (.number (raw n)) input.known).transport input.afterDigits rfl

def Inputs.after {base : Machine} {n : UInt64} (input : Inputs base n) : Machine :=
  input.finalSlot.after (.number (rounded (raw n) (digits (raw n))))

def rawStatement : Stmt := BuildingConstructorSyntax.cpsPrefix.headD .empty
def scaleStatement : Stmt := (BuildingConstructorSyntax.cpsPrefix.drop 1).headD .empty
def roundStatement : Stmt := (BuildingConstructorSyntax.cpsPrefix.drop 2).headD .empty

theorem source_partition : BuildingConstructorSyntax.numericStatements=
    rawStatement::scaleStatement::roundStatement::BuildingConstructorSyntax.priceSuffix := rfl

theorem Inputs.n_read {base : Machine} {n : UInt64} (input : Inputs base n) :
    Reads base nExpression (.number n) 5 := by
  simpa only [input.nValue,nExpression] using input.nSlot.read_this "n" input.thisN

theorem Inputs.raw_read {base : Machine} {n : UInt64} (input : Inputs base n) :
    Reads base rawExpression (.number (raw n)) 55 :=
  BuildingCpsRead.raw_read base input.power input.ceiling n input.n_read

theorem Inputs.scale_read {base : Machine} {n : UInt64} (input : Inputs base n) :
    Reads input.afterRaw scaleExpression (.number (digits (raw n))) 69 := by
  have valueRead:Reads input.afterRaw baseExpression (.number (raw n)) 5 :=
    (input.cps.next (.number (raw n)) input.known).read_this "baseCps" input.thisCps
  exact BuildingCpsRead.scale_read input.afterRaw input.scalePower input.scaleCeiling input.scaleLog
    (raw n) valueRead input.ln10Constant.read

theorem Inputs.round_read {base : Machine} {n : UInt64} (input : Inputs base n) :
    Reads input.afterDigits roundExpression (.number (rounded (raw n) (digits (raw n)))) 29 := by
  have valueRead:Reads input.afterDigits baseExpression (.number (raw n)) 5 :=
    input.finalSlot.read_this "baseCps" input.thisCps
  exact BuildingCpsRead.round_read input.afterDigits input.rounding (raw n) (digits (raw n))
    valueRead (input.localDigits.read (.number (digits (raw n))))

theorem Inputs.raw_statement {base : Machine} {n : UInt64} (input : Inputs base n)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (64+fuel) {base with control:=.statement rawStatement,continuation}=
      Builtins.run fuel {input.afterRaw with control:=.completion (.normal (some (.number (raw n)))),continuation} := by
  rw [show rawStatement=.expression (.assignment .assign baseExpression rawExpression) from raw_source]
  exact BuildingStore.assign_this {base with continuation} "baseCps" {input.cps with} input.thisCps
    rawExpression (.number (raw n)) 55 input.raw_read fuel

theorem Inputs.scale_statement {base : Machine} {n : UInt64} (input : Inputs base n)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (73+fuel) {input.afterRaw with control:=.statement scaleStatement,continuation}=
      Builtins.run fuel {input.afterDigits with control:=.completion (.normal none),continuation} := by
  rw [show scaleStatement=.variable [("digits",some scaleExpression)] from scale_source]
  exact BuildingDigits.native_variable {input.afterRaw with continuation} {input.localDigits with}
    scaleExpression (.number (digits (raw n))) 69 input.scale_read (by rfl) fuel

theorem Inputs.round_statement {base : Machine} {n : UInt64} (input : Inputs base n)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (38+fuel) {input.afterDigits with control:=.statement roundStatement,continuation}=
      Builtins.run fuel {input.after with
        control:=.completion (.normal (some (.number (rounded (raw n) (digits (raw n)))))),continuation} := by
  rw [show roundStatement=.expression (.assignment .assign baseExpression roundExpression) from round_source]
  exact BuildingStore.assign_this {input.afterDigits with continuation} "baseCps" {input.finalSlot with}
    input.thisCps roundExpression (.number (rounded (raw n) (digits (raw n)))) 29 input.round_read fuel

theorem next_value (base : Machine) (first : Stmt) (rest : List Stmt) (previous : Option Value)
    (value : Value) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal (some value)),continuation:=.statementList (first::rest) previous::continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList rest (some value)::continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem next_none (base : Machine) (first : Stmt) (rest : List Stmt) (previous : Option Value)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none),continuation:=.statementList (first::rest) previous::continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList rest previous::continuation} := by
  rw [Nat.add_comm 1 fuel]
  cases previous <;> rfl

/-- Runs the three arithmetic statements from their actual twelve-statement
block. The nine price statements remain as the native statement continuation. -/
theorem Inputs.native_prefix {base : Machine} {n : UInt64} (input : Inputs base n) (fuel : Nat) :
    Builtins.run (178+fuel) {base with control:=.statement (.block BuildingConstructorSyntax.numericStatements)}=
      Builtins.run fuel {input.after with
        control:=.completion (.normal (some (.number (output n).1)))
        continuation:=.statementList BuildingConstructorSyntax.priceSuffix (some (.number (raw n)))::base.continuation} := by
  rw [source_partition,show 178+fuel=1+(64+(1+(73+(1+(38+fuel))))) by omega,
    Nat.add_comm 1 (64+(1+(73+(1+(38+fuel)))))]
  change Builtins.run (64+(1+(73+(1+(38+fuel))))) {base with
    control:=.statement rawStatement
    continuation:=.statementList (scaleStatement::roundStatement::BuildingConstructorSyntax.priceSuffix) none::base.continuation}=_
  rw [input.raw_statement,next_value,input.scale_statement,next_none,input.round_statement]
  rfl

 theorem Inputs.native_branch {base : Machine} {n : UInt64} (input : Inputs base n)
    (nonzero : Number.equal n Number.positiveZero=false) (fuel : Nat) :
    Builtins.run (189+fuel) {base with control:=.statement BuildingConstructorSyntax.numericBranch}=
      Builtins.run fuel {input.after with
        control:=.completion (.normal (some (.number (output n).1)))
        continuation:=.statementList BuildingConstructorSyntax.priceSuffix (some (.number (raw n)))::base.continuation} := by
  have condition:Reads base (.binary .notEqual nExpression (.literal (.number Number.positiveZero))) (.boolean true) 9 := by
    apply binary_value base .notEqual nExpression (.literal (.number Number.positiveZero))
      (.number n) (.number Number.positiveZero) (.boolean true) 5 1 input.n_read
      (literal _ (.number Number.positiveZero)) rfl rfl (by decide)
    simp [binaryWithHeap,binary,abstractEqual,sameType,strictEqual,nonzero,Except.bind,bind,Except.pure,pure]
  rw [show 189+fuel=1+(9+(1+(178+fuel))) by omega,Nat.add_comm 1 (9+(1+(178+fuel)))]
  change Builtins.run (9+(1+(178+fuel))) {base with
    control:=.expression (.binary .notEqual nExpression (.literal (.number Number.positiveZero)))
    continuation:=.ifTest (.block BuildingConstructorSyntax.numericStatements) none::base.continuation}=_
  rw [condition _ (by rfl),Nat.add_comm 1 (178+fuel)]
  exact input.native_prefix fuel

end CookieClicker.JavaScript.BuildingCpsPrefix

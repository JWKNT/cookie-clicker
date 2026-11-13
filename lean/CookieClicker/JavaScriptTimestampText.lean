import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptSeedrandomMixkeySyntax

/-! Scoped source activation for the selected unbounded timestamp-text rule.
The captured source closure remains untouched. The activation retains the actual
mixkey loop and changes only its index-zero initializer to an exact index. -/
namespace CookieClicker.JavaScript.TimestampText

open SeedrandomMixkeySyntax

def nativeBody : List Stmt := match mixkeyBody with | .block body => body | other => [other]

/-- Closed recognition of the complete pinned helper body, with no recursive
AST equality oracle. Every other syntax shape is rejected. -/
def nativeBodyMatches : List Stmt → Bool
  | [
  (.forLoop (some (.variables [("d", none), ("c", (some (.binary .add (.identifier "a") (.literal (.string []))))), ("e", (some (.literal (.number zero))))])) (some (.binary .greater (.member (.identifier "c") (.identifier "length") false) (.identifier "e"))) none (.expression (.assignment .assign (.member (.identifier "b") (.binary .bitAnd (.identifier "j") (.identifier "e")) true) (.binary .bitAnd (.identifier "j") (.binary .add (.assignment .bitXor (.identifier "d") (.binary .multiply (.literal (.number nineteen)) (.member (.identifier "b") (.binary .bitAnd (.identifier "j") (.identifier "e")) true))) (.call (.member (.identifier "c") (.identifier "charCodeAt") false) [(.update .increment (.identifier "e") false)])))))),
  (.return (some (.call (.identifier "o") [(.identifier "b")])))] => decide (zero = (0 : UInt64) ∧ nineteen = (4626041242239631360 : UInt64))
  | _ => false

def nativeClosure (closure : FunctionClosure) : Bool :=
  closure.parameters == ["a","b"] && !closure.strict &&
    nativeBodyMatches closure.body && closure.sourceText == some mixkeyText

theorem nativeBodyMatches_self : nativeBodyMatches nativeBody = true := by
  decide +kernel

theorem nativeBodyMatches_sound (body : List Stmt) (accepted : nativeBodyMatches body = true) :
    body = nativeBody := by
  unfold nativeBodyMatches at accepted
  split at accepted
  next zero nineteen =>
    simp only [decide_eq_true_eq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    rfl
  next => contradiction

def activationBody : List Stmt := match nativeBody with
  | .forLoop (some (.variables declarations)) test update body :: remaining =>
      .forLoop (some (.variables (declarations.map fun (name,value) =>
        if name == "e" then (name,some .textIndexZero) else (name,value)))) test update body :: remaining
  | _ => []

def activation (closure : FunctionClosure) : FunctionClosure :=
  { closure with body := activationBody }

def invoke (machine : Machine) (function : ObjectId) (receiver : Value)
    (arguments : List Value) : Checked Machine := do
  let object ← checkedObject machine.heap function
  let .function closure := object.kind |
    throw (.unresolved (.unsupportedSyntax "Captured timestamp mixkey is no longer a source closure"))
  if !nativeClosure closure then
    throw (.unresolved (.unsupportedSyntax "Captured timestamp mixkey source body changed"))
  let some (.timestampText _) := arguments.head? |
    throw (.fault (.invalidContinuation "Timestamp mixkey activation requires timestamp-text input"))
  prepareCall machine (activation closure) receiver arguments none (some function)

theorem activation_sourceText (closure : FunctionClosure) :
    (activation closure).sourceText = closure.sourceText := rfl

theorem activation_scope (closure : FunctionClosure) :
    (activation closure).scope = closure.scope := rfl

theorem activation_parameters (closure : FunctionClosure) :
    (activation closure).parameters = closure.parameters := rfl

end CookieClicker.JavaScript.TimestampText

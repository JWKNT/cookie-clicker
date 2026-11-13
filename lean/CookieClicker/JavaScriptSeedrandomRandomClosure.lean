import CookieClicker.JavaScriptSeedrandomInvocation
import CookieClicker.JavaScriptArc4GeneratorAllocation

/-! Allocation of the exact random function expression retained in seedrandom's
return sequence. The closure captures the real seedrandom activation. -/
namespace CookieClicker.JavaScript.SeedrandomRandomClosure
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def returnStatement : Stmt := SeedrandomInvocation.body[1]?.getD .empty
def returnExpression : Expr := match returnStatement with
  | .return (some expression) => expression
  | _ => .literal .null
def sequence : List Expr := match returnExpression with
  | .sequence expressions => expressions
  | _ => []
def entropyExpression : Expr := sequence[0]?.getD (.literal .null)
def assignment : Expr := sequence[1]?.getD (.literal .null)
def expression : Expr := match assignment with
  | .assignment .assign _ value => value
  | _ => .literal .null
def closure (scope : EnvId) : FunctionClosure := match expression with
  | .function name parameters body strict sourceText => ⟨name,parameters,body,scope,strict,sourceText⟩
  | _ => ⟨none,[],[],scope,false,none⟩

def functionObject (base : Machine) (scope : EnvId) : JSObject := {
  kind := .function (closure scope)
  prototype := base.functionPrototype
  unresolvedOwnNames := [JSString.ofString "arguments",JSString.ofString "caller"]
  properties := [⟨JSString.ofString "length",.data (.number (Number.ofNat 0)) false false true⟩,
    ⟨JSString.ofString "name",.data (.string []) false false true⟩,
    ⟨JSString.ofString "prototype",.data (.object (base.heap.objects.size+1)) true false false⟩] }
def prototypeObject (base : Machine) : JSObject := {
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "constructor",.data (.object base.heap.objects.size) true false true⟩] }
def objects (base : Machine) (scope : EnvId) :=
  (base.heap.objects.push (functionObject base scope)).push (prototypeObject base)
def allocated (base : Machine) (scope : EnvId) : Machine := {
  base with heap := {base.heap with objects := objects base scope} }

theorem actual_allocate (base : Machine) (scope : EnvId) :
    allocateFunction base (closure scope)=.ok (.object base.heap.objects.size,allocated base scope) := by
  have bound : base.heap.objects.size<base.heap.objects.size+1+1 := by omega
  simp [bound,JSString.ofString,allocateFunction,closure,expression,assignment,sequence,returnExpression,returnStatement,
    SeedrandomInvocation.body,SeedrandomSyntax.seedrandomBody,
    Heap.allocateObject,replaceObject,Heap.writeObject,allocated,objects,functionObject,prototypeObject,
    setOwnProperty,ownProperty,Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem actual_expression (base : Machine) :
    Builtins.builtinStep {base with control := .expression expression}=
      result (allocated base base.context.lexicalEnvironment) (.object base.heap.objects.size) := by
  change {checked base (allocateFunction {base with control := .expression expression} (closure base.context.lexicalEnvironment))
    (fun (value,next) => result next value) with elapsed := base.elapsed}=_
  rw [actual_allocate]
  rfl

theorem extension (base : Machine) (scope : EnvId) : HeapExtension.Extends base.heap (allocated base scope).heap :=
  HeapExtension.trans (HeapExtension.append_object _ (functionObject base scope))
    (HeapExtension.append_object _ (prototypeObject base))

theorem function_present (base : Machine) (scope : EnvId) :
    checkedObject (allocated base scope).heap base.heap.objects.size=.ok (functionObject base scope) := by
  simp [checkedObject,Heap.object?,allocated,objects,Array.getElem?_push]

end CookieClicker.JavaScript.SeedrandomRandomClosure

import CookieClicker.JavaScriptPropertyAssign
import CookieClicker.JavaScriptCommonCpsComplete
import CookieClicker.JavaScriptGainsLoopSyntax

namespace CookieClicker.JavaScript.GainsCommonCache
open SourceRead CommonCpsComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def loop : Stmt := match GainsLoopSyntax.buildingLoopBody with
  | .block [statement] => statement
  | _ => .empty

def body : List Stmt := match loop with
  | .forIn _ _ (.block statements) => statements
  | _ => []

def statement : Stmt := (body.drop 1).headD .empty

theorem source_statement : statement=.expression (.assignment .assign
    (.member (.identifier "me") (.identifier "storedCps") false) CommonCpsCall.expression) := rfl

def callBase (base : Machine) (me : ObjectId) : Machine :=
  PropertyAssign.right base me "storedCps" CommonCpsCall.expression

structure Inputs (base : Machine) (me : ObjectId) where
  window : ObjectId
  function : ObjectId
  scopes : HasEnvironment.Scopes window
  source : Option JSString
  object : JSObject
  functionObject : JSObject
  call : CommonCpsComplete.Inputs
    (CommonCpsCall.bodyBase (callBase base me) scopes.closureScope me me function) scopes
    (CommonCpsComplete.initialized (CommonCpsCall.state (callBase base me) me function))
  environments : scopes.environments=base.heap.environments
  global : base.globalObject=window
  exclusions : base.objectEnvironmentExclusions=[]
  present : checkedObject base.heap me=.ok object
  kind : object.kind=.ordinary
  property : lookupProperty base.heap me (JSString.ofString "cps")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CommonCpsSource.closure scopes.closureScope source)
  read : SourceRead.Reads base (.identifier "me") (.object me) 3
  previous : Value
  cacheOwn : ownProperty object (JSString.ofString "storedCps")=
    some (.data previous true true true)
  cacheLookup : lookupProperty base.heap me (JSString.ofString "storedCps")=
    .ok (some (.data previous true true true))

def Inputs.returned {base : Machine} {me : ObjectId} (input : Inputs base me) : Machine :=
  CommonCpsCall.returned (callBase base me) input.scopes me me input.function input.call

def Inputs.value {base : Machine} {me : ObjectId} (input : Inputs base me) : Value :=
  .number (Number.mul input.call.baseCps Number.one)

def Inputs.after {base : Machine} {me : ObjectId} (input : Inputs base me) : Machine := {
  input.returned with
  heap:=PropertyFrame.write input.returned.heap me input.object (JSString.ofString "storedCps") input.value true true
  control:=.completion (.normal (some input.value))
  continuation:=base.continuation }

theorem Inputs.returned_extends {base : Machine} {me : ObjectId} (input : Inputs base me) :
    HeapExtension.Extends base.heap input.returned.heap :=
  CommonCpsCall.returned_extends (callBase base me) input.scopes me me input.function input.call

/-- The intact cache statement calls the complete source production callback,
then performs the actual ordinary-property write. The callback is not supplied
as a scalar result premise. -/
theorem Inputs.native_statement {base : Machine} {me : ObjectId} (input : Inputs base me)
    (fuel : Nat) :
    Builtins.run (input.call.work+187+fuel) {base with control:=.statement statement}=
      Builtins.run fuel input.after := by
  rw [source_statement,show input.call.work+187+fuel=8+(input.call.work+176+(3+fuel)) by omega]
  rw [PropertyAssign.dot_prefix base (.identifier "me") CommonCpsCall.expression me "storedCps" 3 input.read]
  have called := CommonCpsCall.source_call (callBase base me) input.scopes me input.function input.source
    input.object input.functionObject input.call input.environments input.global input.exclusions
    input.present input.kind input.property input.functionPresent input.functionKind input.read (3+fuel)
  refine called.trans ?_
  have checked := HeapExtension.checked_object input.returned_extends me input.object input.present
  have present : input.returned.heap.object? me=some input.object := by
    cases h : input.returned.heap.object? me with
    | none => simp [checkedObject,h] at checked
    | some current => simpa [checkedObject,h] using checked
  have lookup := HeapExtension.lookup_property input.returned_extends me
    (JSString.ofString "storedCps") _ input.cacheLookup
  have written := PropertyAssign.dot_suffix
    {input.returned with continuation:=base.continuation} me "storedCps" input.object input.previous
    input.value true true present input.kind input.cacheOwn lookup fuel
  exact written

theorem Inputs.cached_value {base : Machine} {me : ObjectId} (input : Inputs base me) :
    input.after.heap.object? me=some
      (setOwnProperty input.object (JSString.ofString "storedCps") (.data input.value true true true)) := by
  have checked := HeapExtension.checked_object input.returned_extends me input.object input.present
  have present : input.returned.heap.object? me=some input.object := by
    cases h : input.returned.heap.object? me with
    | none => simp [checkedObject,h] at checked
    | some current => simpa [checkedObject,h] using checked
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  exact PropertyFrame.replaced_read input.returned.heap me _ bounded

theorem Inputs.cached_descriptor {base : Machine} {me : ObjectId} (input : Inputs base me) :
    ownProperty (setOwnProperty input.object (JSString.ofString "storedCps")
      (.data input.value true true true)) (JSString.ofString "storedCps")=
        some (.data input.value true true true) := PropertyFrame.own_set _ _ _

end CookieClicker.JavaScript.GainsCommonCache

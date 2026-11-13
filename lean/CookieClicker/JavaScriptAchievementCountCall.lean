import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptAchievementCountSyntax
import CookieClicker.JavaScriptReadCombinators
import CookieClicker.JavaScriptAllocatedGameRead

/-! The native achievement-count predicate for every string pool.
Native lookup, argument allocation, declaration scan and caller return remain. -/
namespace CookieClicker.JavaScript.AchievementCountCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def body : List Stmt := match AchievementCountSyntax.CountsAsAchievementOwnedBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["pool"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (name : JSString) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"pool")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.string name) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }
def locals (base : Machine) (name : JSString) : List Binding :=
  [{name:="pool",value:=.string name},
   {name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject base name callee)
  environments := base.heap.environments.push ⟨.declarative (locals base name),some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none::base.continuation
  control := .declarationScan (body.map (true,·)) [] [] body }
def started (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  prepared base scope game name callee with control := .statement AchievementCountSyntax.CountsAsAchievementOwnedBody }
def returned (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  control := .expressionResult (.value (.boolean (name=[] || name=[110,111,114,109,97,108]))) }

theorem actual_prepare (base : Machine) (scope : EnvId) (game : ObjectId)
    (source : Option JSString) (name : JSString) (callee : Option ObjectId := none) :
    prepareCall (callee:=callee) base (closure scope source) (.object game) [.string name] none =
      .ok (prepared base scope game name callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem name_reference (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    identifierReference (started base scope game name callee) "pool" =
      .ok ⟨.environment (localIndex base) "pool",false⟩ := by
  simp [started,prepared,identifierReference,localIndex,allocatedHeap,resolveName,
    checkedEnvironment,Heap.environment?,locals,bind,Except.bind,pure,Except.pure]

theorem local_environment (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    checkedEnvironment (started base scope game name callee).heap
      (started base scope game name callee).context.lexicalEnvironment =
      .ok ⟨.declarative (locals base name),some scope⟩ := by
  simp [started,prepared,allocatedHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem name_read (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    Reads (started base scope game name callee) (.identifier "pool") (.string name) 3 := by
  apply local_identifier _ _ _ (locals base name) (some scope) (local_environment base scope game name callee) (by rfl)
  simp [readBinding,local_environment,locals,bind,Except.bind,pure,Except.pure]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (5+1+fuel) (prepared base scope game name callee) =
      Builtins.run (1+fuel) (started base scope game name callee) := by
  rw [Nat.add_comm 6 fuel,Nat.add_comm 1 fuel]
  cbv

def emptyTest : Expr := .binary .equal (.identifier "pool") (.literal (.string []))
def normalTest : Expr := .binary .equal (.identifier "pool") (.literal (.string ([110,111,114,109,97,108])))
def test : Expr := .logical .or emptyTest normalTest

theorem true_or (base : Machine) (left right : Expr) (a : Value)
    (ticks : Nat) (read : Reads base left a ticks) (trueValue : truthy a=true) :
    Reads base (.logical .or left right) a (ticks+2) := by
  intro continuation consumer fuel
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression left,continuation:=.logical .or right::continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep _) =_
  simp [Builtins.builtinStep,step,internalStep,consumeValue,trueValue,pushExpression,result]

theorem test_empty (state : Machine)
    (read : Reads state (.identifier "pool") (.string []) 3) :
    Reads state test (.boolean true) 9 := by
  have equal := string_equal state (.identifier "pool") (.literal (.string [])) [] [] 3 1 read
    (literal state (.string []))
  exact true_or state emptyTest normalTest (.boolean true) 7 equal rfl

theorem test_nonempty (state : Machine) (pool : JSString) (nonempty : pool≠[])
    (read : Reads state (.identifier "pool") (.string pool) 3) :
    Reads state test (.boolean (decide (pool=[110,111,114,109,97,108]))) 17 := by
  have left := string_equal state (.identifier "pool") (.literal (.string [])) pool [] 3 1 read
    (literal state (.string []))
  have right := string_equal state (.identifier "pool")
    (.literal (.string ([110,111,114,109,97,108]))) pool ([110,111,114,109,97,108]) 3 1 read
    (literal state (.string ([110,111,114,109,97,108])))
  have leftFalse : Reads state emptyTest (.boolean false) 7 := by simpa only [emptyTest,decide_eq_false nonempty] using left
  exact false_or state emptyTest normalTest (.boolean false)
    (.boolean (decide (pool=[110,111,114,109,97,108]))) 7 7 leftFalse right rfl

def testTicks (pool : JSString) : Nat := if pool=[] then 9 else 17

theorem actual_test (base : Machine) (scope game : ObjectId) (pool : JSString)
    (callee : Option ObjectId := none) :
    Reads (started base scope game pool callee) test
      (.boolean (pool=[] || pool=[110,111,114,109,97,108])) (testTicks pool) := by
  by_cases empty : pool=[]
  · subst pool
    exact test_empty _ (name_read base scope game [] callee)
  · simpa only [testTicks,if_neg empty,decide_eq_false empty,Bool.false_or] using
      test_nonempty _ pool empty (name_read base scope game pool callee)

def afterTest (base : Machine) (scope game : ObjectId) (pool : JSString) (callee : Option ObjectId := none) : Machine := {
  started base scope game pool callee with
  control:=.expressionResult (.value (.boolean (pool=[] || pool=[110,111,114,109,97,108])))
  continuation:=.ifTest (.return (some (.literal (.boolean true))))
    (some (.return (some (.literal (.boolean false)))))::
    .statementList [] none::(started base scope game pool callee).continuation }

theorem body_to_test (base : Machine) (scope game : ObjectId) (pool : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (2+testTicks pool+fuel) (started base scope game pool callee)=
      Builtins.run fuel (afterTest base scope game pool callee) := by
  rw [show 2+testTicks pool+fuel=2+(testTicks pool+fuel) by omega,Nat.add_comm 2 (testTicks pool+fuel)]
  change Builtins.run (testTicks pool+fuel) {started base scope game pool callee with
    control:=.expression test
    continuation:=.ifTest (.return (some (.literal (.boolean true))))
      (some (.return (some (.literal (.boolean false)))))::
      .statementList [] none::(started base scope game pool callee).continuation}=_
  exact actual_test base scope game pool callee _ (by rfl) fuel

theorem return_boolean (base : Machine) (scope game : ObjectId) (pool : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (6+fuel) (afterTest base scope game pool callee)=
      Builtins.run fuel (returned base scope pool callee) := by
  rw [Nat.add_comm 6 fuel]
  unfold afterTest returned
  generalize h : (decide (pool=[]) || decide (pool=[110,111,114,109,97,108]))=value
  cases value <;> cbv

theorem actual_prepared (base : Machine) (scope game : ObjectId) (pool : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (testTicks pool+13+fuel) (prepared base scope game pool callee)=
      Builtins.run fuel (returned base scope pool callee) := by
  rw [show testTicks pool+13+fuel=5+1+(testTicks pool+7+fuel) by omega,actual_hoist (callee:=callee)]
  rw [show 1+(testTicks pool+7+fuel)=2+testTicks pool+(6+fuel) by omega,
    body_to_test (callee:=callee),return_boolean (callee:=callee)]

theorem source_call (base : Machine) (scope game function : ObjectId)
    (argument : Expr) (pool : JSString) (argumentTicks : Nat) (source : Option JSString)
    (gameObject functionObject : JSObject)
    (gamePresent : checkedObject base.heap game=.ok gameObject) (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "CountsAsAchievementOwned")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (closure scope source))
    (callerGame : Reads base (.identifier "Game") (.object game) 3)
    (readArgument : Reads base argument (.string pool) argumentTicks) (fuel : Nat) :
    Builtins.run (argumentTicks+testTicks pool+24+fuel) {base with
      control:=.expression (MemberCall.expression "CountsAsAchievementOwned" argument)}=
      Builtins.run fuel (returned base scope pool (some function)) := by
  rw [show argumentTicks+testTicks pool+24+fuel=argumentTicks+10+(1+(testTicks pool+13+fuel)) by omega,
    MemberCall.source_invoke base "CountsAsAchievementOwned" argument (.string pool)
      game function gameObject argumentTicks gamePresent gameKind method callerGame readArgument,
    Nat.add_comm 1 (testTicks pool+13+fuel)]
  change Builtins.run (testTicks pool+13+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string pool] false}
    (.object function) (.object game) [.string pool] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string pool] false}
      (.object function) (.object game) [.string pool] false=
      prepared base scope game pool (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,actual_prepare]
    rfl
  rw [invoked]
  exact actual_prepared base scope game pool (some function) fuel

theorem returned_extends (base : Machine) (scope : EnvId) (pool : JSString)
    (callee : Option ObjectId := none) : HeapExtension.Extends base.heap (returned base scope pool callee).heap := by
  exact HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base pool callee))
    (HeapExtension.same_objects rfl)

theorem returned_heap (base : Machine) (scope : EnvId) (pool : JSString)
    (callee : Option ObjectId := none) :
    (returned base scope pool callee).heap.objects=base.heap.objects.push (argumentObject base pool callee) ∧
    (returned base scope pool callee).heap.environments=
      base.heap.environments.push ⟨.declarative (locals base pool),some scope⟩ := ⟨rfl,rfl⟩

theorem returned_result (base : Machine) (scope : EnvId) (pool : JSString)
    (callee : Option ObjectId := none) :
    (returned base scope pool callee).control=
      .expressionResult (.value (.boolean (pool=[] || pool=JSString.ofString "normal"))) := by
  have normal : JSString.ofString "normal"=[110,111,114,109,97,108] := by decide +kernel
  rw [normal]
  rfl

end CookieClicker.JavaScript.AchievementCountCall

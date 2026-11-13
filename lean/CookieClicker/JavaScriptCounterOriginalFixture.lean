import CookieClicker.JavaScriptCounterOriginalMember
import CookieClicker.JavaScriptCounterOriginalPreservation

/-! A symbolic layout witnesses that the original-frame premises can hold.
Game is object 3, Window object 1, and the caller and closure use different
lexical environments. This is a constructed fixture, not a runtime capture. -/
namespace CookieClicker.JavaScript.CounterOriginalFixture
open CounterOriginalInvocation CounterOriginalCall CounterOriginalMember
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def functionObject (op : Operation) : JSObject := {kind:=.function (closure op 2 none)}
def windowObject : JSObject := {
  properties:=[⟨JSString.ofString "Game",.data (.object 3) true true false⟩] }
def gameObject (op : Operation) (cookies earned : UInt64) : JSObject := {
  properties:=[⟨JSString.ofString "cookies",.data (.number cookies) true true true⟩,
    ⟨JSString.ofString "cookiesEarned",.data (.number earned) true true true⟩,
    ⟨JSString.ofString (methodName op),.data (.object 4) true true true⟩,
    ⟨JSString.ofString "sentry",.data (.boolean true) false true false⟩] }

def frame (op : Operation) (cookies earned : UInt64) : CounterObjects.Frame cookies earned := {
  objects:=#[{},windowObject,{},gameObject op cookies earned,functionObject op]
  game:=3
  window:=1
  gameObject:=gameObject op cookies earned
  windowObject:=windowObject
  distinct:=by decide
  gameRead:=rfl
  windowRead:=rfl
  gameKind:=rfl
  windowKind:=Or.inl rfl
  gameKnown:=rfl
  windowKnown:=rfl
  gameBinding:=rfl
  cookiesOwn:=rfl
  earnedOwn:=rfl }

def callerBindings : List Binding := [{name:="callerSentry",value:=.boolean true}]
def closureBindings : List Binding := [{name:="closureSentry",value:=.boolean false}]
def originalEnvironments : Array LexicalEnvironment := #[
  ⟨.object 1 false,none⟩,
  ⟨.declarative callerBindings,some 0⟩,
  ⟨.declarative closureBindings,some 0⟩]

def scopes (op : Operation) (cookies earned : UInt64) : HasEnvironment.Scopes (frame op cookies earned).window := {
  environments:=originalEnvironments
  closureScope:=2
  globalScope:=0
  depth:=1
  chain:=HasEnvironment.DeclarativePath.next 2 0 0 0 closureBindings rfl (by decide) (.done 0)
  globalRead:=rfl
  depthBound:=by decide }

def machine (base : Machine) (op : Operation) (cookies earned : UInt64) : Machine := {
  base with
  heap:=⟨(frame op cookies earned).objects,originalEnvironments⟩
  context:=⟨1,1,.object 1,false⟩
  globalObject:=1
  objectEnvironmentExclusions:=[] }

theorem actual_member_call (base : Machine) (op : Operation) (cookies earned amount : UInt64) (fuel : Nat) :
    Builtins.run (preparedSteps op+12+fuel)
      {machine base op cookies earned with
        control:=.expression
          (.call (.member (.identifier "Game") (.identifier (methodName op)) false) [.literal (.number amount)])}=
      Builtins.run fuel (returned (machine base op cookies earned) op (frame op cookies earned)
        (scopes op cookies earned) amount (some 4)) := by
  have chain : HasEnvironment.DeclarativePath (machine base op cookies earned).heap.environments
      "Game" (machine base op cookies earned).context.lexicalEnvironment 0 1 :=
    HasEnvironment.DeclarativePath.next 1 0 0 0 callerBindings rfl (by decide) (.done 0)
  have method : ownProperty (frame op cookies earned).gameObject (JSString.ofString (methodName op))=
      some (.data (.object 4) true true true) := by cases op <;> rfl
  conv => lhs; arg 1; rw [show preparedSteps op+12+fuel=3+1+preparedSteps op+8+fuel by omega]
  exact actual_game_member_call (machine base op cookies earned) op (frame op cookies earned)
    (scopes op cookies earned) (.literal (.number amount)) amount 1
    (SourceRead.literal _ (.number amount)) rfl rfl rfl rfl 0 1 chain (by change 1≤3; decide) rfl
    4 none (functionObject op) rfl rfl method fuel

end CookieClicker.JavaScript.CounterOriginalFixture

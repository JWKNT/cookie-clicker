import CookieClicker.JavaScriptAuraRead
import CookieClicker.JavaScriptAuraSource

/-! The complete native auraMult body for the two empty aura selectors. -/
namespace CookieClicker.JavaScript.AuraBody
open SourceRead AuraLocals AuraRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem reads_update (base : Machine) (control : Control) (continuation : List Frame)
    (expression : Expr) (value : Value) (ticks : Nat) (read : Reads base expression value ticks) :
    Reads {base with control,continuation} expression value ticks := read

def firstState (base : Machine) : Machine := {base with
  control:=.statement firstBranch
  continuation:=.statementList [secondBranch,.return (some (.identifier "n"))] none::base.continuation}
def secondState (base : Machine) : Machine := {base with
  control:=.statement secondBranch
  continuation:=.statementList [.return (some (.identifier "n"))] none::base.continuation}
def returnState (base : Machine) : Machine := {base with
  control:=.statement (.return (some (.identifier "n")))
  continuation:=.statementList [] none::base.continuation}

theorem native_suffix (base : Machine) (first : Reads base firstTest (.boolean false) 61)
    (second : Reads base (.logical .and realityTest levelTest) (.boolean false) 59)
    (localN : Reads base (.identifier "n") (.number 0) 3) (fuel : Nat) :
    Builtins.run (133+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.statementList body.tail none::base.continuation}=
      Builtins.run fuel {base with control:=.completion (.return (.number 0))} := by
  rw [show 133+fuel=1+(63+(1+(61+(1+(5+(1+fuel)))))) by omega,
    Nat.add_comm 1 (63+(1+(61+(1+(5+(1+fuel))))))]
  change Builtins.run (63+(1+(61+(1+(5+(1+fuel)))))) (firstState base)=_
  change Builtins.run (61+2+(1+(61+(1+(5+(1+fuel))))))
    {firstState base with control:=.statement (.ifThenElse firstTest
      (.expression (.assignment .assign (.identifier "n") (.literal (.number Number.one)))) none)}=_
  rw [false_branch (firstState base) firstTest
    (.expression (.assignment .assign (.identifier "n") (.literal (.number Number.one))))
    (.boolean false) 61 first rfl,
    Nat.add_comm 1 (61+(1+(5+(1+fuel))))]
  change Builtins.run (61+(1+(5+(1+fuel)))) (secondState base)=_
  change Builtins.run (59+2+(1+(5+(1+fuel))))
    {secondState base with control:=.statement (.ifThenElse (.logical .and realityTest levelTest)
      (.expression (.assignment .add (.identifier "n") (.literal (.number 4591870180066957722)))) none)}=_
  rw [false_branch (secondState base) (.logical .and realityTest levelTest)
    (.expression (.assignment .add (.identifier "n") (.literal (.number 4591870180066957722))))
    (.boolean false) 59 second rfl,Nat.add_comm 1 (5+(1+fuel))]
  change Builtins.run (5+(1+fuel)) (returnState base)=_
  change Builtins.run (3+2+(1+fuel)) {returnState base with
    control:=.statement (.return (some (.identifier "n")))}=_
  rw [return_read (returnState base) (.identifier "n") (.number 0) 3 localN,
    Nat.add_comm 1 fuel]
  rfl

theorem native_body (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) (what : JSString) (parameter : values.what=.string what)
    (other : noAura ≠ what)
    (world : World (start base objects leading outer {values with n:=.number 0} suffix))
    (game : Reads (start base objects leading outer {values with n:=.number 0} suffix)
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (139+fuel) (start base objects leading outer values suffix)=
      Builtins.run fuel {start base objects leading outer {values with n:=.number 0} suffix with
        control:=.completion (.return (.number 0))} := by
  rw [show 139+fuel=6+(133+fuel) by omega,
    actual_initial_n_prefix base objects leading outer values suffix]
  apply native_suffix (start base objects leading outer {values with n:=.number 0} suffix)
  · apply first_test _ world what other game
    simpa only [parameter] using local_what base objects leading outer {values with n:=.number 0} suffix
  · exact second_test _ world game
  · exact local_n base objects leading outer {values with n:=.number 0} suffix

end CookieClicker.JavaScript.AuraBody

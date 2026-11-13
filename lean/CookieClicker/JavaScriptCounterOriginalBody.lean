import CookieClicker.JavaScriptCounterOriginalEnvironment

/-! Both native counter bodies run against one retained heap. The second Earn
write uses the frame produced by the first write. -/
namespace CookieClicker.JavaScript.CounterOriginalBody
open CounterOriginalEnvironment CounterObjects
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def compound (operator : AssignmentOp) (name : String) : Stmt :=
  .expression (.assignment operator (.member (.identifier "Game") (.identifier name) false)
    (.identifier "howmuch"))

theorem add_cookies {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) (fuel : Nat) :
    Builtins.run (17+fuel) {ambient base frame scopes amount arguments with control:=.statement (compound .add "cookies")}=
      Builtins.run fuel {ambient base (writeCookies frame (Number.add cookies amount)) scopes amount arguments with
        control:=.completion (.normal (some (.number (Number.add cookies amount))))} := by
  let start:=ambient base frame scopes amount arguments
  change Builtins.run (17+fuel) {start with control:=.statement (compound .add "cookies")}=_
  conv => lhs; arg 1; rw [show 17+fuel=10+(3+(4+fuel)) by omega]
  have firstPart:=PropertyCompound.dot_prefix start (.identifier "Game") (.identifier "howmuch")
    frame.game "cookies" .add (by decide) (.number cookies) frame.gameObject 3
    (read_game base frame scopes amount arguments) (checked_game frame _) frame.gameKind (cookies_lookup frame _) (3+(4+fuel))
  refine firstPart.trans ?_
  have rhs:=read_amount base frame scopes amount arguments
  refine (rhs _ (by rfl) (4+fuel)).trans ?_
  exact PropertyCompound.dot_suffix start frame.game "cookies" .add .add rfl frame.gameObject
    (.number cookies) (.number amount) (.number (Number.add cookies amount)) rfl rfl (by decide) rfl
    frame.gameRead frame.gameKind frame.cookiesOwn (cookies_lookup frame _) fuel

theorem sub_cookies {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) (fuel : Nat) :
    Builtins.run (17+fuel) {ambient base frame scopes amount arguments with control:=.statement (compound .subtract "cookies")}=
      Builtins.run fuel {ambient base (writeCookies frame (Number.sub cookies amount)) scopes amount arguments with
        control:=.completion (.normal (some (.number (Number.sub cookies amount))))} := by
  let start:=ambient base frame scopes amount arguments
  change Builtins.run (17+fuel) {start with control:=.statement (compound .subtract "cookies")}=_
  conv => lhs; arg 1; rw [show 17+fuel=10+(3+(4+fuel)) by omega]
  have firstPart:=PropertyCompound.dot_prefix start (.identifier "Game") (.identifier "howmuch")
    frame.game "cookies" .subtract (by decide) (.number cookies) frame.gameObject 3
    (read_game base frame scopes amount arguments) (checked_game frame _) frame.gameKind (cookies_lookup frame _) (3+(4+fuel))
  refine firstPart.trans ?_
  have rhs:=read_amount base frame scopes amount arguments
  refine (rhs _ (by rfl) (4+fuel)).trans ?_
  exact PropertyCompound.dot_suffix start frame.game "cookies" .subtract .subtract rfl frame.gameObject
    (.number cookies) (.number amount) (.number (Number.sub cookies amount)) rfl rfl (by decide) rfl
    frame.gameRead frame.gameKind frame.cookiesOwn (cookies_lookup frame _) fuel

theorem add_earned {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) (fuel : Nat) :
    Builtins.run (17+fuel) {ambient base frame scopes amount arguments with control:=.statement (compound .add "cookiesEarned")}=
      Builtins.run fuel {ambient base (writeEarned frame (Number.add earned amount)) scopes amount arguments with
        control:=.completion (.normal (some (.number (Number.add earned amount))))} := by
  let start:=ambient base frame scopes amount arguments
  change Builtins.run (17+fuel) {start with control:=.statement (compound .add "cookiesEarned")}=_
  conv => lhs; arg 1; rw [show 17+fuel=10+(3+(4+fuel)) by omega]
  have firstPart:=PropertyCompound.dot_prefix start (.identifier "Game") (.identifier "howmuch")
    frame.game "cookiesEarned" .add (by decide) (.number earned) frame.gameObject 3
    (read_game base frame scopes amount arguments) (checked_game frame _) frame.gameKind (earned_lookup frame _) (3+(4+fuel))
  refine firstPart.trans ?_
  have rhs:=read_amount base frame scopes amount arguments
  refine (rhs _ (by rfl) (4+fuel)).trans ?_
  exact PropertyCompound.dot_suffix start frame.game "cookiesEarned" .add .add rfl frame.gameObject
    (.number earned) (.number amount) (.number (Number.add earned amount)) rfl rfl (by decide) rfl
    frame.gameRead frame.gameKind frame.earnedOwn (earned_lookup frame _) fuel

def earnedFrame {cookies earned : UInt64} (frame : CounterObjects.Frame cookies earned) (amount : UInt64) :=
  writeEarned (writeCookies frame (Number.add cookies amount)) (Number.add earned amount)

def spentFrame {cookies earned : UInt64} (frame : CounterObjects.Frame cookies earned) (amount : UInt64) :=
  writeCookies frame (Number.sub cookies amount)

def earnCompleted {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) : Machine := {
  ambient base (earnedFrame frame amount) scopes amount arguments with
  control:=.completion (.normal (some (.number (Number.add earned amount)))) }

def spendCompleted {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) : Machine := {
  ambient base (spentFrame frame amount) scopes amount arguments with
  control:=.completion (.normal (some (.number (Number.sub cookies amount)))) }

theorem actual_earn {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) (fuel : Nat) :
    Builtins.run (37+fuel) {ambient base frame scopes amount arguments with control:=.statement CounterSyntax.earnBody}=
      Builtins.run fuel (earnCompleted base frame scopes amount arguments) := by
  conv => lhs; arg 1; rw [show 37+fuel=(17+(1+(17+(1+fuel))))+1 by omega]
  change Builtins.run (17+(1+(17+(1+fuel))))
    {ambient {base with continuation:=.statementList [compound .add "cookiesEarned"] none::base.continuation}
      frame scopes amount arguments with control:=.statement (compound .add "cookies")}=_
  refine (add_cookies {base with continuation:=.statementList [compound .add "cookiesEarned"] none::base.continuation}
    frame scopes amount arguments (1+(17+(1+fuel)))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (17+(1+fuel))]
  change Builtins.run (17+(1+fuel))
    {ambient {base with continuation:=.statementList [] (some (.number (Number.add cookies amount)))::base.continuation}
      (writeCookies frame (Number.add cookies amount)) scopes amount arguments with
      control:=.statement (compound .add "cookiesEarned")}=_
  refine (add_earned {base with continuation:=.statementList [] (some (.number (Number.add cookies amount)))::base.continuation}
    (writeCookies frame (Number.add cookies amount)) scopes amount arguments (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

theorem actual_spend {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (arguments : ObjectId) (fuel : Nat) :
    Builtins.run (19+fuel) {ambient base frame scopes amount arguments with control:=.statement CounterSyntax.spendBody}=
      Builtins.run fuel (spendCompleted base frame scopes amount arguments) := by
  conv => lhs; arg 1; rw [show 19+fuel=(17+(1+fuel))+1 by omega]
  change Builtins.run (17+(1+fuel))
    {ambient {base with continuation:=.statementList [] none::base.continuation}
      frame scopes amount arguments with control:=.statement (compound .subtract "cookies")}=_
  refine (sub_cookies {base with continuation:=.statementList [] none::base.continuation}
    frame scopes amount arguments (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.CounterOriginalBody

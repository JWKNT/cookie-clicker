import CookieClicker.JavaScriptNotifySource
import CookieClicker.JavaScriptNotifyLocals
import CookieClicker.JavaScriptReadCombinators

/-! Notification entry when the native fast-notes preference is zero.
The original replacement, constructor and log statements remain pending. -/
namespace CookieClicker.JavaScript.NotifyHeader
open NotifyLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def condition : Expr := .member (.member (.identifier "Game") (.identifier "prefs") false)
  (.identifier "notifs") false

def consequent : Stmt := match NotifySource.body.headD .empty with
  | .ifThenElse _ yes _ => yes
  | other => other

theorem source_head : NotifySource.body=.ifThenElse condition consequent none::NotifySource.body.tail := rfl

theorem skipped (base : Machine) (notifs : Reads base condition (.number 0) 11) (fuel : Nat) :
    Builtins.run (14+fuel) {base with control:=.statement NotificationSyntax.NotifyBody}=
      Builtins.run fuel {base with
        control:=.completion (.normal none)
        continuation:=.statementList NotifySource.body.tail none::base.continuation} := by
  rw [show 14+fuel=1+(13+fuel) by omega,Nat.add_comm 1 (13+fuel)]
  change Builtins.run (11+2+fuel) {base with
    control:=.statement (.ifThenElse condition consequent none)
    continuation:=.statementList NotifySource.body.tail none::base.continuation}=_
  exact false_branch {base with continuation:=.statementList NotifySource.body.tail none::base.continuation} condition consequent (.number 0) 11 notifs rfl fuel

theorem preference_read (base : Machine) (game prefs : ObjectId) (gameObject prefsObject : JSObject)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (gamePresent : checkedObject base.heap game=.ok gameObject) (gameKind : gameObject.kind=.ordinary)
    (prefsProperty : lookupProperty base.heap game (JSString.ofString "prefs")=
      .ok (some (.data (.object prefs) true true true)))
    (prefsPresent : checkedObject base.heap prefs=.ok prefsObject) (prefsKind : prefsObject.kind=.ordinary)
    (notifsProperty : lookupProperty base.heap prefs (JSString.ofString "notifs")=
      .ok (some (.data (.number 0) true true true))) :
    Reads base condition (.number 0) 11 := by
  apply dot base _ prefs "notifs" (.number 0) prefsObject 7
    (dot base _ game "prefs" (.object prefs) gameObject 3 gameRead gamePresent (Or.inl gameKind) prefsProperty)
    prefsPresent (Or.inl prefsKind) notifsProperty

def initialValues (base : Machine) (title desc pic : Value) : Values := {
  title,desc,pic,arguments:=.object (NotifySource.argumentIndex base) }

theorem actual_state (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none) :
    start (NotifySource.hoisted base scope game title desc pic callee)
      (base.heap.objects.push (NotifySource.argumentObject base title desc pic callee))
      base.heap.environments scope (initialValues base title desc pic) #[]=
      {NotifySource.hoisted base scope game title desc pic callee with
        control:=.statement NotificationSyntax.NotifyBody} := by
  simp [start,heap,bindings,slotIndex,initialValues,NotifySource.hoisted,NotifySource.prepared,
    NotifySource.allocatedHeap,NotifySource.locals,NotifySource.localIndex]

theorem prepared_skipped (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none)
    (notifs : Reads (NotifySource.hoisted base scope game title desc pic callee) condition (.number 0) 11)
    (fuel : Nat) :
    Builtins.run (26+fuel) (NotifySource.prepared base scope game title desc pic callee)=
      Builtins.run fuel {NotifySource.hoisted base scope game title desc pic callee with
        control:=.completion (.normal none)
        continuation:=.statementList NotifySource.body.tail none::
          (NotifySource.hoisted base scope game title desc pic callee).continuation} := by
  rw [show 26+fuel=12+(14+fuel) by omega,NotifySource.actual_hoist base scope game title desc pic callee]
  have entry : Builtins.run (14+fuel) (NotifySource.hoisted base scope game title desc pic callee)=
      Builtins.run (14+fuel) {NotifySource.hoisted base scope game title desc pic callee with
        control:=.statement NotificationSyntax.NotifyBody} := by
    rw [Nat.add_comm 14 fuel]
    change Builtins.run (fuel+13)
      (Builtins.builtinStep (NotifySource.hoisted base scope game title desc pic callee))=
      Builtins.run (fuel+13) (Builtins.builtinStep
        {NotifySource.hoisted base scope game title desc pic callee with control:=.statement NotificationSyntax.NotifyBody})
    rw [NotifySource.hoisted_starts_body base scope game title desc pic callee]
  exact entry.trans (skipped _ notifs fuel)

end CookieClicker.JavaScript.NotifyHeader

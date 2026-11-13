import CookieClicker.JavaScriptAudioCall
import CookieClicker.JavaScriptGlobalCall

/-! Full native global call expressions for muted PlaySound. Argument reads
are exact source reads, and function lookup retains the global receiver rule. -/
namespace CookieClicker.JavaScript.AudioExpression
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem default_volume (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window)
    (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (AudioInvocation.closure scopes.closureScope source))
    (callee : GlobalCall.Callee base "PlaySound" function)
    (argument : Expr) (ticks : Nat) (read : SourceRead.Reads base argument url ticks) (fuel : Nat) :
    Builtins.run (ticks+105+fuel)
      {base with control:=.expression (.call (.identifier "PlaySound") [argument])}=
      Builtins.run fuel (AudioCall.returned base frame scopes url none (some function)) := by
  rw [show ticks+105+fuel=ticks+6+(99+fuel) by omega,
    GlobalCall.source_one base "PlaySound" function callee argument url ticks read]
  exact AudioCall.actual_source_call base frame scopes url none objects environments global exclusions
    function source object present kind fuel

theorem provided_volume (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (volume : AudioMuted.Volume)
    (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window)
    (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (AudioInvocation.closure scopes.closureScope source))
    (callee : GlobalCall.Callee base "PlaySound" function)
    (argument volumeArgument : Expr) (ticks volumeTicks : Nat)
    (read : SourceRead.Reads base argument url ticks)
    (readVolume : SourceRead.Reads base volumeArgument (.number volume.bits) volumeTicks) (fuel : Nat) :
    Builtins.run (ticks+volumeTicks+116+fuel)
      {base with control:=.expression (.call (.identifier "PlaySound") [argument,volumeArgument])}=
      Builtins.run fuel (AudioCall.returned base frame scopes url (some volume) (some function)) := by
  rw [show ticks+volumeTicks+116+fuel=ticks+volumeTicks+7+(109+fuel) by omega,
    GlobalCall.source_two base "PlaySound" function callee argument volumeArgument url (.number volume.bits)
      ticks volumeTicks read readVolume]
  exact AudioCall.actual_source_call base frame scopes url (some volume) objects environments global exclusions
    function source object present kind fuel

end CookieClicker.JavaScript.AudioExpression

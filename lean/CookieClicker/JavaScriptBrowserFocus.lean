import CookieClicker.JavaScriptBrowserLayout
import CookieClicker.JavaScriptBrowserEvents
import CookieClicker.JavaScriptBrowserInput
import CookieClicker.JavaScriptBrowserDocument
import CookieClicker.JavaScriptBrowserTextSelection

/-! Synchronous focus procedures for the supported single-document box model.
Native focus/blur callbacks run through the ordinary event/source machine. CSS
focusability, editable selection, scrolling and mutation lifecycle requirements
are explicit; this does not supply trusted pointer targeting or keyboard input.
-/
namespace CookieClicker.JavaScript.BrowserFocus

open Browser
open BrowserFocusState (Transition)
private def key := JSString.ofString
private def argument := Builtins.argument
private def missing (message : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("Focus: " ++ message)))

/-- HTML signed-integer parsing, with the native signed32 representable range.
Trailing non-digits are allowed; an empty digit sequence is not an integer. -/
def htmlInteger (source : JSString) : Option Int := do
  let text := source.dropWhile (fun unit => [9,10,12,13,32].contains unit.toNat)
  let negative := text.head? == some 45
  let text := if negative || text.head? == some 43 then text.drop 1 else text
  let digits := text.takeWhile (fun unit => 48 ≤ unit.toNat && unit.toNat ≤ 57)
  if digits.isEmpty then none else
    let magnitude : Nat := digits.foldl (fun value unit => value*10+unit.toNat-48) 0
    let value := if negative then -(magnitude : Int) else magnitude
    if value < -2147483648 || value > 2147483647 then none else some value

private def tabindexDefault (node : Node) : Checked Int :=
  match node.kind with
  | .element tag =>
    if ["a","area","button","frame","iframe","input","object","select","textarea"].contains tag then pure 0
    else if tag == "summary" then missing "summary/details default tab index"
    else pure (-1)
  | _ => .error (.exception "TypeError" "HTMLElement required")

def focusedElement (state : State) : Checked (Option Nat) := do
  match state.focus.element with
  | none => pure none
  | some id =>
    if ← connectedToDocument state (state.nodes.size+1) id then pure (some id)
    else missing "focused node detached without native blur/removal lifecycle"

def activeElement (state : State) : Checked Value := do
  match ← focusedElement state with
  | some id => nodeValue state (some id)
  | none =>
    nodeValue state (← BrowserDocument.htmlChild state state.document
      (fun tag => tag == "body" || tag == "frameset"))

private def checkAncestors : Nat → State → Nat → Checked Unit
  | 0,_,_ => .error (.fault (.invalidContinuation "Cyclic focus ancestry"))
  | fuel+1,state,id => do
    let node ← checkedNode state id
    if (getAttribute node "contenteditable").isSome then missing "editable focus and selection"
    if (getAttribute node "inert").isSome then missing "native inert subtree configuration"
    if node.kind == .element "fieldset" && (getAttribute node "disabled").isSome then
      missing "disabled fieldset and first-legend focus rule"
    match node.parent with
    | some parent => checkAncestors fuel state parent
    | none => pure ()

private def focusable (state : State) (id : Nat) : Checked Bool := do
  if !(← connectedToDocument state (state.nodes.size+1) id) then pure false else
  checkAncestors (state.nodes.size+1) state id
  let node ← checkedNode state id
  let .element tag := node.kind | .error (.exception "TypeError" "HTMLElement required")
  if ["textarea","button"].contains tag && (getAttribute node "disabled").isSome then return false
  if state.focus.spatialNavigationEnabled || state.focus.keyboardFocusableScrollers then
    missing "nondefault spatial navigation or keyboard-focusable scrollers"
  -- For these ordinary elements, SupportsFocus is false without a valid
  -- explicit tabindex or editable root. The native style/layout update cannot
  -- turn this conjunction true. Shadow creation and custom-element lifecycle
  -- are unresolved elsewhere; the selected engine disables spatial focus and
  -- the experimental KeyboardFocusableScrollers feature.
  if ["div","span"].contains tag && ((getAttribute node "tabindex").bind htmlInteger).isNone &&
      (← BrowserLayout.readOnlyEditing state id) then return false
  if tag == "textarea" then return ← BrowserLayout.textareaFocusStyle state id
  if !(← BrowserLayout.focusStyle state id) then pure false else
  if ["input","textarea","select","iframe","frame","object","embed","summary"].contains tag then
    missing "editable or embedded native focusability and selection"
  else if tag == "button" && (getAttribute node "disabled").isSome then pure false
  else pure (((getAttribute node "tabindex").bind htmlInteger).isSome ||
    (tag == "a" && (getAttribute node "href").isSome) || tag == "button")

private def requestAdvance (state : State) : State :=
  { state with machine := { state.machine with control := .resumeBuiltin {
    id := ⟨"Browser.Focus","advance"⟩,phase := "advance",thisValue := .undefined } .undefined } }

private def finish (state : State) : State :=
  Browser.result { state with focus := { state.focus with transitions := state.focus.transitions.drop 1 } } .undefined

private def update (state : State) (transition : Transition) : State :=
  { state with focus := { state.focus with transitions := transition :: state.focus.transitions.drop 1 } }

private def send (state : State) (target : Nat) (related : Option Nat) (name : String) (bubbles : Bool) : State :=
  Browser.checked state (nodeValue state (some target)) fun receiver =>
  Browser.checked state (nodeValue state related) fun relatedTarget =>
  Browser.checked state (BrowserInput.allocate state "FocusEvent" (key name)
    (.focus { ui := { view := .object state.machine.globalObject },relatedTarget }) bubbles false true true)
    fun (event,next) =>
      let continuation : BuiltinContinuation := {
        id := ⟨"Browser.Focus","advance"⟩,phase := "advance",thisValue := .undefined }
      BrowserEvents.dispatchEvent { next with machine := { next.machine with
        continuation := .builtin continuation :: next.machine.continuation } } receiver [event] true

def advance (state : State) : State :=
  match state.focus.transitions with
  | [] => Browser.fail state (.fault (.invalidContinuation "Missing focus procedure"))
  | transition :: _ =>
    Browser.checked state (match state.focus.pageFocused with
      | some value => pure value
      | none => missing "page focus environment is unconfigured") fun pageFocused =>
    Browser.checked state (focusedElement state) fun current =>
      if transition.phase == 0 then
        let state := update state { transition with phase := 1 }
        match transition.oldTarget with
        | some old => if pageFocused then send state old transition.newTarget "blur" false else requestAdvance state
        | none => requestAdvance state
      else if transition.phase == 1 then
        let transition := if current.isSome then { transition with newTarget := none,blocked := true } else transition
        let state := update state { transition with phase := 2 }
        match transition.oldTarget with
        | some old => if pageFocused then send state old transition.newTarget "focusout" true else requestAdvance state
        | none => requestAdvance state
      else if transition.phase == 2 then
        let state := update state { transition with phase := 3 }
        match transition.oldTarget with
        | some old => if pageFocused then send state old transition.newTarget "DOMFocusOut" true else requestAdvance state
        | none => requestAdvance state
      else if transition.phase == 3 then
        let transition := if current.isSome then { transition with newTarget := none,blocked := true } else transition
        match transition.newTarget with
        | none => finish state
        | some target => Browser.checked state (focusable state target) fun allowed =>
          if !allowed then finish state
          else if !transition.preventScroll then Browser.fail state
            (.unresolved (.unsupportedSyntax "Focus: native scroll-into-view appearance"))
          else
            let state := update { state with focus := { state.focus with element := some target } }
              { transition with phase := 4 }
            Browser.checked state (do
              let node ← checkedNode state target
              if node.kind == .element "textarea" && !transition.selectionNone then
                BrowserTextSelection.restore state target
              else pure state) fun state =>
                if pageFocused then send state target transition.oldTarget "focus" false else finish state
      else if transition.phase == 4 || transition.phase == 5 then
        if current != transition.newTarget then finish state else
        match transition.newTarget with
        | none => finish state
        | some target => send (update state { transition with phase := transition.phase+1 })
          target transition.oldTarget (if transition.phase == 4 then "focusin" else "DOMFocusIn") true
      else if transition.phase == 6 then finish state
      else Browser.fail state (.fault (.invalidContinuation "Invalid focus procedure phase"))

private def begin (state : State) (target : Option Nat) (preventScroll : Bool)
    (selectionNone : Bool := false) : State :=
  Browser.checked state (focusedElement state) fun old =>
    if old == target then Browser.result state .undefined
    else Browser.checked state (match state.focus.pageFocused with
      | some value => pure value | none => missing "page focus environment is unconfigured") fun _ =>
      requestAdvance { state with focus := { state.focus with
        element := none,transitions := { oldTarget := old,newTarget := target,preventScroll,selectionNone } :: state.focus.transitions } }

private def focusCall (state : State) (receiver : Value) (preventScroll : Bool)
    (selectionNone : Bool := false) : State :=
  Browser.checked state (receiverNode state receiver) fun (id,_) =>
  Browser.checked state (focusedElement state) fun old =>
    if old == some id then Browser.result state .undefined
    else Browser.checked state (focusable state id) fun allowed =>
      if !allowed then Browser.result state .undefined
      else if !preventScroll then Browser.fail state
        (.unresolved (.unsupportedSyntax "Focus: native scroll-into-view appearance"))
      else begin state (some id) preventScroll selectionNone

/-- TextControlElement::select uses SelectionBehaviorOnFocus::kNone. Its
textarea appearance hook returns before selection restoration and scrolling;
select itself restores the cache after all synchronous focus callbacks. -/
def focusForSelection (state : State) (receiver : Value) : State :=
  focusCall state receiver true true

private def call (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Native focus member is not a constructor")
  else Browser.checked state (nodeBrand state builtin.namespaceName receiver) fun _ =>
  Browser.checked state (receiverNode state receiver) fun (id,node) =>
    if builtin.name == "get activeElement" then Browser.checked state (activeElement state) (Browser.result state)
    else if builtin.name == "hasFocus" then
      match state.focus.pageFocused with
      | some value => Browser.result state (.boolean value)
      | none => Browser.fail state (.unresolved (.unsupportedSyntax "Focus: page focus environment is unconfigured"))
    else if builtin.name == "get tabIndex" then
      Browser.checked state (tabindexDefault node) fun fallback =>
        Browser.result state (.number (Number.ofInt (((getAttribute node "tabindex").bind htmlInteger).getD fallback)))
    else if builtin.name == "set tabIndex" then
      match Browser.convertArguments state ⟨"Browser.Focus","tabIndex"⟩ receiver arguments false [(0,"number")] with
      | some next => next
      | none => Browser.checked state (toNumber (argument arguments 0)) fun bits =>
        Browser.checked state (setNodeAttribute state id "tabindex" (key (toString (Number.toInt32 bits))))
          fun next => Browser.result next .undefined
    else if builtin.name == "blur" then
      Browser.checked state (focusedElement state) fun old =>
        if old == some id then begin state none true else Browser.result state .undefined
    else
      let options := argument arguments 0
      if options == .undefined || options == .null then focusCall state receiver false
      else if !isObject options then Browser.fail state (.exception "TypeError" "Focus options must be an object")
      else
        let continuation : BuiltinContinuation := {
          id := ⟨"Browser.Focus","focus"⟩,phase := "option",thisValue := receiver }
        { state with machine := readProperty { state.machine with
          continuation := .builtin continuation :: state.machine.continuation } options (key "preventScroll") }

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "advance" then advance state
  else if continuation.phase == "option" then focusCall state continuation.thisValue (truthy value)
  else if continuation.phase == "convert" && continuation.id.name == "tabIndex" then
    Browser.checked state (Browser.convertedArgument continuation value) fun value =>
      call state ⟨"Browser.HTMLElement","set tabIndex"⟩ continuation.thisValue [value] false
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if (["Browser.HTMLElement","Browser.Element"].contains builtin.namespaceName &&
        ["focus","blur","get tabIndex","set tabIndex"].contains builtin.name) ||
      (["Browser.Document","Browser.HTMLDocument"].contains builtin.namespaceName &&
        ["get activeElement","hasFocus"].contains builtin.name) then
      some (call state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Focus" then some (resume state continuation value) else none
  | _ => none

end CookieClicker.JavaScript.BrowserFocus

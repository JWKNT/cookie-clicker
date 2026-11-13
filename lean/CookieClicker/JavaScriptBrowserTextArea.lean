import CookieClicker.JavaScriptBrowserDocument
import CookieClicker.JavaScriptBrowserAnimation
import CookieClicker.JavaScriptBrowserFocus
import CookieClicker.JavaScriptBrowserTextSelection

/-! Native textarea value/reflection backed by parsed DOM children and the
dirty-value flag. Focus, editing and selection-event scheduling remain explicit.
-/
namespace CookieClicker.JavaScript.BrowserTextArea

open Browser
private def key := JSString.ofString

private def receiver (state : State) (value : Value) : Checked (Nat × Node) := do
  let (id,node) ← receiverNode state value
  if node.kind == .element "textarea" then pure (id,node)
  else .error (.exception "TypeError" "HTMLTextAreaElement receiver required")

private abbrev setRange := BrowserTextSelection.setRange

private def direction (text : JSString) : TextControl.Direction :=
  if text == key "forward" then .forward else if text == key "backward" then .backward else .none

private def call (state : State) (builtin : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) : State :=
  if construct then Browser.fail state (.exception "TypeError" "Textarea member is not a constructor")
  else Browser.checked state (receiver state thisValue) fun (id,node) =>
  let name := (builtin.name.drop 4).toString
  if builtin.name == "select" then
    Browser.checked state (setRange state id 0 4294967295 .none) fun state =>
      let continuation : BuiltinContinuation := {
        id := ⟨"Browser.TextAreaSelection","restore"⟩,phase := "restore",thisValue }
      BrowserFocus.focusForSelection {state with machine := {state.machine with
        continuation := .builtin continuation :: state.machine.continuation}} thisValue
  else if builtin.name == "setSelectionRange" then
    if arguments.length < 2 then Browser.fail state (.exception "TypeError" "setSelectionRange requires two arguments")
    else match Browser.convertArguments state builtin thisValue arguments false [(0,"number"),(1,"number"),(2,"string")] with
    | some next => next
    | none =>
      Browser.checked state (toNumber (Builtins.argument arguments 0)) fun start =>
      Browser.checked state (toNumber (Builtins.argument arguments 1)) fun finish =>
      Browser.checked state (toJSString (Builtins.argument arguments 2)) fun text =>
      Browser.checked state (setRange state id (Number.toUInt32 start).toNat (Number.toUInt32 finish).toNat (direction text))
        fun next => Browser.result next .undefined
  else if builtin.name.startsWith "get " then
    if name == "value" then Browser.result state (.string node.textarea.value)
    else if name == "defaultValue" then
      Browser.checked state (BrowserDocument.childText state id) fun text => Browser.result state (.string text)
    else if name == "textLength" then Browser.result state (.number (Number.ofNat node.textarea.value.length))
    else if ["readOnly","disabled","required"].contains name then
      Browser.result state (.boolean ((getAttribute node name.toLower).isSome))
    else if ["selectionStart","selectionEnd","selectionDirection"].contains name then
      Browser.checked state (BrowserTextSelection.range state id) fun (start,finish,direction) =>
        if name == "selectionStart" then Browser.result state (.number (Number.ofNat start))
        else if name == "selectionEnd" then Browser.result state (.number (Number.ofNat finish))
        else Browser.result state (.string (key (match direction with
          | .none => "none" | .forward => "forward" | .backward => "backward")))
    else state
  else if builtin.name.startsWith "set " then
    let value := Builtins.argument arguments 0
    if ["readOnly","disabled","required"].contains name then
      Browser.checked state (if truthy value then setNodeAttribute state id name.toLower []
        else replaceNode state id {node with attributes := node.attributes.filter (·.name != name.toLower)})
        fun next => Browser.result next .undefined
    else if name == "value" || name == "defaultValue" then
      match Browser.convertArguments state builtin thisValue arguments false [(0,"string")] with
      | some next => next
      | none =>
        Browser.checked state (if name == "value" && value == .null then pure [] else toJSString value) fun text =>
          if name == "defaultValue" then Browser.setter state "textContent" thisValue (.string text)
          else if TextControl.normalize text != node.textarea.value &&
              (state.focus.element == some id || state.textSelection.current.any (·.owner == id)) then
            Browser.fail state (.unresolved (.unsupportedSyntax "Textarea value mutation of represented FrameSelection requires native editor adjustment"))
          else Browser.checked state (replaceNode state id
            {node with textarea := TextControl.setValue node.textarea text}) fun next =>
              Browser.result next .undefined
    else if ["selectionStart","selectionEnd","selectionDirection"].contains name then
      match Browser.convertArguments state builtin thisValue arguments false
          [(0,if name == "selectionDirection" then "string" else "number")] with
      | some next => next
      | none =>
        let range : Checked (Nat × Nat × TextControl.Direction) := do
          let (start,finish,direction) ← BrowserTextSelection.range state id
          if name == "selectionDirection" then
            pure (start,finish,BrowserTextArea.direction (← toJSString value))
          else
            let index := (Number.toUInt32 (← toNumber value)).toNat
            if name == "selectionStart" then pure (index,max index finish,direction)
            else pure (min index start,index,direction)
        Browser.checked state range fun (start,finish,direction) =>
          Browser.checked state (setRange state id start finish direction) fun next => Browser.result next .undefined
    else state
  else state

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin thisValue arguments construct) =>
    if builtin.namespaceName == "Browser.HTMLTextAreaElement" &&
        ["get value","set value","get defaultValue","set defaultValue","get textLength",
         "get readOnly","set readOnly","get disabled","set disabled","get required","set required",
         "get selectionStart","get selectionEnd","get selectionDirection","set selectionStart",
         "set selectionEnd","set selectionDirection","setSelectionRange","select"].contains builtin.name then
      some (call state builtin thisValue arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.HTMLTextAreaElement" && continuation.phase == "convert" then
      some (Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
        call state continuation.id continuation.thisValue
          (continuation.arguments.set (continuation.indices[0]?.getD 0) converted) false)
    else if continuation.id.namespaceName == "Browser.TextAreaSelection" && continuation.phase == "restore" then
      some (Browser.checked state (receiver state continuation.thisValue) fun (id,node) =>
        Browser.checked state (setRange state id node.textarea.start node.textarea.finish node.textarea.direction)
          fun next => Browser.result next .undefined)
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserTextArea

import Lean
import CookieClicker.JavaScriptCursorDomFrame
import CookieClicker.JavaScriptBrowserStyle
import CookieClicker.JavaScriptBrowserTokenList

/-! Frames for actual CSS/classList host procedures. Private aliases name the
existing definitions; they do not supply replacement implementations. Every
statement is checked against those definitions by the Lean kernel. -/
open Lean in
macro "nativeStyleStore" : term => pure (mkIdent
  (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserStyle 0)
    `CookieClicker.JavaScript.BrowserStyle.storeDeclaration))
open Lean in
macro "nativeTokenUpdate" : term => pure (mkIdent
  (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserTokenList 0)
    `CookieClicker.JavaScript.BrowserTokenList.update))

open Lean in
macro "styleNative%" name:str : term => pure (mkIdent
  (Name.str (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserStyle 0)
    `CookieClicker.JavaScript.BrowserStyle) name.getString))

open Lean in
macro "tokenNative%" name:str : term => pure (mkIdent
  (Name.str (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserTokenList 0)
    `CookieClicker.JavaScript.BrowserTokenList) name.getString))

open Lean in
macro "unfold_style" name:str : tactic => do
  let id := mkIdent (Name.str (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserStyle 0)
    `CookieClicker.JavaScript.BrowserStyle) name.getString)
  `(tactic| unfold $id:ident)
open Lean in
macro "unfold_token" name:str : tactic => do
  let id := mkIdent (Name.str (Name.append (Name.num `_private.CookieClicker.JavaScriptBrowserTokenList 0)
    `CookieClicker.JavaScript.BrowserTokenList) name.getString)
  `(tactic| unfold $id:ident)

namespace CookieClicker.JavaScript.CursorStyleFrame
open Browser
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Preserves (before after : State) : Prop where
  heap : HeapExtension.Extends before.machine.heap after.machine.heap
  environments : after.machine.heap.environments=before.machine.heap.environments
  elapsed : after.machine.elapsed=before.machine.elapsed
  draws : after.machine.freeDrawCount=before.machine.freeDrawCount

theorem Preserves.refl (state : State) : Preserves state state :=
  ⟨HeapExtension.refl _,rfl,rfl,rfl⟩

theorem Preserves.trans {a b c : State} (left : Preserves a b) (right : Preserves b c) : Preserves a c :=
  ⟨HeapExtension.trans left.heap right.heap,right.environments.trans left.environments,
    right.elapsed.trans left.elapsed,right.draws.trans left.draws⟩

theorem same_machine {before after : State} (same : after.machine=before.machine) : Preserves before after := by
  constructor
  · rw [congrArg Machine.heap same]; exact HeapExtension.refl _
  · rw [congrArg Machine.heap same]
  · exact congrArg Machine.elapsed same
  · exact congrArg Machine.freeDrawCount same

theorem result_preserves (state : State) (value : Value) : Preserves state (Browser.result state value) :=
  ⟨HeapExtension.refl _,rfl,rfl,rfl⟩

theorem fail_preserves (state : State) (failure : EvalFailure) : Preserves state (Browser.fail state failure) := by
  cases failure with
  | fault value => exact ⟨HeapExtension.refl _,rfl,rfl,rfl⟩
  | unresolved value => exact ⟨HeapExtension.refl _,rfl,rfl,rfl⟩
  | exception name message => exact ⟨HeapExtension.append_object _ _,rfl,rfl,rfl⟩

theorem checked_preserves {α : Type} (state : State) (value : Checked α) (next : α → State)
    (framed : ∀ value, Preserves state (next value)) :
    Preserves state (Browser.checked state value next) := by
  cases value with
  | error failure => exact fail_preserves state failure
  | ok value => exact framed value

abbrev styleStore := nativeStyleStore
abbrev tokenUpdate := nativeTokenUpdate

theorem style_store_machine (before after : State) (id : Nat) (entries : BrowserStyle.Declaration)
    (ran : styleStore before id entries=.ok after) : after.machine=before.machine := by
  change (do
    let node ← checkedNode before id
    let text ← BrowserStyle.serialize entries
    let text := JSString.ofString text
    replaceNode before id { setAttribute node "style" text with
      styleCache := some (text,entries.map fun (p : BrowserStyle.Property) => (p.name,p.value,p.important)) })=.ok after at ran
  cases got : checkedNode before id with
  | error failure => simp [got,Except.bind,bind] at ran
  | ok node =>
    simp only [got,Except.bind,bind] at ran
    cases serialized : BrowserStyle.serialize entries with
    | error failure => simp [serialized,Except.bind,bind] at ran
    | ok text =>
      simp only [serialized,Except.bind,bind] at ran
      exact CursorDomFrame.replace_node_machine before after id _ ran

theorem token_update_machine (before after : State) (id : Nat) (values : List JSString)
    (ran : tokenUpdate before id values=.ok after) : after.machine=before.machine := by
  change (do
    let node ← checkedNode before id
    let joined := values.foldl (fun (text token : JSString) => if text.isEmpty then token else text ++ [32] ++ token) []
    replaceNode before id (setAttribute node "class" joined))=.ok after at ran
  cases got : checkedNode before id with
  | error failure => simp [got,Except.bind,bind] at ran
  | ok node =>
    simp only [got,Except.bind,bind] at ran
    exact CursorDomFrame.replace_node_machine before after id _ ran

theorem style_store_preserves (before after : State) (id : Nat) (entries : BrowserStyle.Declaration)
    (ran : styleStore before id entries=.ok after) : Preserves before after :=
  same_machine (style_store_machine before after id entries ran)

theorem token_update_preserves (before after : State) (id : Nat) (values : List JSString)
    (ran : tokenUpdate before id values=.ok after) : Preserves before after :=
  same_machine (token_update_machine before after id values ran)


 theorem checked_successful {α : Type} (state : State) (value : Checked α) (next : α → State)
    (framed : ∀ output, value=.ok output → Preserves state (next output)) :
    Preserves state (Browser.checked state value next) := by
  cases h : value with
  | error failure => exact fail_preserves state failure
  | ok output => exact framed output h

/-- This is the intact commit tail of native CSS property assignment. Invalid
or unsupported values retain their actual failure. Successful writes retain
the serialized declaration and native-value cache. -/
def putTail (state : State) (id : Nat) (property text : String) (resultValue : Value) : State :=
  Browser.checked state (BrowserStyle.readDeclaration state id) fun entries =>
    Browser.checked state (BrowserStyle.set entries property text false) fun changed =>
      let next := if changed == entries then pure state else styleStore state id changed
      Browser.checked state next fun next => Browser.result next resultValue

theorem put_tail_preserves (state : State) (id : Nat) (property text : String) (resultValue : Value) :
    Preserves state (putTail state id property text resultValue) := by
  unfold putTail
  apply checked_preserves
  intro entries
  apply checked_preserves
  intro changed
  apply checked_successful
  intro next ran
  split at ran
  · cases ran; exact result_preserves _ _
  · exact (style_store_preserves state next id changed ran).trans (result_preserves next resultValue)

private theorem checked_ok {α : Type} (state : State) (value : α) (next : α → State) :
    Browser.checked state (.ok value) next=next value := rfl

 theorem display_assignment_preserves (state : State) (styleId nodeId : Nat)
    (object : JSObject) (present : checkedObject state.machine.heap styleId=.ok object)
    (kind : object.kind=.host "DOM.Style" nodeId) (text : JSString) :
    Preserves state (BrowserStyle.dispatch state ⟨"Browser.Style","put:display"⟩
      (.object styleId) [.string text,.string text] false) := by
  have receiver : (styleNative% "styleId") state (.object styleId)=.ok nodeId := by
    change (do
      match (← checkedObject state.machine.heap styleId).kind with
      | .host "DOM.Style" id => pure id
      | _ => .error (.exception "TypeError" "CSS declaration method called on incompatible receiver"))=.ok nodeId
    simp [present,kind,Except.bind,bind,Except.pure,pure]
  have lower : "".toLower="" := by decide +kernel
  simp only [BrowserStyle.dispatch,Id.run,receiver]
  simp [Browser.convertArguments,isObject,toJSString,Builtins.argument,checked_ok,Except.pure,pure]
  apply checked_preserves
  intro converted
  have property : ("put:display".drop 4).copy="display" := by decide +kernel
  simpa [putTail,BrowserStyle.readDeclaration,styleStore,lower,property,Except.pure,pure] using
    put_tail_preserves state nodeId "display" converted (.string text)
 theorem background_position_assignment_preserves (state : State) (styleId nodeId : Nat)
    (object : JSObject) (present : checkedObject state.machine.heap styleId=.ok object)
    (kind : object.kind=.host "DOM.Style" nodeId) (text : JSString) :
    Preserves state (BrowserStyle.dispatch state ⟨"Browser.Style","put:background-position"⟩
      (.object styleId) [.string text,.string text] false) := by
  have receiver : (styleNative% "styleId") state (.object styleId)=.ok nodeId := by
    change (do
      match (← checkedObject state.machine.heap styleId).kind with
      | .host "DOM.Style" id => pure id
      | _ => .error (.exception "TypeError" "CSS declaration method called on incompatible receiver"))=.ok nodeId
    simp [present,kind,Except.bind,bind,Except.pure,pure]
  have lower : "".toLower="" := by decide +kernel
  simp only [BrowserStyle.dispatch,Id.run,receiver]
  simp [Browser.convertArguments,isObject,toJSString,Builtins.argument,checked_ok,Except.pure,pure]
  apply checked_preserves
  intro converted
  have property : ("put:background-position".drop 4).copy="background-position" := by decide +kernel
  simpa [putTail,BrowserStyle.readDeclaration,styleStore,lower,property,Except.pure,pure] using
    put_tail_preserves state nodeId "background-position" converted (.string text)


 theorem class_remove_preserves (state : State) (listId nodeId : Nat)
    (object : JSObject) (node : Node)
    (present : checkedObject state.machine.heap listId=.ok object)
    (kind : object.kind=.host "DOM.TokenList" nodeId)
    (nodePresent : checkedNode state nodeId=.ok node) (text : JSString) :
    Preserves state (BrowserTokenList.dispatch state ⟨"Browser.TokenList","remove"⟩
      (.object listId) [.string text] false) := by
  have receiver : (tokenNative% "receiverId") state (.object listId)=.ok nodeId := by
    change (do
      let .host "DOM.TokenList" id := (← checkedObject state.machine.heap listId).kind |
        .error (.exception "TypeError" "DOMTokenList receiver required")
      let _ ← checkedNode state id
      pure id)=.ok nodeId
    simp [present,kind,nodePresent,Except.bind,bind,Except.pure,pure]
  simp only [BrowserTokenList.dispatch,Id.run,receiver]
  simp [Browser.convertArguments,isObject,toJSString,Builtins.argument,checked_ok,Except.pure,pure]
  apply checked_preserves
  intro oldText
  apply checked_preserves
  intro supplied
  apply checked_preserves
  intro validated
  apply checked_preserves
  intro currentNode
  split
  · exact result_preserves _ _
  · apply checked_successful
    intro next updated
    exact (token_update_preserves state next nodeId _ updated).trans (result_preserves _ _)


 theorem cached_style_get (state : State) (receiver : Value) (id object : Nat)
    (node : Node) (tag : String)
    (present : receiverNode state receiver=.ok (id,node))
    (kind : node.kind=.element tag) (cached : node.styleObject=some object) :
    (styleNative% "getStyle") state receiver=Browser.result state (.object object) := by
  unfold_style "getStyle"
  simp [present,Browser.checked,kind,cached]

 theorem cached_class_list_get (state : State) (receiver : Value) (id object : Nat)
    (node : Node) (tag : String)
    (present : receiverNode state receiver=.ok (id,node))
    (kind : node.kind=.element tag) (cached : node.classListObject=some object) :
    (tokenNative% "getList") state receiver=Browser.result state (.object object) := by
  unfold_token "getList"
  simp [present,Browser.checked,kind,cached]

end CookieClicker.JavaScript.CursorStyleFrame

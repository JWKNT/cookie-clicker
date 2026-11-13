import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptHeapExtension

/-! Frames for the actual DOM procedures reached by Cursor.rebuild. These
statements preserve all allocation and tree updates. They do not replace DOM
operations with no-ops or establish admission of an arbitrary DOM request. -/
namespace CookieClicker.JavaScript.CursorDomFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
open Browser

private theorem foldlM_observation {α β γ : Type} (observe : α → γ)
    (step : α → β → Checked α)
    (preserves : ∀ before item after, step before item=.ok after → observe after=observe before)
    (items : List β) (before after : α)
    (ran : items.foldlM step before=.ok after) : observe after=observe before := by
  induction items generalizing before with
  | nil =>
    change Except.ok before = Except.ok after at ran
    cases ran
    rfl
  | cons item rest ih =>
    cases first : step before item with
    | error failure => simp [List.foldlM_cons,first,Except.bind,bind,Except.pure,pure] at ran
    | ok intermediate =>
      have tail : rest.foldlM step intermediate=.ok after := by simpa [List.foldlM_cons,first,Except.bind,bind,Except.pure,pure] using ran
      exact (ih intermediate tail).trans (preserves before item intermediate first)

-- This body is definitionally equal to the private native helper. The change
-- below checks that equality; no callback result is supplied as a premise.
private def refreshNative (state : State) (id : Nat) : Checked State := do
  let node ← checkedNode state id
  if node.kind != .element "textarea" || node.textarea.dirty then pure state else
  let text ← node.children.foldlM (fun text child => do
    let child ← checkedNode state child
    pure (text ++ (match child.kind with | .text value => value | _ => []))) []
  let next := {node with textarea := TextControl.childrenChanged node.textarea text}
  pure {state with nodes := state.nodes.set! id next}

private theorem refresh_textarea_machine (before after : State) (id : Nat)
    (ran : refreshNative before id=.ok after) : after.machine=before.machine := by
  unfold refreshNative at ran
  cases got : checkedNode before id with
  | error failure => simp [got,Except.bind,bind] at ran
  | ok node =>
    simp only [got,Except.bind,bind] at ran
    split at ran
    · cases ran; rfl
    · generalize folded : List.foldlM (m := Checked) _ ([] : JSString) node.children = output at ran
      cases output with
      | error failure => simp [Except.bind,bind] at ran
      | ok text => cases ran; rfl

theorem replace_node_machine (before after : State) (id : Nat) (node : Node)
    (ran : replaceNode before id node=.ok after) : after.machine=before.machine := by
  unfold replaceNode at ran
  cases got : checkedNode before id with
  | error failure => simp [got,Except.bind,bind,Except.map,Functor.map,Except.pure,pure] at ran
  | ok old =>
    simp only [got,Except.bind,bind] at ran
    split at ran
    · contradiction
    · split at ran
      · contradiction
      · have framed := foldlM_observation State.machine refreshNative (fun before id after ran => refresh_textarea_machine before after id ran) _ _ _ ran
        exact framed

theorem replace_children_machine (before after : State) (id : Nat) (children : List Nat)
    (ran : replaceChildren before id children=.ok after) : after.machine=before.machine := by
  unfold replaceChildren at ran
  cases got : checkedNode before id with
  | error failure => simp [got,Except.bind,bind,Except.map,Functor.map,Except.pure,pure] at ran
  | ok node =>
    simp only [got,Except.bind,bind] at ran
    generalize firstEq : List.foldlM (m := Checked) _ before node.children = first at ran
    cases first with
    | error failure => simp [Except.bind,bind] at ran
    | ok intermediate =>
      have firstFrame : intermediate.machine=before.machine := by
        apply foldlM_observation State.machine _ _ node.children before intermediate firstEq
        intro old child next stepRan
        cases childGot : checkedNode old child with
        | error failure => simp [childGot,Except.bind,bind,Except.map,Functor.map] at stepRan
        | ok childNode =>
          simp only [childGot,Except.bind,bind] at stepRan
          exact replace_node_machine old next _ _ stepRan
      simp only [Except.bind,bind] at ran
      cases parentEq : replaceNode intermediate id {node with children} with
      | error failure => simp [parentEq,Except.bind,bind] at ran
      | ok parentState =>
        have parentFrame := replace_node_machine intermediate parentState id _ parentEq
        simp only [parentEq,Except.bind,bind] at ran
        have finalFrame : after.machine=parentState.machine := by
          apply foldlM_observation State.machine _ _ children parentState after ran
          intro old child next stepRan
          cases childGot : checkedNode old child with
          | error failure => simp [childGot,Except.bind,bind,Except.map,Functor.map] at stepRan
          | ok childNode =>
            simp only [childGot,Except.bind,bind] at stepRan
            exact replace_node_machine old next _ _ stepRan
        exact finalFrame.trans (parentFrame.trans firstFrame)

structure Extends (before after : State) : Prop where
  machine : after.machine={before.machine with heap:=after.machine.heap}
  heap : HeapExtension.Extends before.machine.heap after.machine.heap
  environments : after.machine.heap.environments=before.machine.heap.environments

 theorem Extends.refl (state : State) : Extends state state := ⟨rfl,HeapExtension.refl _,rfl⟩
 theorem Extends.trans {a b c : State} (left : Extends a b) (right : Extends b c) : Extends a c := by
  constructor
  · rw [right.machine,left.machine]
  · exact HeapExtension.trans left.heap right.heap
  · exact right.environments.trans left.environments

 theorem same_machine {before after : State} (same : after.machine=before.machine) : Extends before after := by
  constructor
  · simp [same]
  · rw [same]; exact HeapExtension.refl _
  · rw [same]

 theorem allocate_node_extends (before after : State) (kind : NodeKind) (id : Nat)
    (ran : allocateNode before kind=.ok (id,after)) : Extends before after := by
  unfold allocateNode at ran
  cases proto : nodePrototype before.prototypes kind with
  | error failure => simp [proto,Except.bind,bind,Except.map,Functor.map,Except.pure,pure] at ran
  | ok prototype =>
    simp only [proto,Except.bind,bind] at ran
    cases ran
    exact ⟨rfl,HeapExtension.append_object _ _,rfl⟩

 theorem replaced_lookup (before after : State) (id : Nat) (node : Node)
    (ran : replaceNode before id node=.ok after) (object : ObjectId) (name : JSString) :
    lookupProperty after.machine.heap object name=lookupProperty before.machine.heap object name := by
  rw [replace_node_machine before after id node ran]


/-- A plain text allocation retains all earlier heap objects and environments.
The allocated text object remains in the result, even if a later refresh
replaces the DOM child that refers to it. -/
theorem allocate_plain_text_extends (before after : State) (text : JSString)
    (ids : List Nat) (fuel : Nat)
    (ran : allocateParsed before (fuel+1) [.text text]=.ok (ids,after)) :
    Extends before after := by
  simp only [allocateParsed] at ran
  cases allocation : allocateNode before (.text text) with
  | error failure => simp [allocation,Except.bind,bind] at ran
  | ok pair =>
    rcases pair with ⟨id,next⟩
    simp only [allocation,Except.bind,bind] at ran
    have frame := allocate_node_extends before next _ id allocation
    cases fuel <;> simp only [allocateParsed,Except.bind,bind,Except.pure,pure] at ran <;>
      cases ran <;> exact frame

theorem cursor_fragment : DomSyntax.parseFragment "div" (JSString.ofString "Cursor")=
    .ok [.text (JSString.ofString "Cursor")] := by rfl

/-- The actual fixed-English Cursor name refresh preserves every previous
JavaScript object. This is a frame theorem on the native handler; success and
the expected product element are explicit premises, not guessed DOM results. -/
theorem cursor_innerHTML_extends (before after : State) (id : Nat) (node : Node)
    (present : checkedNode before id=.ok node) (kind : node.kind=.element "div")
    (ran : setInnerHTML before id (JSString.ofString "Cursor")=.ok after) :
    Extends before after := by
  simp only [setInnerHTML,present,Except.bind,bind,kind,cursor_fragment] at ran
  cases parsed : allocateParsed before ((JSString.ofString "Cursor").length+2)
      [.text (JSString.ofString "Cursor")] with
  | error failure => simp [parsed,Except.bind,bind] at ran
  | ok pair =>
    rcases pair with ⟨children,next⟩
    simp only [parsed,Except.bind,bind] at ran
    have allocation := allocate_plain_text_extends before next _ children
      ((JSString.ofString "Cursor").length+1) parsed
    exact allocation.trans (same_machine (replace_children_machine next after id children ran))

/-- All successful old-object property reads survive the native Cursor name
refresh. Failed or unknown reads are deliberately not promoted to facts. -/
theorem cursor_innerHTML_lookup (before after : State) (id : Nat) (node : Node)
    (present : checkedNode before id=.ok node) (kind : node.kind=.element "div")
    (ran : setInnerHTML before id (JSString.ofString "Cursor")=.ok after)
    (object : ObjectId) (name : JSString) (descriptor : Option PropertyDescriptor)
    (read : lookupProperty before.machine.heap object name=.ok descriptor) :
    lookupProperty after.machine.heap object name=.ok descriptor :=
  HeapExtension.lookup_property (cursor_innerHTML_extends before after id node present kind ran).heap
    object name descriptor read


/-- The checked subprocedure used by the actual textContent setter for an
Element. The defining equality in `text_content_setter` retains the native
conversion and receiver checks. -/
def textChildren (before : State) (text : JSString) : Checked (List Nat × State) := do
  if text.isEmpty then pure ([],before) else
    let (child,next) ← allocateNode before (.text text)
    pure ([child],next)

def textContentWrite (before : State) (id : Nat) (text : JSString) : Checked State := do
  let (children,next) ← textChildren before text
  replaceChildren next id children

theorem text_children_extends (before after : State) (text : JSString) (ids : List Nat)
    (ran : textChildren before text=.ok (ids,after)) : Extends before after := by
  unfold textChildren at ran
  split at ran
  · cases ran; exact Extends.refl _
  · cases allocation : allocateNode before (.text text) with
    | error failure => simp [allocation,Except.bind,bind] at ran
    | ok pair =>
      rcases pair with ⟨id,next⟩
      simp only [allocation,Except.bind,bind,Except.pure,pure] at ran
      have frame := allocate_node_extends before next _ id allocation
      cases ran
      exact frame

theorem text_content_write_extends (before after : State) (id : Nat) (text : JSString)
    (ran : textContentWrite before id text=.ok after) : Extends before after := by
  unfold textContentWrite at ran
  cases children : textChildren before text with
  | error failure => simp [children,Except.bind,bind] at ran
  | ok pair =>
    rcases pair with ⟨ids,next⟩
    simp only [children,Except.bind,bind] at ran
    exact (text_children_extends before next text ids children).trans
      (same_machine (replace_children_machine next after id ids ran))

theorem text_content_setter (before after : State) (receiver : Value) (id : Nat)
    (node : Node) (tag : String) (text : JSString)
    (present : receiverNode before receiver=.ok (id,node))
    (kind : node.kind=.element tag)
    (ran : textContentWrite before id text=.ok after) :
    setter before "textContent" receiver (.string text)=Browser.result after .undefined := by
  unfold textContentWrite at ran
  cases children : textChildren before text with
  | error failure => simp [children,Except.bind,bind] at ran
  | ok pair =>
    rcases pair with ⟨ids,next⟩
    simp only [children,Except.bind,bind] at ran
    have childExpr : (if text.isEmpty then pure ([],before) else do
        let (child,next) ← allocateNode before (.text text)
        pure ([child],next) : Checked (List Nat × State))=.ok (ids,next) := children
    cases text with
    | nil =>
      simp [textChildren] at children
      obtain ⟨rfl,rfl⟩ := children
      simp [setter,present,Browser.checked,kind,toJSString,ran,Except.pure,pure]
    | cons unit rest =>
      cases allocated : allocateNode before (.text (unit::rest)) with
      | error failure => simp [textChildren,allocated,Except.bind,bind] at children
      | ok pair =>
        rcases pair with ⟨child,allocatedState⟩
        simp [textChildren,allocated,Except.bind,bind,Except.pure,pure] at children
        obtain ⟨rfl,rfl⟩ := children
        simp [setter,present,Browser.checked,kind,toJSString,allocated,ran,Except.bind,bind,Except.pure,pure]


/-- A successful element textContent setter retains the complete original
heap graph and its lexical environments. It changes only the DOM, newly
allocated text objects, and the source-visible undefined return. -/
theorem text_content_native_frame (before after : State) (receiver : Value) (id : Nat)
    (node : Node) (tag : String) (text : JSString)
    (present : receiverNode before receiver=.ok (id,node))
    (kind : node.kind=.element tag)
    (ran : textContentWrite before id text=.ok after) :
    HeapExtension.Extends before.machine.heap
      (setter before "textContent" receiver (.string text)).machine.heap ∧
    (setter before "textContent" receiver (.string text)).machine.heap.environments=
      before.machine.heap.environments := by
  rw [text_content_setter before after receiver id node tag text present kind ran]
  exact ⟨(text_content_write_extends before after id text ran).heap,
    (text_content_write_extends before after id text ran).environments⟩

end CookieClicker.JavaScript.CursorDomFrame

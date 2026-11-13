import CookieClicker.JavaScriptEscapeInput
import CookieClicker.JavaScriptEscapeSyntax
import CookieClicker.JavaScriptEscapeReduction
import CookieClicker.JavaScriptEscapeSpan

namespace CookieClicker.JavaScript.EscapePath
open Browser BrowserInputState
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 8000000
attribute [local cbv_opaque] EscapeSyntax.keyUpText
def key := JSString.ofString
def property (name : String) (value : Value) : OwnProperty :=
  ⟨key name,.data value true true true⟩
def body : List Stmt := match EscapeSyntax.keyUpBody with | .block body => body | _ => []
def closure : FunctionClosure := ⟨none,["e"],body,0,false,some EscapeSyntax.keyUpText⟩
def device : EscapeInput.Device := {
  escapeHeld := true,routingToPage := true,javascriptKeysEnabled := true,capabilities := 10 }
def documentNode : Node := {object:=4,kind:=.document,children:=[1]}
def htmlNode : Node := {object:=5,kind:=.element "html",parent:=some 0,children:=[2]}
def bodyNode : Node := {object:=6,kind:=.element "body",parent:=some 1}
def nodes : Array Node := #[documentNode,htmlNode,bodyNode]

theorem nodes_0 : nodes[0]? = some documentNode := rfl
theorem nodes_1 : nodes[1]? = some htmlNode := rfl
theorem nodes_2 : nodes[2]? = some bodyNode := rfl
theorem nodes_size : nodes.size = 3 := rfl
theorem document_kind : documentNode.kind = .document := rfl
theorem document_object : documentNode.object = 4 := rfl
theorem document_parent : documentNode.parent = none := rfl
theorem document_children : documentNode.children = [1] := rfl
theorem document_listeners : documentNode.listeners = [] := rfl
theorem document_handlers : documentNode.handlers = [] := rfl
theorem html_kind : htmlNode.kind = .element "html" := rfl
theorem html_object : htmlNode.object = 5 := rfl
theorem html_parent : htmlNode.parent = some 0 := rfl
theorem html_children : htmlNode.children = [2] := rfl
theorem html_listeners : htmlNode.listeners = [] := rfl
theorem html_handlers : htmlNode.handlers = [] := rfl
theorem body_kind : bodyNode.kind = .element "body" := rfl
theorem body_object : bodyNode.object = 6 := rfl
theorem body_parent : bodyNode.parent = some 1 := rfl
theorem body_children : bodyNode.children = [] := rfl
theorem body_listeners : bodyNode.listeners = [] := rfl
theorem body_handlers : bodyNode.handlers = [] := rfl
attribute [local cbv_opaque] nodes documentNode htmlNode bodyNode
attribute [local cbv_eval] nodes_0 nodes_1 nodes_2 nodes_size
attribute [local cbv_eval] document_kind document_object document_parent document_children document_listeners document_handlers
attribute [local cbv_eval] html_kind html_object html_parent html_children html_listeners html_handlers
attribute [local cbv_eval] body_kind body_object body_parent body_children body_listeners body_handlers

/-- Explicit minimal data/prototype frame. It does not assert startup or the
previous physical key-down has established this frame. Source time and duration
values, elapsed time and the untouched source IID input queue are arbitrary. -/
def state (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) : Browser.State := {
  machine := {
    heap := {
      objects := #[
        {kind := .host "Window" 0,properties := [⟨key "Game",.data (.object 1) true true false⟩]},
        {properties := [property "lastActivity" (.number 0),property "time" gameTime,
          property "promptOn" (.number 0),property "AscendTimer" (.number 4607182418800017408),
          property "AscendDuration" duration,property "keys" (.object 2)]},
        {kind := .array,properties := [property "27" (.number 4607182418800017408),
          ⟨key "length",.data (.number 4628574517030027264) true false false⟩]},
        {kind := .function closure},
        {kind := .host "DOM.Node" 0},
        {kind := .host "DOM.Node" 1},
        {kind := .host "DOM.Node" 2},
        {},
        {prototype := some 7,properties := [⟨key "keyCode",.accessor (some 9) none true true⟩]},
        {kind := .builtin ⟨"Browser.KeyboardEvent","get keyCode"⟩,propertiesComplete := false},
        {kind := .host "DOM.InputDeviceCapabilities" 0,prototype := some 11},
        {}]
      environments := #[⟨.object 0 false,none⟩] }
    context := {lexicalEnvironment := 0,variableEnvironment := 0,thisValue := .object 0,strict := false}
    control := .idle
    globalObject := 0
    elapsed }
  prototypes := {
    node:=7
    element:=7
    htmlElement:=7
    document:=7
    canvas:=7
    image:=7
    canvasContext:=7
    tokenList:=7
    nodeList:=7
    collection:=7
    style:=7
    specific := [("#Event",7),("#KeyboardEvent",8),("#InputDeviceCapabilities",11)]}
  nodes := nodes
  focus := {pageFocused:=some true}
  windowListeners := [{eventType:=key "keyup",callback:=.object 3}]
  randomInputs := draws }

def started (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) : Browser.State :=
  match EscapeInput.begin (state gameTime duration elapsed draws) device with
  | .ok started => started.browser
  | .error failure => Browser.fail (state gameTime duration elapsed draws) failure

def output (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) : Browser.State :=
  BrowserRuntime.run 147 (started gameTime duration elapsed draws)

def propertyValue (s : Browser.State) (object : Nat) (name : String) :=
  s.machine.heap.objects[object]?.bind fun object => ownProperty object (key name)

attribute [local cbv_opaque] closure

theorem target_is_body (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) :
    EscapeInput.target (state gameTime duration elapsed draws) = .ok 2 := by rfl

theorem admission (gameTime duration : Value) (elapsed : Rat) (draws : List Nat) :
    EscapeInput.admitted (state gameTime duration elapsed draws) device = .ok () := by rfl


theorem number_ofInt_27 : Number.ofInt 27 = 4628293042053316608 := by decide +kernel
theorem number_ofNat_one : Number.ofNat 1 = 4607182418800017408 := by decide +kernel
theorem number_zero_below_one : Number.lessThan 0 4607182418800017408 = true := by decide +kernel
theorem number_27_equal : Number.equal 4628293042053316608 4628293042053316608 = true := by decide +kernel
theorem number_27_string : toJSString (.number 4628293042053316608) = .ok (key "27") := by rfl

theorem closure_name : closure.name = none := rfl
theorem closure_parameters : closure.parameters = ["e"] := rfl
theorem closure_body : closure.body = body := rfl
theorem closure_scope : closure.scope = 0 := rfl
theorem closure_strict : closure.strict = false := rfl
theorem closure_text : closure.sourceText = some EscapeSyntax.keyUpText := rfl
attribute [local cbv_eval] closure_name closure_parameters closure_body closure_scope closure_strict closure_text
attribute [local cbv_opaque] BrowserRuntime.step BrowserCanvasState.defaults Number.ofNat Number.ofInt
  Number.lessThan Number.equal toJSString
attribute [local cbv_eval] EscapeReduction.step_reduction
attribute [local cbv_eval] number_ofInt_27 number_ofNat_one number_zero_below_one
  number_27_equal number_27_string


end CookieClicker.JavaScript.EscapePath

import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptBrowserAssets
import CookieClicker.JavaScriptBrowserEvents

/-! Explicit zero-latency local resource tasks and source callbacks. Captured
asset metadata is a host input, not a proved decoder. The callback subset below
requires that no listener can observe omitted intermediate loading events.
Unsupported URLs, listener paths, media playback and rendering remain explicit
model-incompleteness requests. This is not full native resource refinement.
-/
namespace CookieClicker.JavaScript.BrowserResources

open Browser

private def key := JSString.ofString

private def unresolved (state : State) (description : String) : State :=
  Browser.fail state (.unresolved (.unsupportedSyntax description))

private def ascii (units : JSString) : Checked String :=
  if units.all (fun u => u.toNat < 128) then
    pure (String.ofList (units.map (fun u => Char.ofNat u.toNat)))
  else .error (.unresolved (.unsupportedSyntax "Non-ASCII resource URL parsing"))

/-- The selected prefix admits the pinned relative resource paths and a
configured exact base prefix. Other URL forms require a URL parser. -/
def resourcePath (state : State) (source : JSString) : Checked String := do
  let text ← ascii source
  let text ← match state.resourceBaseURL with
    | none => pure text
    | some base => do
      let base ← ascii base
      pure (if text.startsWith base then (text.drop base.length).toString else text)
  let path := (text.splitOn "?").head!
  let path := (path.splitOn "#").head!
  if path.startsWith "img/" || path.startsWith "snd/" || path.startsWith "loc/" ||
      ["minigameGarden.js","minigameMarket.js","minigameGrimoire.js","minigamePantheon.js","base64.js","main.js"].contains path then
    if path.contains '\\' || path.contains '%' || path.contains ':' || path.contains ' ' ||
        (path.splitOn "/").any (fun part => part == ".." || part == ".") then
      .error (.unresolved (.unsupportedSyntax "Resource URL needs native normalization"))
    else pure path
  else .error (.unresolved (.unsupportedSyntax ("Resource outside pinned local paths: " ++ path)))

def connected (state : State) (id : Nat) : Checked Bool := do
  pure ((← Browser.subtree state state.document).contains id)

def currentRequest (state : State) (request : ResourceRequest) : Checked Bool := do
  let node ← checkedNode state request.node
  pure (node.lastResourceOrder == some request.order && getAttribute node "src" == some request.source)

def supportedRequest (state : State) (request : ResourceRequest) : Checked Bool := do
  if !(← currentRequest state request) then pure false else
  let node ← checkedNode state request.node
  if request.kind == "script" then
    -- Registration already required connection. Later removal does not undo
    -- the initiated external script load.
    if node.scriptStatus != some .unstarted then pure false else
    let path ← resourcePath state request.source
    if state.scripts.any (fun script => script.1 == path) then pure true
    else .error (.unresolved (.unsupportedSyntax ("Missing pinned script AST: " ++ path)))
  else if request.kind == "img" || request.kind == "audio" then
    if request.kind == "audio" && (!node.mediaPlaybackPristine || (getAttribute node "autoplay").isSome) then
      .error (.unresolved (.unsupportedSyntax "Autoplay resource selection requires native playback admission")) else pure ()
    let path ← resourcePath state request.source
    match BrowserAssets.assets.find? (fun asset => asset.path == path) with
    | none => .error (.unresolved (.unsupportedSyntax ("Missing pinned asset metadata: " ++ path)))
    | some asset => match asset.metadata with
      | .image _ _ =>
        if request.kind == "img" then pure true
        else .error (.unresolved (.unsupportedSyntax "Media element decoding image bytes"))
      | .audio _ _ _ =>
        if request.kind == "audio" then pure true
        else .error (.unresolved (.unsupportedSyntax "Image element decoding media bytes"))
  else .error (.unresolved (.unsupportedSyntax ("Unsupported resource element: " ++ request.kind)))

/-- Request initialization order is retained explicitly in the mathematical
zero-latency queue. No requested resource is silently declared loaded. -/
def prepare (state : State) : Checked State := do
  let tasks ← state.resourceRequests.filterMapM fun request => do
    if ← supportedRequest state request then pure (some (ResourceTask.mk request state.machine.elapsed))
    else pure none
  pure { state with resourceRequests := [], resourceTasks := state.resourceTasks ++ tasks }

abbrev allocateEvent := BrowserEventData.allocateEvent
abbrev eventId := BrowserEventData.eventId
def eventCall (state : State) (name : String) (receiver : Value) (arguments : List Value := []) : State :=
  BrowserEventData.eventCall state name receiver arguments

private def callbackSubset (state : State) (node : Node) (eventType : JSString) : Checked Unit := do
  if node.kind != .element "audio" then pure () else
  let omitted := ["loadstart","durationchange","loadedmetadata","progress","canplay","canplaythrough",
    "suspend","stalled","abort","emptied","waiting"] |>.map key
  let observes := fun (listeners : List Listener) (handlers : List BrowserEventState.Handler) =>
    listeners.any (fun listener => omitted.contains listener.eventType && listener.eventType != eventType) ||
    handlers.any (fun handler => omitted.contains handler.eventType && handler.eventType != eventType && handler.body.isSome)
  if state.nodes.any (fun node => observes node.listeners node.handlers) ||
      observes state.windowListeners state.windowHandlers then
    .error (.unresolved (.unsupportedSyntax "Observable intermediate media-resource event sequence"))
  else pure ()

def beginCallback (state : State) (task : ResourceTask) (eventType : JSString) : State :=
  Browser.checked state (checkedNode state task.request.node) fun node =>
  Browser.checked state (callbackSubset state node eventType) fun _ =>
    BrowserEvents.beginTrusted { state with
      activeResource := some ⟨task,"callback"⟩
      currentTimerNesting := none
      machine := { state.machine with continuation := [] } } (.object node.object) eventType

def fire (state : State) (task : ResourceTask) : State :=
  Browser.checked state (currentRequest state task.request) fun current =>
  if !current then { state with machine := { state.machine with control := .idle } } else
  Browser.checked state (resourcePath state task.request.source) fun path =>
  Browser.checked state (checkedNode state task.request.node) fun node =>
    if task.request.kind == "script" then
      match state.scripts.find? (fun script => script.1 == path) with
      | none => unresolved state ("Missing source script AST: " ++ path)
      | some (_,program) =>
        Browser.checked state (replaceNode state task.request.node { node with scriptStatus := some .started }) fun state =>
        Browser.startProgram { state with activeResource := some ⟨task,"script"⟩, currentTimerNesting := none } program
    else
      match BrowserAssets.assets.find? (fun asset => asset.path == path) with
      | none => unresolved state ("Missing asset metadata: " ++ path)
      | some asset =>
        let (resourceStatus,eventType) := match asset.metadata with
          | .image width height => (ResourceStatus.image task.request.source width height,key "load")
          | .audio duration ready network => (ResourceStatus.audio task.request.source duration ready network,key "loadeddata")
        Browser.checked state (replaceNode state task.request.node { node with resourceStatus }) fun state =>
          beginCallback state task eventType

def finish (state : State) : State :=
  if !Browser.taskFinished state.machine then state else
  match state.activeResource with
  | none => state
  | some active =>
    if active.phase == "script" then
      match status state.machine with
      | .completion (.throw _) => unresolved state "Native script error reporting and Window error event"
      | _ => beginCallback state active.task (key "load")
    else if active.phase == "callback" then
      let exceptions := match status state.machine with
        | .completion (.throw exception) => state.reportedExceptions ++ [exception]
        | _ => state.reportedExceptions
      { state with
        activeResource := none
        reportedExceptions := exceptions
        machine := { state.machine with control := .idle, continuation := [] } }
    else unresolved state "Unknown resource task phase"

def nextTask (state : State) : Option ResourceTask :=
  state.resourceTasks.foldl (fun current task => match current with
    | none => some task
    | some earlier => if task.due < earlier.due ||
        (task.due == earlier.due && task.request.order < earlier.request.order) then some task else some earlier) none

def fireNextTask (state : State) : State :=
  if !Browser.taskFinished state.machine then state else
  let state := finish state
  if !Browser.taskFinished state.machine then state else
  Browser.checked state (prepare state) fun state =>
  match nextTask state with
  | none => state
  | some task =>
    let state := { state with
      resourceTasks := state.resourceTasks.filter (fun next => next.request.order != task.request.order)
      machine := { state.machine with elapsed := max state.machine.elapsed task.due } }
    fire state task

def resolvedSource (state : State) (node : Node) : Checked JSString := do
  match getAttribute node "src" with
  | none => pure []
  | some source =>
    let _ ← resourcePath state source
    let some base := state.resourceBaseURL |
      .error (.unresolved (.unsupportedSyntax "Resource src getter needs an explicit canonical base URL"))
    let text ← ascii source
    if text.contains '%' || text.contains ' ' || text.contains '\\' then
      .error (.unresolved (.unsupportedSyntax "Resource src URL serialization"))
    else if source.take base.length == base then pure source else pure (base ++ source)

def imageGetter (state : State) (name : String) (receiver : Value) : State :=
  Browser.checked state (receiverNode state receiver) fun (id,node) =>
    if node.kind != .element "img" then Browser.fail state (.exception "TypeError" "HTMLImageElement receiver required")
    else if name == "get src" then Browser.checked state (resolvedSource state node) (fun source => Browser.result state (.string source))
    else if name == "get complete" then
      match node.resourceStatus with
      | .pending _ => unresolved state "Image completion state before the selected resource task"
      | _ => Browser.result state (.boolean true)
    else
      let dimensions : Checked (Nat × Nat) := match node.resourceStatus with
        | .image _ width height => pure (width,height)
        | .empty | .failed _ => pure (0,0)
        | _ => .error (.unresolved (.unsupportedSyntax "Intermediate image dimensions before resource completion"))
      Browser.checked state dimensions fun (width,height) =>
        if name == "get naturalWidth" then Browser.result state (.number (Number.ofNat width))
        else if name == "get naturalHeight" then Browser.result state (.number (Number.ofNat height))
        else Browser.checked state (connected state id) fun attached =>
          if attached || (getAttribute node "style").isSome || (getAttribute node "width").isSome || (getAttribute node "height").isSome then
            unresolved state "Rendered or attribute-constrained image dimensions need layout/IDL rules"
          else if name == "get width" then Browser.result state (.number (Number.ofNat width))
          else if name == "get height" then Browser.result state (.number (Number.ofNat height))
          else Browser.fail state (.unresolved (.builtin ⟨"Browser.HTMLImageElement",name⟩ receiver [] false))

def mediaGetter (state : State) (name : String) (receiver : Value) : State :=
  Browser.checked state (receiverNode state receiver) fun (_,node) =>
    if node.kind != .element "audio" then Browser.fail state (.exception "TypeError" "Audio receiver required")
    else if name == "get src" then Browser.checked state (resolvedSource state node) (fun source => Browser.result state (.string source))
    else if name == "get paused" then
      -- Every admitted Audio starts paused. play(), native media controls and
      -- autoplay resource selection remain unresolved, so no successful
      -- modeled operation can silently change this native state.
      if !node.mediaPlaybackPristine || (getAttribute node "autoplay").isSome then
        unresolved state "Media paused state with native autoplay admission"
      else Browser.result state (.boolean true)
    else
      let fields : Checked (UInt64 × Nat × Nat) := match node.resourceStatus with
        | .audio _ duration ready network => pure (duration,ready,network)
        | .empty => pure (Number.nan,0,0)
        | _ => .error (.unresolved (.unsupportedSyntax "Intermediate native media readiness"))
      Browser.checked state fields fun (duration,ready,network) =>
        if name == "get duration" then Browser.result state (.number duration)
        else if name == "get readyState" then Browser.result state (.number (Number.ofNat ready))
        else if name == "get networkState" then Browser.result state (.number (Number.ofNat network))
        else Browser.fail state (.unresolved (.builtin ⟨"Browser.HTMLMediaElement",name⟩ receiver [] false))

def audioConstructor (state : State) (_id : BuiltinId) (receiver : Value) (arguments : List Value) (construct : Bool) : State :=
  let source := Builtins.argument arguments 0
  if isObject source then
    { state with machine := { state.machine with
        control := .toPrimitive source "string"
        continuation := .builtin {
          id := ⟨"Browser.Resources","Audio"⟩, phase := "source", thisValue := receiver
          arguments, indices := [if construct then 1 else 0] } :: state.machine.continuation } }
  else Browser.checked state (if source == .undefined then pure none else some <$> toJSString source) fun source =>
    Browser.checked state (allocateNode state (.element "audio")) fun (created,state) =>
    Browser.checked state (setNodeAttribute state created "preload" (key "auto")) fun state =>
    Browser.checked state (match source with | none => pure state | some source => setNodeAttribute state created "src" source) fun state =>
      Browser.checked state (nodeValue state (some created)) (Browser.result state)

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin id receiver arguments construct) =>
    if id.namespaceName == "Browser.Event" then some (if construct then
      Browser.fail state (.exception "TypeError" "Event method is not a constructor")
      else eventCall state id.name receiver arguments)
    else if id.namespaceName == "Browser.Constructor" && id.name == "Audio" then
      some (audioConstructor state id receiver arguments construct)
    else if id.namespaceName == "Browser.HTMLImageElement" &&
        ["get src","get complete","get naturalWidth","get naturalHeight","get width","get height"].contains id.name && !construct then
      some (imageGetter state id.name receiver)
    else if id.namespaceName == "Browser.HTMLMediaElement" &&
        ["get src","get duration","get readyState","get networkState","get paused"].contains id.name && !construct then
      some (mediaGetter state id.name receiver)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Resources" && continuation.id.name == "Audio" && continuation.phase == "source" then
      some (Browser.checked state (toJSString value) fun text =>
        audioConstructor state ⟨"Browser.Constructor","Audio"⟩ continuation.thisValue
          (.string text :: continuation.arguments.drop 1) (continuation.indices[0]? == some 1))
    else none
  | _ => none

end CookieClicker.JavaScript.BrowserResources

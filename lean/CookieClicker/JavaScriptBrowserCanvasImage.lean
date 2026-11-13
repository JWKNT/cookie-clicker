import CookieClicker.JavaScriptBrowserCanvas
import CookieClicker.JavaScriptBrowserResources
import CookieClicker.JavaScriptBrowserCanvasImageAssets

/-! Isolated drawImage admission and immutable-call representation.
The native overload conversions and recoverable errors are represented before
recording. Rect clipping, response-origin taint and pixels have a conditional
native interpretation; this module does not fabricate them. Video, SVG,
ImageBitmap, offscreen and CSS image sources stay explicit. -/
namespace CookieClicker.JavaScript.BrowserCanvasImage
open Browser
open BrowserCanvasState (ImageArguments ImageSnapshot imageSnapshot)

private def failure (description : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax description))

/-- Union conversion is an interface-brand check, before numeric coercions.
Source dimensions and readiness are deliberately read after those coercions. -/
private def sourceId (state : State) (value : Value) : Checked Nat := do
  let .object object := value |
    .error (.exception "TypeError" "drawImage requires a CanvasImageSource")
  let objectData ← checkedObject state.machine.heap object
  match objectData.kind with
  | .host "DOM.Node" id =>
    let node ← checkedNode state id
    if [.element "canvas",.element "img"].contains node.kind then pure id
    else if [.element "video",.element "image"].contains node.kind then
      failure "drawImage video or SVG source conversion"
    else .error (.exception "TypeError" "drawImage requires a CanvasImageSource")
  | .host _ _ => failure "drawImage native source interface union"
  | _ => .error (.exception "TypeError" "drawImage requires a CanvasImageSource")

private def overloadCount (count : Nat) : Checked Nat :=
  if count == 3 || count == 5 then .ok count
  else if count ≥ 9 then .ok 9
  else .error (.exception "TypeError" "drawImage overload resolution")

private def converted (numbers : List UInt64) : Checked ImageArguments :=
  match numbers with
  | [x,y] => .ok (.at x y)
  | [x,y,width,height] => .ok (.sized x y width height)
  | [sx,sy,sw,sh,dx,dy,dw,dh] => .ok (.cropped sx sy sw sh dx dy dw dh)
  | _ => .error (.fault (.invalidContinuation "drawImage converted argument count"))

private def sourceDimensions (node : Node) : Nat × Nat :=
  if node.kind == .element "canvas" then
    (BrowserCanvas.dimension node "width",BrowserCanvas.dimension node "height")
  else match node.resourceStatus with
    | .image _ width height => (width,height)
    | _ => (0,0)

/-- ToImageSourceInternal checks zero-sized canvas sources before target paint
allocation, even if all later rectangle values are nonfinite. -/
private def validateInternalSource (node : Node) : Checked Unit :=
  if node.kind == .element "canvas" &&
      (BrowserCanvas.dimension node "width" == 0 || BrowserCanvas.dimension node "height" == 0) then
    failure "drawImage zero-size canvas source requires native InvalidStateError DOMException"
  else pure ()

/-- Source bitmap acquisition happens after destination allocation, before the
finite-rectangle guard. Captured asset metadata is the existing host input;
this function does not prove native decoding or response-origin semantics. -/
private def captureSource (state : State) (node : Node) : Checked (Option ImageSnapshot) := do
  if node.kind == .element "canvas" then
    let available ← BrowserCanvas.paintAvailable node
    if !available then pure none else
    pure (some (imageSnapshot node.canvasDrawing
      (BrowserCanvas.dimension node "width") (BrowserCanvas.dimension node "height") node.canvasAlpha))
  else
    if (getAttribute node "srcset").isSome then
      failure "drawImage responsive image selection requires native current-request state"
    else if let some parent := node.parent then
      let parent ← checkedNode state parent
      if parent.kind == .element "picture" then
        failure "drawImage picture source selection requires native current-request state"
      else captureRaster state node
    else captureRaster state node
where
  captureRaster (state : State) (node : Node) : Checked (Option ImageSnapshot) := do
    match node.resourceStatus with
    | .empty | .pending _ => pure none
    | .failed _ => failure "drawImage broken image source requires native InvalidStateError DOMException"
    | .image source width height =>
      let path ← BrowserResources.resourcePath state source
      let some asset := BrowserAssets.assets.find? (fun asset => asset.path == path) |
        failure "drawImage missing pinned image identity"
      if !["image/png","image/jpeg"].contains asset.mime then
        failure "drawImage animated, vector or other image source decoding"
      else if asset.mime == "image/png" && !BrowserCanvasImageAssets.staticPngHashes.contains asset.sha256 then
        failure "drawImage PNG animation/orientation is outside the pinned static-byte audit"
      else if asset.mime == "image/jpeg" && !BrowserCanvasImageAssets.ordinaryJpegHashes.contains asset.sha256 then
        failure "drawImage JPEG orientation is outside the pinned ordinary-orientation audit"
      else if asset.metadata != .image width height then
        failure "drawImage source dimensions differ from captured asset metadata"
      else if width == 0 || height == 0 then pure none
      else pure (some (.asset ⟨path,asset.sha256,asset.mime,source,
        getAttribute node "crossorigin",width,height⟩))
    | _ => failure "drawImage unsupported source bitmap state"

private def rectangleValid (node : Node) (arguments : ImageArguments) : Bool :=
  let (width,height) := sourceDimensions node
  match arguments with
  | .at x y => [x,y].all Number.isFinite && width != 0 && height != 0
  | .sized x y w h => [x,y,w,h].all Number.isFinite &&
      !Number.isZero w && !Number.isZero h && width != 0 && height != 0
  | .cropped sx sy sw sh dx dy dw dh => [sx,sy,sw,sh,dx,dy,dw,dh].all Number.isFinite &&
      !Number.isZero sw && !Number.isZero sh && !Number.isZero dw && !Number.isZero dh

private def dispatch (state : State) (receiver : Value) (arguments : List Value) (construct : Bool) : State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "drawImage is not a constructor")
  let .ok (id,node) := BrowserCanvas.contextReceiver state receiver |
    return Browser.checked state (BrowserCanvas.contextReceiver state receiver) fun _ => state
  let .ok count := overloadCount arguments.length |
    return Browser.checked state (overloadCount arguments.length) fun _ => state
  let .ok source := sourceId state (Builtins.argument arguments 0) |
    return Browser.checked state (sourceId state (Builtins.argument arguments 0)) fun _ => state
  if let some next := Browser.convertArguments state ⟨"Browser.CanvasImage","drawImage"⟩ receiver arguments false
      ((List.range (count-1)).map (fun index => (index+1,"number"))) then return next
  return Browser.checked state (((arguments.drop 1).take (count-1)).mapM toNumber >>= converted) fun convertedArguments =>
    Browser.checked state (checkedNode state source) fun sourceNode =>
    Browser.checked state (validateInternalSource sourceNode) fun _ =>
    Browser.checked state (BrowserCanvas.paintAvailable node) fun available =>
      if !available then Browser.result state .undefined else
      Browser.checked state (captureSource state sourceNode) fun snapshot =>
        match snapshot with
        | none => Browser.result state .undefined
        | some snapshot =>
          if !rectangleValid sourceNode convertedArguments then Browser.result state .undefined else
          Browser.checked state (replaceNode state id {node with
            canvasDrawing := BrowserCanvasState.drawImage node.canvasDrawing
              (BrowserCanvas.dimension node "width") (BrowserCanvas.dimension node "height")
              node.canvasAlpha snapshot convertedArguments}) fun next =>
                Browser.result next .undefined

private def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase != "convert" then
    Browser.fail state (.unresolved (.builtinContinuation continuation value))
  else Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
    let index := continuation.indices[0]?.getD 0
    let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
    dispatch state continuation.thisValue arguments false

def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.namespaceName == "Browser.CanvasContext" && builtin.name == "drawImage" then
      some (dispatch state receiver arguments construct) else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.CanvasImage" then some (resume state continuation value) else none
  | _ => none

end CookieClicker.JavaScript.BrowserCanvasImage

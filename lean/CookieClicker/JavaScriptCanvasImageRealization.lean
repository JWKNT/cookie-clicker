import CookieClicker.JavaScriptBrowserCanvasState

/-! Conditional realization of the executable immutable image-call records.
No decoder, origin-clean, backend-return, transform-refinement or pixel theorem
is supplied here. These are explicit premises of the relation, not axioms or
runtime oracles. Source calls execute only the separate admission adapter. -/
namespace CookieClicker.JavaScript.CanvasImageRealization
open BrowserCanvasState (Snapshot Command ImageSnapshot AssetImage ImageArguments)

structure NativeDrawing (Backend Path : Type) where
  fields : List (String × Value)
  transform : CanvasDeferred.NativeState Backend Path
  font : Option CssFont.Parsed
  colors : BrowserCanvasState.Colors

/-- The origin component is deliberately part of the scene type supplied by
native interpretation. It cannot be discarded merely because pixels are deferred. -/
structure NativeScene (Pixels Origin : Type) where
  pixels : Pixels
  origin : Origin

inductive NativeSource (Resource Pixels Origin : Type) where
  | asset (resource : Resource)
  | canvas (width height : Nat) (alpha : Bool) (scene : NativeScene Pixels Origin)

structure Contract (Backend Path Resource Pixels Origin : Type) where
  transforms : CanvasDeferred.NativeOperations Backend Path
  initialTransform : CanvasDeferred.NativeState Backend Path
  assetRealizes : AssetImage → Resource → Prop
  blankRealizes : Nat → Nat → Bool → NativeScene Pixels Origin → Prop
  otherCallRealizes : Command → NativeScene Pixels Origin → NativeScene Pixels Origin → Prop
  imageCall : NativeScene Pixels Origin → NativeDrawing Backend Path →
    NativeSource Resource Pixels Origin → ImageArguments → Except String (NativeScene Pixels Origin)

def DrawingRealizes {Backend Path Resource Pixels Origin : Type}
    (contract : Contract Backend Path Resource Pixels Origin)
    (drawing : Snapshot) (native : NativeDrawing Backend Path) : Prop :=
  drawing.fields = native.fields ∧ drawing.font = native.font ∧ drawing.colors = native.colors ∧
    CanvasDeferred.Realizes contract.transforms contract.initialTransform drawing.transform native.transform

mutual
  inductive SceneRealizes {Backend Path Resource Pixels Origin : Type}
      (contract : Contract Backend Path Resource Pixels Origin) :
      Nat → Nat → Bool → List Command → NativeScene Pixels Origin → Prop where
    | blank (width height alpha scene)
        (initial : contract.blankRealizes width height alpha scene) :
        SceneRealizes contract width height alpha [] scene
    | other (width height alpha prior command before after)
        (history : SceneRealizes contract width height alpha prior before)
        (notImage : match command with | .drawImage .. => False | _ => True)
        (step : contract.otherCallRealizes command before after) :
        SceneRealizes contract width height alpha (prior ++ [command]) after
    | image (width height alpha prior drawing source arguments before after nativeDrawing nativeSource)
        (history : SceneRealizes contract width height alpha prior before)
        (drawingState : DrawingRealizes contract drawing nativeDrawing)
        (sourceState : SourceRealizes contract source nativeSource)
        (normalReturn : contract.imageCall before nativeDrawing nativeSource arguments = .ok after) :
        SceneRealizes contract width height alpha
          (prior ++ [.drawImage drawing width height alpha source arguments]) after
  inductive SourceRealizes {Backend Path Resource Pixels Origin : Type}
      (contract : Contract Backend Path Resource Pixels Origin) :
      ImageSnapshot → NativeSource Resource Pixels Origin → Prop where
    | asset (image resource) (identity : contract.assetRealizes image resource) :
        SourceRealizes contract (.asset image) (.asset resource)
    | canvas (width height alpha commands scene)
        (history : SceneRealizes contract width height alpha commands scene) :
        SourceRealizes contract (.canvas width height alpha commands) (.canvas width height alpha scene)
end

/-- The source scene relation uses the captured command list itself. It does
not reread the source node, so later source mutations do not change this premise. -/
theorem captured_canvas_realizes {Backend Path Resource Pixels Origin : Type}
    (contract : Contract Backend Path Resource Pixels Origin) (source : BrowserCanvasState.State)
    (width height : Nat) (alpha : Bool) (scene : NativeScene Pixels Origin)
    (history : SceneRealizes contract width height alpha source.commands scene) :
    SourceRealizes contract (BrowserCanvasState.imageSnapshot source width height alpha)
      (.canvas width height alpha scene) :=
  .canvas width height alpha source.commands scene history

/-- One actual append in the implementation extends a scene relation only when
its source capture, drawing transform, and native normal-return premises hold.
The conclusion retains origin state together with pixels. -/
theorem image_call_realizes {Backend Path Resource Pixels Origin : Type}
    (contract : Contract Backend Path Resource Pixels Origin) (destination : BrowserCanvasState.State)
    (width height : Nat) (alpha : Bool) (source : ImageSnapshot) (arguments : ImageArguments)
    (before after : NativeScene Pixels Origin) (nativeDrawing : NativeDrawing Backend Path)
    (nativeSource : NativeSource Resource Pixels Origin)
    (history : SceneRealizes contract width height alpha destination.commands before)
    (drawingState : DrawingRealizes contract (BrowserCanvasState.snapshot destination) nativeDrawing)
    (sourceState : SourceRealizes contract source nativeSource)
    (normalReturn : contract.imageCall before nativeDrawing nativeSource arguments = .ok after) :
    SceneRealizes contract width height alpha
      (BrowserCanvasState.drawImage destination width height alpha source arguments).commands after :=
  .image width height alpha destination.commands (BrowserCanvasState.snapshot destination)
    source arguments before after nativeDrawing nativeSource history drawingState sourceState normalReturn

end CookieClicker.JavaScript.CanvasImageRealization

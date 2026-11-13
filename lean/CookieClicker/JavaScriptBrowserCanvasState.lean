import CookieClicker.JavaScriptState
import CookieClicker.JavaScriptNumber
import CookieClicker.JavaScriptCanvasMatrix
import CookieClicker.JavaScriptCanvasDeferred
import CookieClicker.JavaScriptCssFont
import CookieClicker.JavaScriptCssColor

/-! Drawing-state projection of the pinned Chromium 87 canvas implementation.
Raster operations, paths, font resolution, and general CSS colors remain separate
operations. Unsupported mutations cannot enter this projection silently.
-/
namespace CookieClicker.JavaScript.BrowserCanvasState

private def string (value : String) : Value := .string (JSString.ofString value)

def defaults : List (String × Value) :=
  [("globalAlpha", .number Number.one), ("globalCompositeOperation", string "source-over"),
   ("lineWidth", .number Number.one), ("lineCap", string "butt"), ("lineJoin", string "miter"),
   ("miterLimit", .number (Number.ofNat 10)), ("lineDashOffset", .number Number.positiveZero),
   ("shadowOffsetX", .number Number.positiveZero), ("shadowOffsetY", .number Number.positiveZero),
   ("shadowBlur", .number Number.positiveZero), ("imageSmoothingEnabled", .boolean true),
   ("imageSmoothingQuality", string "low"), ("textAlign", string "start"),
   ("textBaseline", string "alphabetic"), ("fillStyle", string "#000000"),
   ("strokeStyle", string "#000000"), ("shadowColor", string "rgba(0, 0, 0, 0)"),
   ("filter", string "none"), ("font", string "10px sans-serif")]

structure Colors where
  fill : CssColor.RGBA := ⟨0,0,0,255⟩
  stroke : CssColor.RGBA := ⟨0,0,0,255⟩
  shadow : CssColor.RGBA := ⟨0,0,0,0⟩
  deriving Repr, DecidableEq

structure Snapshot where
  fields : List (String × Value)
  transform : CanvasDeferred.State
  font : Option CssFont.Parsed
  colors : Colors
  deriving Repr, DecidableEq

/-- Deferred raster command. All admitted paths retain the initial full-canvas
clip: path/clip mutations remain explicit requests. A fill records the drawing
state and target allocation at the call, not a reference to mutable state. -/
inductive ImageArguments where
  | at (x y : UInt64)
  | sized (x y width height : UInt64)
  | cropped (sx sy sw sh dx dy dw dh : UInt64)
  deriving Repr, DecidableEq

/-- Resource provenance is retained without inventing an origin-clean result.
File/CORS response semantics belong to the resource realization relation. -/
structure AssetImage where
  path : String
  sha256 : String
  mime : String
  sourceURL : JSString
  crossOrigin : Option JSString
  width : Nat
  height : Nat
  deriving Repr, DecidableEq

mutual
  inductive Command where
    | clearRect (drawing : Snapshot) (x y width height : UInt64)
    | fillRect (drawing : Snapshot) (canvasWidth canvasHeight : Nat) (alpha : Bool)
        (x y width height : UInt64)
    | drawImage (drawing : Snapshot) (canvasWidth canvasHeight : Nat) (alpha : Bool)
        (source : ImageSnapshot) (arguments : ImageArguments)
    deriving Repr
  inductive ImageSnapshot where
    | asset (image : AssetImage)
    | canvas (width height : Nat) (alpha : Bool) (commands : List Command)
    deriving Repr
end

structure State where
  fields : List (String × Value) := defaults
  transform : CanvasDeferred.State := {}
  font : Option CssFont.Parsed := none
  colors : Colors := {}
  saved : List Snapshot := []
  commands : List Command := []
  deriving Repr

def read (state : State) (name : String) : Option Value :=
  (state.fields.find? (fun field => field.1 == name)).map Prod.snd

def write (state : State) (name : String) (value : Value) : State :=
  { state with fields := state.fields.map fun field => if field.1 == name then (name,value) else field }

def writeFont (state : State) (font : CssFont.Parsed) : State :=
  { write state "font" (string (CssFont.text font)) with font := some font }

def writeColor (state : State) (name : String) (rgba : CssColor.RGBA) : Option State := do
  let text ← CssColor.canvasText rgba
  let colors := if name == "fillStyle" then {state.colors with fill := rgba}
    else if name == "strokeStyle" then {state.colors with stroke := rgba}
    else if name == "shadowColor" then {state.colors with shadow := rgba}
    else state.colors
  return {write state name (string text) with colors}

def snapshot (state : State) : Snapshot :=
  ⟨state.fields,state.transform,state.font,state.colors⟩

def save (state : State) : State :=
  { state with saved := snapshot state :: state.saved }

def restore (state : State) : State :=
  match state.saved with
  | [] => state
  | snapshot :: saved =>
    { state with
      fields := snapshot.fields
      transform := snapshot.transform
      font := snapshot.font
      colors := snapshot.colors
      saved := saved }

def reset (_state : State) : State := {}

/-- Snapshot the source's existing scene by value, before any destination write.
A self-copy therefore contains a finite earlier scene, never a mutable node ID. -/
def imageSnapshot (state : State) (width height : Nat) (alpha : Bool) : ImageSnapshot :=
  .canvas width height alpha state.commands

/-- A native call record after source-visible admission checks. Rect clipping,
origin taint and raster output are deferred together; this is not a pixel write. -/
def drawImage (state : State) (width height : Nat) (alpha : Bool)
    (source : ImageSnapshot) (arguments : ImageArguments) : State :=
  {state with commands := state.commands ++ [.drawImage (snapshot state) width height alpha source arguments]}

theorem image_snapshot_is_immutable (state : State) (width height : Nat) (alpha : Bool) :
    imageSnapshot state width height alpha = .canvas width height alpha state.commands := rfl

theorem image_call_captures_source (destination source : State)
    (dw dh sw sh : Nat) (destinationAlpha sourceAlpha : Bool) (arguments : ImageArguments) :
    (drawImage destination dw dh destinationAlpha (imageSnapshot source sw sh sourceAlpha) arguments).commands =
      destination.commands ++ [.drawImage (snapshot destination) dw dh destinationAlpha
        (.canvas sw sh sourceAlpha source.commands) arguments] := rfl

theorem image_call_preserves_drawing (state : State) (width height : Nat) (alpha : Bool)
    (source : ImageSnapshot) (arguments : ImageArguments) :
    snapshot (drawImage state width height alpha source arguments) = snapshot state := rfl

theorem restore_save (state : State) : restore (save state) = state := rfl

theorem restore_after_write (state : State) (name : String) (value : Value) :
    restore (write (save state) name value) = state := rfl

theorem reset_clears_saved (state : State) : (reset state).saved = [] := rfl

theorem reset_defaults (state : State) : (reset state).fields = defaults := rfl

theorem restore_after_font (state : State) (font : CssFont.Parsed) :
    restore (writeFont (save state) font) = state := rfl

theorem restore_after_matrix (state : State) (matrix : CanvasMatrix.Matrix) :
    restore {save state with transform := {state.transform with known := some matrix}} = state := rfl

theorem reset_matrix (state : State) : (reset state).transform.known = some CanvasMatrix.identity := rfl

theorem reset_font (state : State) : (reset state).font = none := rfl

theorem reset_colors (state : State) : (reset state).colors = {} := rfl

/-- Chromium validates before canvas allocation; a rectangle with just one zero
side is valid. In particular `copy` can clear the canvas for such a rectangle. -/
def validRectangle (x y width height : UInt64) : Bool :=
  [x,y,width,height].all Number.isFinite && !(Number.isZero width && Number.isZero height)

/-- Native AdjustRectForCanvas evaluates in binary64, then each component is
clamped and rounded to binary32 before SkRect construction. -/
def adjustedRectangle (x y width height : UInt64) : List UInt64 :=
  let negativeWidth := Number.lessThan width Number.positiveZero
  let negativeHeight := Number.lessThan height Number.positiveZero
  let width := if negativeWidth then Number.neg width else width
  let height := if negativeHeight then Number.neg height else height
  let x := if negativeWidth then Number.sub x width else x
  let y := if negativeHeight then Number.sub y height else y
  [x,y,width,height].map CanvasMatrix.clampFloat

/-- Paint allocation has already been checked by the browser adapter. The
command is deferred, including zero-area/full-canvas composite interactions.
An unknown transform records the native call; its native invertibility guard
belongs to interpretation. It is not a claim that pixels changed. -/
def fillRect (state : State) (canvasWidth canvasHeight : Nat) (alpha : Bool)
    (x y width height : UInt64) : State :=
  if validRectangle x y width height && (state.transform.known.map CanvasMatrix.invertible).getD true then
    match adjustedRectangle x y width height with
    | [x,y,width,height] => {state with commands := state.commands ++
        [.fillRect (snapshot state) canvasWidth canvasHeight alpha x y width height]}
    | _ => state
  else state

theorem fill_preserves_fields (state : State) (canvasWidth canvasHeight : Nat) (alpha : Bool)
    (x y width height : UInt64) :
    (fillRect state canvasWidth canvasHeight alpha x y width height).fields = state.fields := by
  simp only [fillRect]
  split
  · split <;> rfl
  · rfl

theorem fill_preserves_saved (state : State) (canvasWidth canvasHeight : Nat) (alpha : Bool)
    (x y width height : UInt64) :
    (fillRect state canvasWidth canvasHeight alpha x y width height).saved = state.saved := by
  simp only [fillRect]
  split
  · split <;> rfl
  · rfl

theorem invalid_fill_unchanged (state : State) (canvasWidth canvasHeight : Nat) (alpha : Bool)
    (x y width height : UInt64) (invalid : validRectangle x y width height = false) :
    fillRect state canvasWidth canvasHeight alpha x y width height = state := by
  simp [fillRect,invalid]

/-- Clear commands do not belong to the saved drawing-state stack. -/
def clearRect (state : State) (x y width height : UInt64) : State :=
  if [x,y,width,height].all Number.isFinite && !(Number.isZero width && Number.isZero height) then
    {state with commands := state.commands ++ [.clearRect (snapshot state) x y width height]}
  else state

theorem clear_preserves_fields (state : State) (x y width height : UInt64) :
    (clearRect state x y width height).fields = state.fields := by
  simp [clearRect]; split <;> rfl

theorem clear_preserves_saved (state : State) (x y width height : UInt64) :
    (clearRect state x y width height).saved = state.saved := by
  simp [clearRect]; split <;> rfl

theorem restore_preserves_commands (state : State) : (restore state).commands = state.commands := by
  cases h : state.saved <;> simp [restore,h]

theorem reset_clears_commands (state : State) : (reset state).commands = [] := rfl

/-- Clear restores the creation pixel wherever the renderer's transformed,
clipped mask applies. It leaves an initially blank bitmap blank for every mask.
These lemmas apply to clear-only histories; deferred painting has no supplied
pixel interpretation. -/
def clearPixels {Point Pixel : Type} (initial : Pixel) (covered : Point → Bool)
    (pixels : Point → Pixel) : Point → Pixel :=
  fun point => if covered point then initial else pixels point

theorem clear_blank {Point Pixel : Type} (initial : Pixel) (covered : Point → Bool) :
    clearPixels initial covered (fun _ => initial) = fun _ => initial := by
  funext point
  simp [clearPixels]

theorem clear_history_blank {Point Pixel : Type} (initial : Pixel) (masks : List (Point → Bool)) :
    masks.foldl (fun pixels mask => clearPixels initial mask pixels) (fun _ => initial) =
      fun _ => initial := by
  induction masks with
  | nil => rfl
  | cons mask rest ih => simpa only [List.foldl_cons,clear_blank] using ih

/-- Blink's clampTo<float>: first clamp to the finite binary32 range, then
round to binary32. The result is re-encoded exactly in binary64 for JS. -/
def clampFloat := CanvasMatrix.clampFloat

def numericNames : List String :=
  ["globalAlpha", "lineWidth", "miterLimit", "lineDashOffset", "shadowOffsetX", "shadowOffsetY", "shadowBlur"]

def setNumber (state : State) (name : String) (bits : UInt64) : State :=
  let valid := if name == "globalAlpha" then Number.lessEqual Number.positiveZero bits && Number.lessEqual bits Number.one
    else Number.isFinite bits &&
      (if ["lineWidth","miterLimit"].contains name then Number.lessThan Number.positiveZero bits
       else if name == "shadowBlur" then Number.lessEqual Number.positiveZero bits else true)
  if !valid then state
  else if (read state name).any (fun value => match value with
      | .number old => Number.equal old bits | _ => false) then state
  else write state name (.number (if name == "globalAlpha" then bits else clampFloat bits))

def keywords (name : String) : List String :=
  if name == "globalCompositeOperation" then
    ["clear","copy","source-over","source-in","source-out","source-atop",
     "destination-over","destination-in","destination-out","destination-atop","xor","lighter",
     "normal","multiply","screen","overlay","darken","lighten","color-dodge","color-burn",
     "hard-light","soft-light","difference","exclusion","hue","saturation","color","luminosity"]
  else if name == "lineCap" then ["butt","round","square"]
  else if name == "lineJoin" then ["miter","round","bevel"]
  else if name == "imageSmoothingQuality" then ["low","medium","high"]
  else if name == "textAlign" then ["start","end","left","center","right"]
  else if name == "textBaseline" then ["top","hanging","middle","alphabetic","ideographic","bottom"]
  else []

def setKeyword (state : State) (name : String) (value : JSString) : State :=
  if !(keywords name).any (fun option => JSString.ofString option == value) then state
  else write state name (.string (if name == "globalCompositeOperation" && value == JSString.ofString "normal"
    then JSString.ofString "source-over" else value))

theorem invalid_alpha_unchanged (state : State) (bits : UInt64)
    (invalid : (Number.lessEqual Number.positiveZero bits && Number.lessEqual bits Number.one) = false) :
    setNumber state "globalAlpha" bits = state := by simp [setNumber, invalid]

theorem invalid_keyword_unchanged (state : State) (name : String) (value : JSString)
    (invalid : (keywords name).any (fun option => JSString.ofString option == value) = false) :
    setKeyword state name value = state := by simp [setKeyword, invalid]

end CookieClicker.JavaScript.BrowserCanvasState

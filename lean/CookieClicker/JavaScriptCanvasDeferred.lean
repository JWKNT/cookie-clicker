import CookieClicker.JavaScriptCanvasMatrix

/-! Isolated integration candidate. Source-converted transform calls are retained
in order. The numerical cache is absent after an uncomputed native rotation;
no caller can obtain a stale matrix from this type. This is a representation,
not an implementation of native libm, SkCanvas, allocation, or rasterization. -/
namespace CookieClicker.JavaScript.CanvasDeferred

abbrev Matrix := CanvasMatrix.Matrix

inductive Operation where
  | translate (x y : UInt64)
  | scale (x y : UInt64)
  | rotate (radians : UInt64)
  | transform (matrix : Matrix)
  | setTransform (matrix : Matrix)
  | resetTransform
  deriving Repr, DecidableEq

structure State where
  history : List Operation := []
  known : Option Matrix := some CanvasMatrix.identity
  deriving Repr, DecidableEq

/-- Calls reach this function only after WebIDL argument conversion and the
paint-canvas acquisition check. Invalid numbers have no transform effect. The
history records the admitted native call, including native internal guards. -/
def apply (state : State) (operation : Operation) : State :=
  let known := match operation with
    | .translate x y => state.known.map (fun matrix => CanvasMatrix.translate matrix x y)
    | .scale x y => state.known.map (fun matrix => CanvasMatrix.scale matrix x y)
    | .rotate radians => state.known.bind (fun matrix => CanvasMatrix.rotate matrix radians)
    | .transform matrix => state.known.map (fun old => CanvasMatrix.transform old matrix)
    | .setTransform matrix =>
      if (CanvasMatrix.values matrix).all Number.isFinite then
        some (CanvasMatrix.setTransform CanvasMatrix.identity matrix)
      else state.known
    | .resetTransform => some CanvasMatrix.identity
  {history := state.history ++ [operation],known}

/-- The native logical matrix calculation uses the platform C library. Both
functions are explicit interpretation parameters, never V8 replacements. -/
structure NativeLibrary where
  cos : UInt64 → UInt64
  sin : UInt64 → UInt64

/-- The backend and path states are independent of the logical matrix. Each
operation below denotes a normally returning native backend call; context
acquisition/fatal-resource behavior is a separate admission premise. -/
structure NativeState (Backend Path : Type) where
  matrix : Matrix
  backend : Backend
  path : Path

structure NativeOperations (Backend Path : Type) where
  library : NativeLibrary
  rotateBackend : Backend → UInt64 → Backend
  transformPath : Path → Matrix → Path
  other : NativeState Backend Path → Operation → NativeState Backend Path

def rotationMatrix (library : NativeLibrary) (angle : UInt64) : Matrix :=
  let cosine := library.cos angle
  let sine := library.sin angle
  ⟨cosine,sine,Number.neg sine,cosine,0,0⟩

/-- kPiFloat is the rounded binary32 constant, promoted to binary64. -/
def backendDegrees (angle : UInt64) : UInt64 :=
  CanvasMatrix.clampFloat (Number.mul angle (Number.div (Number.ofNat 180) 0x400921fb60000000))

/-- Closed normal-return body of pinned BaseRenderingContext2D::rotate after
paint acquisition. This does not claim backend or C-library implementation
refinement. There is no exception constructor in the represented native body. -/
def nativeRotate {Backend Path : Type} (operations : NativeOperations Backend Path)
    (before : NativeState Backend Path) (angle : UInt64) : NativeState Backend Path :=
  if !Number.isFinite angle then before
  else
    let matrix := CanvasMatrix.multiply before.matrix (rotationMatrix operations.library angle)
    if CanvasMatrix.same before.matrix matrix then before
    else if !CanvasMatrix.invertible matrix then {before with matrix}
    else {
      matrix := matrix
      backend := operations.rotateBackend before.backend (backendDegrees angle)
      path := operations.transformPath before.path
        (CanvasMatrix.multiply CanvasMatrix.identity (rotationMatrix operations.library (Number.neg angle)))}

def nativeStep {Backend Path : Type} (operations : NativeOperations Backend Path)
    (before : NativeState Backend Path) : Operation → NativeState Backend Path
  | .rotate angle => nativeRotate operations before angle
  | operation => operations.other before operation

def denote {Backend Path : Type} (operations : NativeOperations Backend Path)
    (initial : NativeState Backend Path) (history : List Operation) : NativeState Backend Path :=
  history.foldl (nativeStep operations) initial

def Realizes {Backend Path : Type} (operations : NativeOperations Backend Path)
    (initial : NativeState Backend Path) (state : State) (native : NativeState Backend Path) : Prop :=
  denote operations initial state.history = native ∧
    ∀ cached, state.known = some cached → native.matrix = cached

/-- A history extension denotes one further native call. No pixel equality or
native failure-elision conclusion is included. -/
theorem append_denotation {Backend Path : Type} (operations : NativeOperations Backend Path)
    (initial : NativeState Backend Path) (state : State) (operation : Operation) :
    denote operations initial (apply state operation).history =
      nativeStep operations (denote operations initial state.history) operation := by
  simp [denote,apply,List.foldl_append]

theorem rotation_realizes {Backend Path : Type} (operations : NativeOperations Backend Path)
    (initial native : NativeState Backend Path) (state : State) (angle : UInt64)
    (realizes : Realizes operations initial state native)
    (finite : Number.isFinite angle = true) (nonzero : Number.isZero angle = false) :
    Realizes operations initial (apply state (.rotate angle)) (nativeRotate operations native angle) := by
  constructor
  · rw [append_denotation,realizes.1]
    rfl
  · intro cached equality
    cases h : state.known <;> simp [apply,h,CanvasMatrix.rotate,finite,nonzero] at equality

theorem nonzero_rotation_forgets_cache (state : State) (angle : UInt64)
    (finite : Number.isFinite angle = true) (nonzero : Number.isZero angle = false) :
    (apply state (.rotate angle)).known = none := by
  cases h : state.known <;> simp [apply,h,CanvasMatrix.rotate,finite,nonzero]

theorem reset_restores_cache (state : State) :
    (apply state .resetTransform).known = some CanvasMatrix.identity := rfl

theorem unknown_translation_remains_unknown (state : State) (x y : UInt64)
    (unknown : state.known = none) :
    (apply state (.translate x y)).known = none := by simp [apply,unknown]

end CookieClicker.JavaScript.CanvasDeferred

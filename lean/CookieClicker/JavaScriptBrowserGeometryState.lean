import CookieClicker.JavaScriptState

/-! Native rectangle values are distinct from renderer layout. Their mutable
coordinates retain binary64 values and the captured native interface brand. -/
namespace CookieClicker.JavaScript.BrowserGeometryState

structure Rect where
  object : ObjectId
  x : UInt64
  y : UInt64
  width : UInt64
  height : UInt64
  writable : Bool
  deriving Repr

end CookieClicker.JavaScript.BrowserGeometryState

import Lean
import CookieClicker.JavaScriptCanvasMatrix

open Lean CookieClicker.JavaScript CanvasMatrix
private def bits (j : Json) : Except String UInt64 := do
  let text ← j.getStr?
  let some value := text.toNat? | throw "Expected bit string"
  if value ≥ 2^64 then throw "Bits out of range"
  return UInt64.ofNat value
private def operation (m : Matrix) (j : Json) : Except String Matrix := do
  let op ← j.getObjVal? "op" >>= Json.getStr?
  let args ← (← j.getObjVal? "args" >>= Json.getArr?).toList.mapM bits
  match op,args with
  | "translate",[x,y] => return translate m x y
  | "scale",[x,y] => return scale m x y
  | "transform",[a,b,c,d,e,f] => return transform m ⟨a,b,c,d,e,f⟩
  | "setTransform",[a,b,c,d,e,f] => return setTransform m ⟨a,b,c,d,e,f⟩
  | "resetTransform",[] => return identity
  | "rotate",[a] => match rotate m a with | some n => return n | none => throw "C-library trigonometry is unresolved"
  | _,_ => throw "Unknown operation/arity"
private def evaluate (j : Json) : Except String Json := do
  let ops ← j.getArr?
  let result ← ops.toList.foldlM operation identity
  return toJson ((values result).map fun bits => toString bits.toNat)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let text ← stdin.readToEnd
  let output := do
    let input ← Json.parse text
    let requests ← input.getArr?
    let result ← requests.toList.mapM evaluate
    return toJson result
  match output with
  | .error reason => throw (IO.userError reason)
  | .ok answer => (← IO.getStdout).putStrLn answer.compress

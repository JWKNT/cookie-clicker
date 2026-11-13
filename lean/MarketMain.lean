import Lean
import CookieClicker.MarketRecurrence

open Lean CookieClicker.FullGame.MarketRecurrence

private def rational (value : Rat) : Json :=
  Json.mkObj [("numerator", Json.str value.num.repr), ("denominator", Json.str value.den.repr)]

private def evaluate (input : Json) : Except String Json := do
  let direction ← match ← (← input.getObjVal? "direction").getStr? with
    | "rise" => pure Direction.rise
    | "fall" => pure Direction.fall
    | _ => throw "Unknown direction"
  let mode ← match ← (← input.getObjVal? "mode").getNat? with
    | 0 => pure Mode.stable
    | 1 => pure Mode.slowRise
    | 2 => pure Mode.slowFall
    | 3 => pure Mode.fastRise
    | 4 => pure Mode.fastFall
    | 5 => pure Mode.chaotic
    | _ => throw "Unknown mode"
  let price ← (← input.getObjVal? "price").getInt?
  let velocity ← (← input.getObjVal? "velocity").getInt?
  let resting ← (← input.getObjVal? "resting").getInt?
  let boostTenths ← (← input.getObjVal? "boostTenths").getNat?
  let after := forcedStep direction ((boostTenths : Rat) / 10) resting { price, velocity, mode }
  return Json.mkObj [("price", rational after.price), ("velocity", rational after.velocity)]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok cases =>
    match cases.mapM evaluate with
    | .error error => (← IO.getStderr).putStrLn error; return 1
    | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0

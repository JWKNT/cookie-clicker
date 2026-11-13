import CookieClicker.JavaScriptParser
import CookieClicker.JavaScriptDecode
import CookieClicker.JavaScriptBuiltins

open Lean CookieClicker.JavaScript

private def units (json : Json) : Except String JSString := do
  let values ← (← json.getArr?).toList.mapM Json.getNat?
  if values.any (· ≥ 65536) then throw "UTF16 input outside code-unit range"
  pure (values.map UInt16.ofNat)

private def encodeValue : Value → Json
  | .undefined => Json.mkObj [("type",toJson "undefined")]
  | .null => Json.mkObj [("type",toJson "null")]
  | .boolean value => Json.mkObj [("type",toJson "boolean"),("value",toJson value)]
  | .number bits | .timestamp (.native bits) => Json.mkObj [("type",toJson "number"),("bits",toJson bits.toNat.repr)]
  | .calendar q => Json.mkObj [("type",toJson "calendar"),("numerator",toJson (toString q.num)),("denominator",toJson q.den)]
  | .timestamp (.extended time) => Json.mkObj [("type",toJson "timestamp"),
      ("numerator",toJson (toString time.normalize.numerator)),("scale",toJson time.normalize.scale)]
  | .textIndex value => Json.mkObj [("type",toJson "number"),("bits",toJson (Number.ofInt value).toNat.repr)]
  | .timestampText value => Json.mkObj [("type",toJson "string"),("units",toJson (value.toList.map UInt16.toNat))]
  | .string value => Json.mkObj [("type",toJson "string"),("units",toJson (value.map UInt16.toNat))]
  | .object id => Json.mkObj [("type",toJson "object"),("id",toJson id)]

private def execution (program : Program) (fuel : Nat) : Json :=
  let finished := Builtins.run fuel (startProgram Builtins.standardMachine program)
  match status finished with
  | .completion (.normal value) => Json.mkObj [("status",toJson "complete"),("value",encodeValue (value.getD .undefined))]
  | .value value => Json.mkObj [("status",toJson "complete"),("value",encodeValue value)]
  | other => Json.mkObj [("status",toJson "other"),("detail",toJson (reprStr other))]

private def mismatch (actual expected : String) : Json := Id.run do
  let actual := actual.toList.toArray
  let expected := expected.toList.toArray
  let mut offset := 0
  while offset < min actual.size expected.size && actual[offset]? == expected[offset]? do
    offset := offset+1
  return Json.mkObj [("offset",toJson offset),
    ("actual",toJson (String.ofList (actual.extract (offset-100) (offset+300)).toList)),
    ("expected",toJson (String.ofList (expected.extract (offset-100) (offset+300)).toList))]

private def one (request : Json) : Except String Json := do
  let source ← units (← request.getObjVal? "sourceUnits")
  let fuel := (request.getObjValAs? Nat "fuel").toOption.getD (16*source.length+64)
  match Parser.parseSource source ((request.getObjValAs? Bool "functionBody").toOption.getD false) fuel with
  | .error error => pure (Json.mkObj [("status",toJson "parse-error"),("kind",toJson (reprStr error.kind)),
      ("offset",toJson error.offset),("message",toJson error.message)])
  | .ok program =>
    let comparison ← match (request.getObjVal? "expectedAst").toOption with
      | none => pure []
      | some expected => do
        let artifact ← decodeArtifact expected
        if artifact.units.size != 1 then throw "Expected exactly one reference unit"
        let some unit := artifact.units[0]? | throw "Missing reference unit"
        let actual := reprStr program
        let expected := reprStr unit.program
        pure ([("matchesReference",toJson (actual == expected))] ++
          if actual == expected then [] else [("mismatch",mismatch actual expected)])
    let execution := if (request.getObjValAs? Bool "execute").toOption.getD false then
      [("execution",execution program ((request.getObjValAs? Nat "executionFuel").toOption.getD 500000))] else []
    pure (Json.mkObj ([("status",toJson "parsed"),("statements",toJson program.body.length),
      ("strict",toJson program.strict),("parserRefinementVerified",toJson false)] ++ comparison ++ execution))

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let result := do
    let json ← Json.parse input
    let requests ← json.getArr?
    let output ← requests.toList.mapM one
    pure (Json.arr output.toArray)
  match result with
  | .error error => throw (IO.userError error)
  | .ok output => (← IO.getStdout).putStrLn output.compress

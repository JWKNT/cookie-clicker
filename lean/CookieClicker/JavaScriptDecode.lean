import Lean
import CookieClicker.JavaScriptSyntax

/-! Decoder for the closed, typed flat AST emitted by `javascript-ast.mjs`.
Every semantic child must refer to an earlier node in the same compilation
unit, with the required expression/statement type. This rules out cycles and
forward references. Decoding is not a proof of Acorn correctness, source hash
correspondence, JavaScript execution semantics, or host behavior.
-/
namespace CookieClicker.JavaScript
open Lean

inductive DecodedSyntax where
  | expression (value : Expr)
  | statement (value : Stmt)
  | program (value : Program)
  deriving Repr

structure DecodedNode where
  unit : Nat
  value : DecodedSyntax
  deriving Repr

structure DecodedUnit where
  name : String
  kind : String
  root : Nat
  program : Program
  deriving Repr

structure DecodedArtifact where
  clockAnnotated : Bool := false
  nodes : Array DecodedNode
  units : Array DecodedUnit
  deriving Repr

private def field := Json.getObjVal?
private def stringField (j : Json) (name : String) := field j name >>= Json.getStr?
private def natField (j : Json) (name : String) := field j name >>= Json.getNat?
private def boolField (j : Json) (name : String) := field j name >>= Json.getBool?
private def arrayField (j : Json) (name : String) := field j name >>= Json.getArr?

private def keys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  for (key, _) in object.toList do
    if !allowed.contains key then throw s!"Unknown AST field: {key}"

private def optional (read : Json → Except String α) (j : Json) : Except String (Option α) :=
  match j with
  | .null => .ok none
  | other => some <$> read other

private def bitPattern (j : Json) : Except String UInt64 := do
  let text ← j.getStr?
  let some n := text.toNat? | throw "Expected unsigned decimal binary64 bit string"
  if n ≥ 2 ^ 64 || n.repr != text then throw "Noncanonical or out-of-range binary64 bits"
  return UInt64.ofNat n

private def codeUnits (j : Json) : Except String JSString := do
  let values ← j.getArr?
  values.toList.mapM fun value => do
    let n ← value.getNat?
    if n > 65535 then throw "UTF-16 code unit exceeds uint16"
    return UInt16.ofNat n

private def unaryOp : String → Except String UnaryOp
  | "delete" => .ok .delete | "void" => .ok .void | "typeOf" => .ok .typeOf
  | "plus" => .ok .plus | "minus" => .ok .minus | "bitNot" => .ok .bitNot
  | "not" => .ok .not | s => .error s!"Unknown unary operator: {s}"

private def updateOp : String → Except String UpdateOp
  | "increment" => .ok .increment | "decrement" => .ok .decrement
  | s => .error s!"Unknown update operator: {s}"

private def binaryOp : String → Except String BinaryOp
  | "equal" => .ok .equal | "notEqual" => .ok .notEqual
  | "strictEqual" => .ok .strictEqual | "strictNotEqual" => .ok .strictNotEqual
  | "less" => .ok .less | "lessEqual" => .ok .lessEqual
  | "greater" => .ok .greater | "greaterEqual" => .ok .greaterEqual
  | "shiftLeft" => .ok .shiftLeft | "shiftRight" => .ok .shiftRight
  | "unsignedShiftRight" => .ok .unsignedShiftRight
  | "add" => .ok .add | "subtract" => .ok .subtract | "multiply" => .ok .multiply
  | "divide" => .ok .divide | "remainder" => .ok .remainder
  | "bitOr" => .ok .bitOr | "bitXor" => .ok .bitXor | "bitAnd" => .ok .bitAnd
  | "inOp" => .ok .inOp | "instanceOf" => .ok .instanceOf
  | s => .error s!"Unknown binary operator: {s}"

private def logicalOp : String → Except String LogicalOp
  | "and" => .ok .and | "or" => .ok .or
  | s => .error s!"Unknown logical operator: {s}"

private def assignmentOp : String → Except String AssignmentOp
  | "assign" => .ok .assign | "add" => .ok .add | "subtract" => .ok .subtract
  | "multiply" => .ok .multiply | "divide" => .ok .divide | "remainder" => .ok .remainder
  | "shiftLeft" => .ok .shiftLeft | "shiftRight" => .ok .shiftRight
  | "unsignedShiftRight" => .ok .unsignedShiftRight
  | "bitOr" => .ok .bitOr | "bitXor" => .ok .bitXor | "bitAnd" => .ok .bitAnd
  | s => .error s!"Unknown assignment operator: {s}"

private def propertyKind : String → Except String PropertyKind
  | "init" => .ok .init | "get" => .ok .get | "set" => .ok .set
  | s => .error s!"Unknown property kind: {s}"

private def propertyName (j : Json) : Except String PropertyName := do
  match ← stringField j "kind" with
  | "identifier" => keys j ["kind", "name"]; return .identifier (← stringField j "name")
  | "string" => keys j ["kind", "units", "raw"]; return .string (← codeUnits (← field j "units"))
  | "number" => keys j ["kind", "bits", "raw"]; return .number (← bitPattern (← field j "bits"))
  | s => throw s!"Unknown property name kind: {s}"

private def child (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String DecodedSyntax := do
  let index ← j.getNat?
  let some node := nodes[index]? | throw "AST child is a forward, cyclic or out-of-range reference"
  if node.unit != unit then throw "AST child crosses compilation units"
  return node.value

private def expression (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String Expr := do
  match ← child nodes unit j with
  | .expression value => return value
  | _ => throw "AST expression child has the wrong type"

private def statement (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String Stmt := do
  match ← child nodes unit j with
  | .statement value => return value
  | _ => throw "AST statement child has the wrong type"

private def expressions (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String (List Expr) := do
  (← j.getArr?).toList.mapM (expression nodes unit)

private def statements (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String (List Stmt) := do
  (← j.getArr?).toList.mapM (statement nodes unit)

private def declarations (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String (List (String × Option Expr)) := do
  (← j.getArr?).toList.mapM fun item => do
    keys item ["name", "value"]
    return (← stringField item "name", ← optional (expression nodes unit) (← field item "value"))

private def forInitial (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String ForInit := do
  match ← stringField j "kind" with
  | "expression" => keys j ["kind", "value"]; return .expression (← expression nodes unit (← field j "value"))
  | "variables" => keys j ["kind", "declarations"]; return .variables (← declarations nodes unit (← field j "declarations"))
  | s => throw s!"Unknown for initializer kind: {s}"

private def forBinding (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String ForInBinding := do
  match ← stringField j "kind" with
  | "variable" => keys j ["kind", "name"]; return .variable (← stringField j "name")
  | "reference" => keys j ["kind", "value"]; return .reference (← expression nodes unit (← field j "value"))
  | s => throw s!"Unknown for-in binding kind: {s}"

private def parameters (j : Json) : Except String (List String) := do
  (← arrayField j "parameters").toList.mapM Json.getStr?

private def baseKeys := ["id", "kind", "tag", "source"]

private def decodeExpr (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String Expr := do
  let ex name := field j name >>= expression nodes unit
  let exs name := field j name >>= expressions nodes unit
  let check extra := keys j (baseKeys ++ extra)
  match ← stringField j "tag" with
  | "identifier" => check ["name"]; return .identifier (← stringField j "name")
  | "this" => check []; return .this
  | "literal" =>
    match ← stringField j "literalKind" with
    | "null" => check ["literalKind"]; return .literal .null
    | "boolean" => check ["literalKind", "value"]; return .literal (.boolean (← boolField j "value"))
    | "number" => check ["literalKind", "bits", "raw"]; return .literal (.number (← bitPattern (← field j "bits")))
    | "string" => check ["literalKind", "units", "raw"]; return .literal (.string (← codeUnits (← field j "units")))
    | s => throw s!"Unknown literal kind: {s}"
  | "regexp" => check ["pattern", "flags", "raw"]; return .regexp (← codeUnits (← field j "pattern")) (← stringField j "flags")
  | "array" => check ["elements"]; return .array (← (← arrayField j "elements").toList.mapM (optional (expression nodes unit)))
  | "object" =>
    check ["properties"]
    let props ← (← arrayField j "properties").toList.mapM fun prop => do
      keys prop ["key", "kind", "value", "source"]
      return ObjectProperty.mk (← propertyName (← field prop "key"))
        (← propertyKind (← stringField prop "kind")) (← expression nodes unit (← field prop "value"))
    return .object props
  | "function" =>
    check ["name", "parameters", "body", "strict", "sourceText"]
    return .function (← optional Json.getStr? (← field j "name")) (← parameters j)
      (← statements nodes unit (← field j "body")) (← boolField j "strict")
      (← optional codeUnits (← field j "sourceText"))
  | "sequence" => check ["expressions"]; return .sequence (← exs "expressions")
  | "unary" => check ["operator", "argument"]; return .unary (← unaryOp (← stringField j "operator")) (← ex "argument")
  | "update" => check ["operator", "argument", "isPrefix"]; return .update (← updateOp (← stringField j "operator")) (← ex "argument") (← boolField j "isPrefix")
  | "binary" => check ["operator", "left", "right"]; return .binary (← binaryOp (← stringField j "operator")) (← ex "left") (← ex "right")
  | "logical" => check ["operator", "left", "right"]; return .logical (← logicalOp (← stringField j "operator")) (← ex "left") (← ex "right")
  | "assignment" => check ["operator", "left", "right"]; return .assignment (← assignmentOp (← stringField j "operator")) (← ex "left") (← ex "right")
  | "conditional" => check ["test", "consequent", "alternate"]; return .conditional (← ex "test") (← ex "consequent") (← ex "alternate")
  | "member" => check ["object", "property", "computed"]; return .member (← ex "object") (← ex "property") (← boolField j "computed")
  | "call" => check ["callee", "arguments"]; return .call (← ex "callee") (← exs "arguments")
  | "clockRead" => check ["integer", "callee", "argument"]; return .clockRead (← boolField j "integer") (← ex "callee") (← ex "argument")
  | "clockZero" => check []; return .clockZero
  | "construct" => check ["callee", "arguments"]; return .construct (← ex "callee") (← exs "arguments")
  | s => throw s!"Unsupported expression tag: {s}"

private def decodeStmt (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String Stmt := do
  let ex name := field j name >>= expression nodes unit
  let st name := field j name >>= statement nodes unit
  let optEx name := field j name >>= optional (expression nodes unit)
  let optSt name := field j name >>= optional (statement nodes unit)
  let check extra := keys j (baseKeys ++ extra)
  match ← stringField j "tag" with
  | "empty" => check []; return .empty
  | "expression" => check ["expression", "directive"]; return .expression (← ex "expression")
  | "block" => check ["body"]; return .block (← statements nodes unit (← field j "body"))
  | "variable" => check ["declarations"]; return .variable (← declarations nodes unit (← field j "declarations"))
  | "functionDeclaration" =>
    check ["name", "parameters", "body", "strict", "sourceText"]
    return .functionDeclaration (← stringField j "name") (← parameters j)
      (← statements nodes unit (← field j "body")) (← boolField j "strict")
      (← optional codeUnits (← field j "sourceText"))
  | "ifThenElse" => check ["test", "consequent", "alternate"]; return .ifThenElse (← ex "test") (← st "consequent") (← optSt "alternate")
  | "while" => check ["test", "body"]; return .while (← ex "test") (← st "body")
  | "doWhile" => check ["body", "test"]; return .doWhile (← st "body") (← ex "test")
  | "forLoop" =>
    check ["initial", "test", "update", "body"]
    return .forLoop (← optional (forInitial nodes unit) (← field j "initial"))
      (← optEx "test") (← optEx "update") (← st "body")
  | "forIn" => check ["binding", "object", "body"]; return .forIn (← forBinding nodes unit (← field j "binding")) (← ex "object") (← st "body")
  | "return" => check ["value"]; return .return (← optEx "value")
  | "throw" => check ["value"]; return .throw (← ex "value")
  | "break" => check ["label"]; return .break (← optional Json.getStr? (← field j "label"))
  | "continue" => check ["label"]; return .continue (← optional Json.getStr? (← field j "label"))
  | "labeled" => check ["label", "body"]; return .labeled (← stringField j "label") (← st "body")
  | "tryCatchFinally" =>
    check ["body", "handler", "finalizer"]
    let handler ← optional (fun h => do
      keys h ["name", "body"]
      return (← stringField h "name", ← statement nodes unit (← field h "body"))) (← field j "handler")
    return .tryCatchFinally (← st "body") handler (← optSt "finalizer")
  | s => throw s!"Unsupported statement tag: {s}"

private def decodeProgram (nodes : Array DecodedNode) (unit : Nat) (j : Json) : Except String Program := do
  keys j (baseKeys ++ ["body", "strict"])
  if (← stringField j "tag") != "program" then throw "Unknown program tag"
  return { body := ← statements nodes unit (← field j "body"), strict := ← boolField j "strict" }

private def decodeNode (nodes : Array DecodedNode) (units : Array Json) (j : Json) : Except String DecodedNode := do
  if (← natField j "id") != nodes.size then throw "AST node ID does not match its table index"
  let source ← field j "source"
  keys source ["unit", "start", "end", "line", "column", "endLine", "endColumn"]
  let unit ← natField source "unit"
  let some unitJson := units[unit]? | throw "AST source refers to absent compilation unit"
  let start ← natField source "start"
  let finish ← natField source "end"
  if start > finish || finish > (← natField unitJson "lengthUtf16") then throw "Invalid AST source range"
  for name in ["line", "column", "endLine", "endColumn"] do
    let _ ← natField source name
  let kind ← stringField j "kind"
  let value : DecodedSyntax ← match kind with
    | "expr" => DecodedSyntax.expression <$> decodeExpr nodes unit j
    | "stmt" => DecodedSyntax.statement <$> decodeStmt nodes unit j
    | "program" => DecodedSyntax.program <$> decodeProgram nodes unit j
    | s => .error s!"Unknown AST node kind: {s}"
  return { unit, value }

/-- Decode typed, acyclic AST syntax. Source correspondence remains a separate obligation. -/
def decodeArtifact (j : Json) : Except String DecodedArtifact := do
  if (← natField j "schemaVersion") != 2 || (← stringField j "schema") != "cookie-clicker-es5-ast-v2" then
    throw "Unsupported JavaScript AST schema"
  let clockAnnotated ← match field j "clockModel" with
    | .error _ => pure false
    | .ok value => do
      if (← value.getStr?) != "selected-unbounded-v1" then throw "Unknown source clock model"
      pure true
  let unitsJson ← arrayField j "units"
  let mut nodes := #[]
  for node in ← arrayField j "nodes" do
    if !clockAnnotated && ["clockRead","clockZero"].contains (← stringField node "tag") then
      throw "Clock annotation requires the selected unbounded-clock artifact marker"
    nodes := nodes.push (← decodeNode nodes unitsJson node)
  let mut units := #[]
  for unitJson in unitsJson do
    let index := units.size
    if (← natField unitJson "id") != index then throw "AST unit ID does not match its table index"
    let name ← stringField unitJson "name"
    let kind ← stringField unitJson "kind"
    if !["script", "inline-script", "html-handler", "literal-handler"].contains kind then throw "Unknown compilation unit kind"
    let root ← natField unitJson "root"
    let some node := nodes[root]? | throw "Compilation unit root is absent"
    if node.unit != index then throw "Compilation unit root belongs to another unit"
    let .program program := node.value | throw "Compilation unit root is not a program"
    units := units.push { name, kind, root, program }
  return { nodes, units, clockAnnotated }

end CookieClicker.JavaScript

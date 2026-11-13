import CookieClicker.JavaScriptParser

/-! Dynamic Function construction through the logical source parser.
Arguments convert to strings in native order. Parameter and body source are
parsed independently, then a source closure is allocated in global scope.
Recognized syntax errors are distinct from unsupported grammar or parser fuel
exhaustion. Native parser correspondence and legacy function reflection remain
separate requirements; no native parse result is used as a transition oracle.
-/
namespace CookieClicker.JavaScript.DynamicFunction

def parameterText : JSString := JSString.ofString "n"
def bodyText : JSString :=
  JSString.ofString "var plural, nplurals; nplurals=2;plural=(n!=1); return plural;"

def sourceText : JSString :=
  JSString.ofString "function anonymous(n\n) {\nvar plural, nplurals; nplurals=2;plural=(n!=1); return plural;\n}"

def sourceBody : List Stmt := [
  .variable [("plural",none),("nplurals",none)],
  .expression (.assignment .assign (.identifier "nplurals") (.literal (.number (Number.ofNat 2)))),
  .expression (.assignment .assign (.identifier "plural")
    (.binary .notEqual (.identifier "n") (.literal (.number Number.one)))),
  .return (some (.identifier "plural")) ]

private def allocate (machine : Machine) (parameters : List String) (program : Program)
    (text : JSString) : Machine :=
  let (scope,heap) := machine.heap.allocateEnvironment ⟨.object machine.globalObject false, none⟩
  checked { machine with heap } (allocateFunction { machine with heap }
      ⟨some "anonymous",parameters,program.body,scope,program.strict,some text⟩) fun (value,next) =>
    match value with
    | .object id => checked next (checkedObject next.heap id) fun object =>
      let object := setOwnProperty object (JSString.ofString "name")
        (.data (.string (JSString.ofString "anonymous")) false false true)
      let object := setOwnProperty object (JSString.ofString "length")
        (.data (.number (Number.ofNat parameters.length)) false false true)
      -- allocateFunction retains the unresolved active caller/arguments fields.
      checked next (replaceObject next.heap id object) fun heap => result { next with heap } value
    | _ => fail next (.fault (.invalidContinuation "Dynamic Function did not allocate a function"))

private def parseFailure (machine : Machine) (error : Lexer.Error) : Machine :=
  match error.kind with
  | .syntax => fail machine (.exception "SyntaxError" error.message)
  | .unsupported => fail machine (.unresolved (.unsupportedSyntax
      ("Dynamic Function parser: " ++ error.message)))
  | .exhausted => fail machine (.unresolved (.unsupportedSyntax "Dynamic Function parser fuel exhausted"))

private def compile (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  let texts := continuation.locals.filterMap fun value =>
    match value with | .string text => some text | _ => none
  if texts.length != continuation.locals.length then
    fail machine (.fault (.invalidContinuation "Dynamic Function expected converted string arguments"))
  else
    let body := texts.getLast?.getD []
    let parameters := List.intercalate (JSString.ofString ",") texts.dropLast
    match Parser.parseFormalParameters parameters with
    | .error error => parseFailure machine error
    | .ok names => match Parser.parseFunctionBody body with
      | .error error => parseFailure machine error
      | .ok program =>
        if !Parser.formalParametersValid program.strict names then
          fail machine (.exception "SyntaxError" "Invalid formal parameters for function strictness")
        else
          let text := JSString.ofString "function anonymous(" ++ parameters ++
            JSString.ofString "\n) {\n" ++ body ++ JSString.ofString "\n}"
          allocate machine names program text

private def nextArgument (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  if continuation.locals.length ≥ continuation.arguments.length then compile machine continuation
  else
    let value := continuation.arguments[continuation.locals.length]?.getD .undefined
    if isObject value then primitiveThen machine value "string" (.builtin continuation)
    else checked machine (toJSString value) fun text =>
      { machine with control := .resumeBuiltin continuation (.string text) }

def dispatch (machine : Machine) (thisValue : Value) (arguments : List Value)
    (_construct : Bool) : Machine :=
  nextArgument machine {
    id := ⟨"DynamicFunction","Function"⟩
    phase := "argument"
    thisValue, arguments }

def resume (machine : Machine) (continuation : BuiltinContinuation) (value : Value) : Machine :=
  if continuation.phase != "argument" then
    fail machine (.unresolved (.builtinContinuation continuation value))
  else checked machine (toJSString value) fun text =>
    nextArgument machine { continuation with locals := continuation.locals ++ [.string text] }

end CookieClicker.JavaScript.DynamicFunction

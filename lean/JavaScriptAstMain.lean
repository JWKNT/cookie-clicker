import CookieClicker.JavaScriptDecode
import CookieClicker.JavaScriptCssDecode
import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptBrowserRuntime
import CookieClicker.JavaScriptSeedrandomCapturedDrawEvaluation

open Lean CookieClicker.JavaScript

private def encodeValue : Value → Json
  | .undefined => Json.mkObj [("type", toJson "undefined")]
  | .null => Json.mkObj [("type", toJson "null")]
  | .boolean value => Json.mkObj [("type", toJson "boolean"), ("value", toJson value)]
  | .number bits | .timestamp (.native bits) => Json.mkObj [("type", toJson "number"), ("bits", toJson bits.toNat.repr)]
  | .calendar q => Json.mkObj [("type",toJson "calendar"),("numerator",toJson (toString q.num)),("denominator",toJson q.den)]
  | .timestamp (.extended time) => Json.mkObj [("type", toJson "timestamp"),
      ("numerator",toJson (toString time.normalize.numerator)),("scale",toJson time.normalize.scale)]
  | .textIndex value => Json.mkObj [("type",toJson "number"),("bits",toJson (Number.ofInt value).toNat.repr)]
  | .timestampText units => Json.mkObj [("type",toJson "string"),("units",toJson (units.toList.map UInt16.toNat))]
  | .string units => Json.mkObj [("type", toJson "string"), ("units", toJson (units.map UInt16.toNat))]
  | .object id => Json.mkObj [("type", toJson "object"), ("id", toJson id)]

private def encodeCanvasColor (color : CssColor.RGBA) : Json :=
  toJson ([color.red,color.green,color.blue,color.alpha].map UInt8.toNat)

private def encodeCanvasTransform (transform : CanvasDeferred.State) : Json :=
  transform.known.map (fun matrix => toJson (CanvasMatrix.values matrix |>.map (fun bits => toString bits.toNat)))
    |>.getD Json.null

private def encodeCanvasOperation (operation : CanvasDeferred.Operation) : Json :=
  let (name,bits) := match operation with
    | .translate x y => ("translate",[x,y])
    | .scale x y => ("scale",[x,y])
    | .rotate radians => ("rotate",[radians])
    | .transform matrix => ("transform",CanvasMatrix.values matrix)
    | .setTransform matrix => ("setTransform",CanvasMatrix.values matrix)
    | .resetTransform => ("resetTransform",[])
  Json.mkObj [("name",toJson name),("bits",toJson (bits.map (fun value => toString value.toNat)))]

private def encodeCanvasHistory (transform : CanvasDeferred.State) : Json :=
  Json.arr (transform.history.map encodeCanvasOperation).toArray

private def encodeImageArguments : BrowserCanvasState.ImageArguments → Json
  | .at x y => Json.mkObj [("overload",toJson 3),("bits",toJson ([x,y].map (fun n => toString n.toNat)))]
  | .sized x y w h => Json.mkObj [("overload",toJson 5),("bits",toJson ([x,y,w,h].map (fun n => toString n.toNat)))]
  | .cropped sx sy sw sh dx dy dw dh => Json.mkObj [("overload",toJson 9),
      ("bits",toJson ([sx,sy,sw,sh,dx,dy,dw,dh].map (fun n => toString n.toNat)))]

private def encodeImageSnapshot : BrowserCanvasState.ImageSnapshot → Json
  | .asset asset => Json.mkObj [("kind",toJson "asset"),("path",toJson asset.path),("sha256",toJson asset.sha256),
      ("width",toJson asset.width),("height",toJson asset.height),
      ("sourceUnits",toJson (asset.sourceURL.map UInt16.toNat)),("originClean",Json.null)]
  | .canvas width height alpha commands => Json.mkObj [("kind",toJson "canvas"),
      ("width",toJson width),("height",toJson height),("alpha",toJson alpha),
      ("capturedCommands",toJson commands.length),("originClean",Json.null)]

/-- Internal command diagnostics, never a policy observation or pixel oracle. -/
private def encodeCanvasCommand : BrowserCanvasState.Command → Json
  | .clearRect drawing x y width height => Json.mkObj [
      ("kind",toJson "clearRect"),
      ("matrix",encodeCanvasTransform drawing.transform),
      ("transformHistory",encodeCanvasHistory drawing.transform),
      ("rectangle",toJson ([x,y,width,height].map (fun bits => toString bits.toNat)))]
  | .fillRect drawing canvasWidth canvasHeight alpha x y width height => Json.mkObj [
      ("kind",toJson "fillRect"),("canvasWidth",toJson canvasWidth),
      ("canvasHeight",toJson canvasHeight),("alpha",toJson alpha),
      ("matrix",encodeCanvasTransform drawing.transform),
      ("transformHistory",encodeCanvasHistory drawing.transform),
      ("rectangle",toJson ([x,y,width,height].map (fun bits => toString bits.toNat))),
      ("fields",Json.mkObj (drawing.fields.map fun (name,value) => (name,encodeValue value))),
      ("fill",encodeCanvasColor drawing.colors.fill),("stroke",encodeCanvasColor drawing.colors.stroke),
      ("shadow",encodeCanvasColor drawing.colors.shadow)]
  | .drawImage drawing canvasWidth canvasHeight alpha source arguments => Json.mkObj [
      ("kind",toJson "drawImage"),("canvasWidth",toJson canvasWidth),("canvasHeight",toJson canvasHeight),
      ("alpha",toJson alpha),("matrix",encodeCanvasTransform drawing.transform),
      ("transformHistory",encodeCanvasHistory drawing.transform),("source",encodeImageSnapshot source),
      ("arguments",encodeImageArguments arguments),
      ("fields",Json.mkObj (drawing.fields.map fun (name,value) => (name,encodeValue value)))]

/-- A fixed diagnostic projection of production state. It reads only own data
properties; it never invokes getters, reads RNG internals, or becomes policy input. -/
private def projectionOwnValue (machine : Machine) (id : ObjectId) (name : String) : Option Value := do
  let object ← machine.heap.object? id
  match ownProperty object (JSString.ofString name) with
  | some (.data value _ _ _) => some value
  | _ => none

private def projectionValue (machine : Machine) (value : Value) : Json :=
  match value with
  | .object id =>
    let metadata := match machine.heap.object? id with
      | some object =>
        [("prototype",object.prototype.map toJson |>.getD Json.null),
          ("propertiesComplete",toJson object.propertiesComplete)] ++
        (match object.kind with
        | .function closure => [
            ("kind",toJson "source-function"),("scope",toJson closure.scope),
            ("parameters",toJson closure.parameters),("strict",toJson closure.strict),
            ("sourceTextUnits",closure.sourceText.map (fun text => toJson (text.map UInt16.toNat)) |>.getD Json.null)]
        | .array => [("kind",toJson "array")]
        | .ordinary => [("kind",toJson "ordinary")]
        | _ => [("kind",toJson "other")])
      | none => [("kind",toJson "absent-object")]
    Json.mkObj ([("type",toJson "object"),("id",toJson id)] ++ metadata)
  | value => encodeValue value

private def projectionFields (machine : Machine) (id : ObjectId) (names : List String) : Json :=
  Json.mkObj (names.map fun name => (name, match machine.heap.object? id with
    | none => Json.mkObj [("state",toJson "absent-object")]
    | some object => match ownProperty object (JSString.ofString name) with
      | none => Json.mkObj [("state",toJson "absent")]
      | some (.accessor _ _ _ _) => Json.mkObj [("state",toJson "accessor-not-invoked")]
      | some (.data value writable enumerable configurable) => Json.mkObj [
          ("state",toJson "data"),("value",projectionValue machine value),
          ("writable",toJson writable),("enumerable",toJson enumerable),("configurable",toJson configurable)]))

private def projectionArray (machine : Machine) (game : ObjectId) (name : String)
    (limit : Nat) (fields : List String) : Json :=
  match projectionOwnValue machine game name with
  | some (.object id) => match machine.heap.object? id with
    | some object =>
      let entries := object.properties.filterMap fun property => do
        let text := String.ofList (property.name.map fun unit => Char.ofNat unit.toNat)
        let index ← text.toNat?
        if toString index != text || index ≥ limit then none else
        let .data (.object entry) _ _ _ := property.descriptor | none
        some (Json.mkObj [("index",toJson index),("object",projectionValue machine (.object entry)),
          ("fields",projectionFields machine entry fields)])
      Json.mkObj [("object",toJson id),("entries",Json.arr entries.toArray),("indexLimit",toJson limit)]
    | none => Json.null
  | _ => Json.null

private def projectionScopeChain : Nat → Machine → EnvId → List Json
  | 0,_,id => [Json.mkObj [("id",toJson id),("state",toJson "diagnostic-depth-limit")]]
  | fuel+1,machine,id =>
    match machine.heap.environment? id with
    | none => [Json.mkObj [("id",toJson id),("state",toJson "absent-environment")]]
    | some environment =>
      let record := match environment.record with
        | .declarative bindings => [
            ("kind",toJson "declarative"),("bindingNames",toJson (bindings.map (·.name))),
            ("selectedBindings",Json.mkObj ((bindings.filter (fun binding => ["Game","window"].contains binding.name)).map fun binding =>
              (binding.name,Json.mkObj [("value",encodeValue binding.value),("mutable",toJson binding.mutable),
                ("deletable",toJson binding.deletable),("initialized",toJson binding.initialized)])))]
        | .object object provideThis => [
            ("kind",toJson "object"),("object",toJson object),("provideThis",toJson provideThis),
            ("ownBindingNamesUnits",toJson (((machine.heap.object? object).map (fun object => object.properties.map (fun property => property.name.map UInt16.toNat))).getD [])),
            ("selectedBindings",projectionFields machine object ["Game","window"])]
      Json.mkObj ([("id",toJson id),("outer",environment.outer.map toJson |>.getD Json.null)] ++ record) ::
        (environment.outer.map (projectionScopeChain fuel machine) |>.getD [])

private def projectionScopes (machine : Machine) (game : ObjectId) : Json :=
  let helperNames := ["Has","CalculateGains","Logic","Loop","Earn","ComputeCps","magicCpS",
    "GetTieredCpsMult","eff","auraMult","GetHeavenlyMultiplier","hasBuff","runModHookOnValue","mouseCps","computeLumpTimes"]
  let helpers := helperNames.filterMap fun name =>
    (projectionOwnValue machine game name).map (fun value => ("Game."++name,value))
  let buildings := match projectionOwnValue machine game "ObjectsById" with
    | some (.object array) => (List.range 20).flatMap fun index =>
      match projectionOwnValue machine array (toString index) with
      | some (.object building) => ["cps","baseCps"].filterMap fun name =>
        (projectionOwnValue machine building name).map fun value =>
          ("Game.ObjectsById["++toString index++"]."++name,value)
      | _ => []
    | _ => []
  let closures := (helpers++buildings).filterMap fun (label,value) => do
    let .object object := value | none
    let objectValue ← machine.heap.object? object
    let .function closure := objectValue.kind | none
    some (label,object,closure.scope)
  let roots := (closures.map (fun (_,_,scope) => scope)).eraseDups
  Json.mkObj [
    ("sourceClosures",Json.arr (closures.toArray.map fun (label,object,scope) =>
      Json.mkObj [("label",toJson label),("object",toJson object),("scope",toJson scope)])),
    ("chains",Json.arr (roots.toArray.map fun scope =>
      Json.mkObj [("scope",toJson scope),("environments",toJson (projectionScopeChain 128 machine scope))])),
    ("otherBindingValuesExported",toJson false)]

private def productionProjection (machine : Machine) : Json :=
  match projectionOwnValue machine machine.globalObject "Game" with
  | some (.object game) => Json.mkObj [
      ("diagnosticOnly",toJson true),("initializationComplete",toJson false),
      ("globalObject",toJson machine.globalObject),("gameObject",toJson game),
      ("lexicalScopes",projectionScopes machine game),
      ("fields",projectionFields machine game ["Objects","ObjectsById","Upgrades","UpgradesById","Achievements","AchievementsById",
        "cookies","cookiesEarned","handmadeCookies","cookieClicks","lastClick","BigCookieState","mouseX","mouseY","onMenu","cookiesPs","cookiesPsRaw","cookiesPsRawHighest","globalCpsMult","cpsSucked",
        "UpgradesOwned","AchievementsOwned","milkProgress","prestige","heavenlyPower","ascensionMode","ascensions",
        "season","elderWrath","dragonLevel","dragonAura","dragonAura2","santaLevel","heralds","effs","buffs",
        "T","drawT","ready","promptOn","promptNoClose","promptOptionsN","fps","recalculateGains","CalculateGains","Logic","Loop","Earn","Has","HasAchiev","hasAura",
        "auraMult","hasGod","eff","GetTieredCpsMult","GetHeavenlyMultiplier","GetMilk","GetMilkMultiplier",
        "ComputeCps","magicCpS","hasBuff","runModHookOnValue","mouseCps","computeLumpTimes"]),
      ("dragonAuras",projectionArray machine game "dragonAuras" 1 ["id","name"]),
      ("productionHooks",match projectionOwnValue machine game "modHooks" with
        | some (.object hooks) => Json.mkObj [
            ("cps",projectionArray machine hooks "cps" 1024 []),
            ("cookiesPerClick",projectionArray machine hooks "cookiesPerClick" 1024 [])]
        | _ => Json.null),
      ("buildings",projectionArray machine game "ObjectsById" 20
        ["id","name","amount","bought","free","level","baseCps","storedCps","storedTotalCps","totalCookies",
          "cps","tieredUpgrades","synergies","fortune","minigameLoaded","minigame"]),
      ("upgrades",projectionArray machine game "UpgradesById" 2048
        ["id","name","bought","unlocked","pool","power","tier","buildingTie"])]
  | _ => Json.mkObj [("diagnosticOnly",toJson true),("state",toJson "Game-own-data-object-absent")]

private def errorDetails (machine : Machine) (value : Value) : List (String × Json) :=
  match value with
  | .object id => match machine.heap.object? id with
    | some object => match object.kind with
      | .error name =>
        let message := match ownProperty object (JSString.ofString "message") with
          | some (.data (.string units) _ _ _) => units.map UInt16.toNat
          | _ => []
        [("errorName", toJson name), ("errorMessageUnits", toJson message)]
      | _ => []
    | none => []
  | _ => []

private def completedNormally (machine : Machine) : Bool :=
  match status machine with
  | .completion (.normal _) | .value _ => true
  | _ => false

private def controlLabel : Control → String
  | .expression _ => "expression" | .statement _ => "statement"
  | .expressionResult _ => "expression-result" | .completion _ => "completion"
  | .getValue _ => "get-value" | .putValue _ _ => "put-value"
  | .invoke _ _ _ _ => "invoke" | .toPrimitive _ _ => "to-primitive"
  | .declarationScan _ _ _ _ => "declaration-scan"
  | .declarationVariables _ _ _ => "declaration-variables"
  | .declarationFunctions _ _ => "declaration-functions" | .forInNext _ => "for-in-next"
  | .resumeBuiltin continuation _ => "builtin:" ++ continuation.id.namespaceName ++ "." ++ continuation.id.name ++ ":" ++ continuation.phase
  | .unresolved _ => "unresolved" | .fault _ => "fault" | .idle => "idle"

private def diagnosticText (text : JSString) : String :=
  String.ofList ((text.take 80).map fun unit => Char.ofNat unit.toNat)

/-- Source syntax only: no environment bindings, hidden RNG state, or heap values. -/
private def expressionSummary : Nat → CookieClicker.JavaScript.Expr → String
  | 0, _ => "…"
  | _, .identifier name => name
  | _, .this => "this"
  | _, .literal (.string text) => "\"" ++ diagnosticText text ++ "\""
  | _, .literal _ => "literal"
  | n+1, .member object property computed => expressionSummary n object ++
      (if computed then "[" else ".") ++ expressionSummary n property ++ (if computed then "]" else "")
  | n+1, .call callee _ => expressionSummary n callee ++ "(…)"
  | n+1, .binary operator left right => "(" ++ expressionSummary n left ++ " " ++ reprStr operator ++ " " ++ expressionSummary n right ++ ")"
  | n+1, .assignment operator left right => expressionSummary n left ++ " " ++ reprStr operator ++ " " ++ expressionSummary n right
  | n+1, .update operator operand _ => reprStr operator ++ " " ++ expressionSummary n operand
  | n+1, .unary operator operand => reprStr operator ++ " " ++ expressionSummary n operand
  | _, _ => "expression"

private def statementSummary : Stmt → String
  | .expression expression => expressionSummary 5 expression
  | .variable declarations => "var " ++ String.intercalate "," (declarations.map Prod.fst)
  | .ifThenElse test _ _ => "if " ++ expressionSummary 5 test
  | .forLoop _ test _ _ => "for " ++ (test.map (expressionSummary 5) |>.getD "")
  | .return _ => "return"
  | .functionDeclaration name _ _ _ _ => "function " ++ name
  | _ => "statement"

private def frameDiagnostic : Frame → Option Json
  | .statementList remaining _ =>
    some (Json.mkObj [("frame",toJson "statements"),("remainingCount",toJson remaining.length),
      ("nextSourceStatements",toJson ((remaining.take 3).map statementSummary))])
  | .whileTest test _ _ _ | .whileBody test _ _ _ =>
    some (Json.mkObj [("frame",toJson "while"),("test",toJson (expressionSummary 5 test))])
  | .forTest test _ _ _ _ | .forBody test _ _ _ _ | .forUpdate test _ _ _ _ =>
    some (Json.mkObj [("frame",toJson "for"),("test",toJson (test.map (expressionSummary 5) |>.getD ""))])
  | .forInBody state | .forInAssigned state | .forInReference state _ =>
    some (Json.mkObj [("frame",toJson "for-in"),("remainingKeys",toJson state.remaining.length)])
  | .builtin continuation | .nativeCallback continuation _ =>
    some (Json.mkObj [("frame",toJson "builtin"),("name",toJson (continuation.id.namespaceName ++ "." ++ continuation.id.name)),("phase",toJson continuation.phase)])
  | _ => none

private def runBrowserPrograms (fuel : Nat) (captureAfter : Option Nat) (inspectCapture : Bool)
    (captureSeed : JSString) (evaluateCapture : Bool) :
    Browser.State → List Program → Nat → List Json → Browser.State × Nat × Nat × List Json
  | state, [], index, diagnostics => (state, index, index, diagnostics)
  | state, program :: rest, index, diagnostics =>
    let finished := BrowserRuntime.run fuel (Browser.startProgram state program)
    if !completedNormally finished.machine then (finished, index + 1, index, diagnostics)
    else
      let finished := if captureAfter == some index then
        Browser.checked finished (Browser.captureSeedrandom finished) id else finished
      if !completedNormally finished.machine then (finished, index + 1, index + 1, diagnostics)
      else
        let diagnostics := if inspectCapture && captureAfter == some index then
          let report := SeedrandomCapturedDraw.captureReport finished captureSeed
          let report := if evaluateCapture then report.setObjVal! "drawEvaluationSamples"
            (SeedrandomCapturedDrawEvaluation.samples finished captureSeed) else report
          diagnostics ++ [report] else diagnostics
        runBrowserPrograms fuel captureAfter inspectCapture captureSeed evaluateCapture finished rest (index + 1) diagnostics

private def oneProgram (requireClockAnnotations : Bool) (json : Json) : Except String Program := do
  let ast ← decodeArtifact json
  if requireClockAnnotations && !ast.clockAnnotated then
    throw "Selected unbounded source execution requires annotated clock artifacts"
  if ast.units.size != 1 then throw "Execution fixture requires exactly one compilation unit per program"
  let some unit := ast.units[0]? | throw "Missing execution fixture unit"
  return unit.program

private def utf16Units (json : Json) : Except String JSString := do
  let units ← (← json.getArr?).toList.mapM Json.getNat?
  if units.any (· > 65535) then throw "Initial HTML has a value outside UTF16 code units"
  return units.map UInt16.ofNat

/-- Explicit diagnostic environment data for native getters. These values are
fixture setup, not source actions or policy capabilities. Unspecified object
members stay unresolved and supplied property order is retained. -/
private def fixtureValue : Nat → Machine → Json → Except String (Value × Machine)
  | 0, _, _ => throw "Diagnostic Window data exceeds nesting limit"
  | fuel + 1, machine, json => do
    let kind ← (← json.getObjVal? "kind").getStr?
    if kind == "null" then return (.null,machine)
    if kind == "boolean" then return (.boolean (← (← json.getObjVal? "value").getBool?),machine)
    if kind == "string" then return (.string (← utf16Units (← json.getObjVal? "units")),machine)
    if kind == "number" then
      let spelling ← (← json.getObjVal? "bits").getStr?
      let some bits := spelling.toNat? | throw "Invalid fixture binary64 bits"
      if bits ≥ 2^64 || bits.repr != spelling then throw "Noncanonical fixture binary64 bits"
      return (.number (UInt64.ofNat bits),machine)
    let propertyResult : Except String (List OwnProperty × Machine) := if kind == "object" then do
        (← (← json.getObjVal? "properties").getArr?).toList.foldlM (fun (properties,machine) entry => do
          let name ← (← entry.getObjVal? "name").getStr?
          let (value,machine) ← fixtureValue fuel machine (← entry.getObjVal? "value")
          return (properties ++ [⟨JSString.ofString name,.data value true true true⟩],machine)) (([] : List OwnProperty),machine)
      else if kind == "array" then do
        let items ← (← json.getObjVal? "items").getArr?
        let (properties,machine) ← items.toList.zipIdx.foldlM (fun (properties,machine) (item,index) => do
          let (value,machine) ← fixtureValue fuel machine item
          return (properties ++ [⟨JSString.ofString index.repr,.data value true true true⟩],machine)) (([] : List OwnProperty),machine)
        return (properties ++ [OwnProperty.mk (JSString.ofString "length") (.data (.number (Number.ofNat items.size)) true false false)],machine)
      else throw "Unsupported diagnostic Window data kind"
    let (properties,machine) ← propertyResult
    let (id,heap) := machine.heap.allocateObject {
      kind := if kind == "array" then .array else .ordinary
      prototype := if kind == "array" then machine.arrayPrototype else machine.objectPrototype
      properties, propertiesComplete := kind == "array" }
    return (.object id,{ machine with heap })

private def executeCase (j : Json) : Except String Json := do
  let requireClockAnnotations ← match j.getObjVal? "requireClockAnnotations" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let program ← oneProgram requireClockAnnotations (← j.getObjVal? "ast")
  let fuel ← (← j.getObjVal? "fuel").getNat?
  if fuel > 10000000 then throw "Execution fixture fuel exceeds the runner budget"
  let standardLibrary ← match j.getObjVal? "standardLibrary" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let browserLibrary ← match j.getObjVal? "browserLibrary" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let randomInputs ← match j.getObjVal? "randomInputs" with
    | .ok value => value.getArr? >>= fun values => values.toList.mapM Json.getNat?
    | .error _ => pure []
  if randomInputs.any (· ≥ 2 ^ 53) then throw "Diagnostic random input is not a uniform53 index"
  let epochMilliseconds ← match j.getObjVal? "epochMilliseconds" with
    | .ok (.str text) => match text.toInt? with
      | some value => pure value
      | none => throw "Invalid diagnostic epoch milliseconds"
    | .ok value => value.getInt?
    | .error _ => pure 0
  let fixtureData ← match j.getObjVal? "fixtureWindowData" with
    | .ok value => value.getArr?
    | .error _ => pure #[]
  let fixtureStorage : BrowserStorageState.State ← match j.getObjVal? "fixtureStorage" with
    | .error _ => pure {}
    | .ok value => do
      let origin ← match (← (← value.getObjVal? "origin").getStr?) with
        | "enabled" => pure BrowserStorageState.OriginMode.enabled
        | "denied" => pure .denied
        | "unconfigured" => pure .unconfigured
        | _ => throw "Invalid fixture Storage origin mode"
      let quota ← match value.getObjVal? "quotaBytes" with
        | .error _ => pure BrowserStorageState.Quota.unconfigured
        | .ok bytes => pure (.bytes (← bytes.getNat?))
      pure { origin, quota }
  let fixtureCookieOrigin ← match j.getObjVal? "fixtureCookieOrigin" with
    | .error _ => pure BrowserCookieState.Origin.unconfigured
    | .ok value => match (← value.getStr?) with
      | "unconfigured" => pure BrowserCookieState.Origin.unconfigured
      | "file" => pure .file
      | "opaque" => pure .opaqueOrigin
      | _ => throw "Invalid fixture cookie origin"
  let loadedStylesheets ← match j.getObjVal? "loadedStylesheets" with
    | .error _ => pure none
    | .ok value => some <$> ((← value.getArr?).toList.mapM Css.decodeStylesheet)
  let fixturePageFocused ← match j.getObjVal? "fixturePageFocused" with
    | .error _ => pure none
    | .ok value => some <$> value.getBool?
  let fixtureWindowName ← match j.getObjVal? "fixtureWindowName" with
    | .error _ => pure none
    | .ok value => some <$> utf16Units value
  let fixtureResourceBaseURL ← match j.getObjVal? "fixtureResourceBaseURLUnits" with
    | .error _ => pure none
    | .ok value => some <$> utf16Units value
  let diagnosticProduction ← match j.getObjVal? "diagnosticProduction" with
    | .ok value => value.getBool?
    | .error _ => pure false
  if diagnosticProduction && !browserLibrary then throw "Production diagnostics require browserLibrary"
  let diagnosticCanvas ← match j.getObjVal? "diagnosticCanvas" with
    | .ok value => value.getBool?
    | .error _ => pure false
  if diagnosticCanvas && !browserLibrary then throw "Canvas diagnostics require browserLibrary"
  let initialHtml ← match j.getObjVal? "initialHtmlUnits" with
    | .ok value => some <$> utf16Units value
    | .error _ => pure none
  let followups ← match j.getObjVal? "followupPrograms" with
    | .ok value => (← value.getArr?).toList.mapM (oneProgram requireClockAnnotations)
    | .error _ => pure []
  let postTaskStages ← match j.getObjVal? "postTaskStages" with
    | .error _ => pure []
    | .ok value => (← value.getArr?).toList.mapM fun stage => do
      let program ← oneProgram requireClockAnnotations (← stage.getObjVal? "ast")
      let count ← (← stage.getObjVal? "taskBudget").getNat?
      if count > 10000 then throw "Post-task diagnostic task count exceeds budget"
      pure (program,count)
  if postTaskStages.length > 100 then throw "Post-task diagnostic stage count exceeds budget"
  let captureAfter ← match j.getObjVal? "captureSeedrandomAfter" with
    | .ok value => some <$> value.getNat?
    | .error _ => pure none
  let evaluateCapture ← match j.getObjVal? "seedrandomCaptureDrawEvaluation" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let sourceScripts ← match j.getObjVal? "sourceScripts" with
    | .ok value => (← value.getArr?).toList.mapM fun script => do
      let path ← (← script.getObjVal? "path").getStr?
      let program ← oneProgram requireClockAnnotations (← script.getObjVal? "ast")
      pure (path,program)
    | .error _ => pure []
  let taskBudget ← match j.getObjVal? "taskBudget" with
    | .ok value => value.getNat?
    | .error _ => pure 0
  if taskBudget > 10000 then throw "Browser task count exceeds the diagnostic runner budget"
  let animationEventStages ← match j.getObjVal? "animationEventStages" with
    | .ok value => value.getNat?
    | .error _ => pure 0
  if animationEventStages > 10000 then throw "Animation event stage count exceeds the diagnostic runner budget"
  let selectionEventTasks ← match j.getObjVal? "selectionEventTasks" with
    | .ok value => value.getNat?
    | .error _ => pure 0
  if selectionEventTasks > 10000 then throw "Selection event task count exceeds the diagnostic runner budget"
  let afterAnimationProgram ← match j.getObjVal? "afterAnimationProgram" with
    | .ok value => some <$> oneProgram requireClockAnnotations value
    | .error _ => pure none
  let taskFuel ← match j.getObjVal? "taskFuel" with
    | .ok value => value.getNat?
    | .error _ => pure fuel
  if taskFuel > 100000000 then throw "Browser task fuel exceeds the diagnostic runner budget"
  if !browserLibrary && (initialHtml.isSome || !followups.isEmpty || captureAfter.isSome ||
      !postTaskStages.isEmpty || !sourceScripts.isEmpty || taskBudget != 0 || animationEventStages != 0 || selectionEventTasks != 0 || afterAnimationProgram.isSome || !fixtureData.isEmpty || fixtureStorage != {} || fixtureCookieOrigin != .unconfigured || loadedStylesheets.isSome || fixturePageFocused.isSome || fixtureWindowName.isSome || fixtureResourceBaseURL.isSome) then
    throw "Document initialization and ordered source programs require browserLibrary"
  if captureAfter.any (· > followups.length) then throw "Seedrandom capture boundary is outside the program list"
  let captureSeed ← match j.getObjVal? "seedrandomCaptureSeedUnits" with
    | .ok value => utf16Units value
    | .error _ => pure (JSString.ofString "captured-frame-fixture")
  let (final, browserFields) ← if browserLibrary then do
      let base := Browser.initial
      let initial : Browser.State := {
        base with
        randomInputs := randomInputs
        scripts := sourceScripts
        storage := fixtureStorage
        cookieOrigin := fixtureCookieOrigin
        stylesheets := loadedStylesheets.getD []
        stylesheetsConfigured := loadedStylesheets.isSome
        focus := { pageFocused := fixturePageFocused }
        windowName := fixtureWindowName
        resourceBaseURL := fixtureResourceBaseURL
        machine := { base.machine with epochMilliseconds := epochMilliseconds } }
      let (fixtureWindowData,machine) ← fixtureData.toList.foldlM (fun (values,machine) entry => do
        let name ← (← entry.getObjVal? "name").getStr?
        if !["navigator","location","screen","document","devicePixelRatio","innerWidth","innerHeight","outerWidth","outerHeight"].contains name then
          throw "Unsupported diagnostic Window override"
        let (value,machine) ← fixtureValue 64 machine (← entry.getObjVal? "value")
        return (values ++ [(JSString.ofString name,value)],machine)) ([],initial.machine)
      let initial := { initial with machine, fixtureWindowData }
      let initialized : Checked Browser.State := match initialHtml with
        | none => .ok initial
        | some html => Browser.initializeDocument initial html
      let (finished, executed, completed, seedrandomCaptureDiagnostics) := match initialized with
        | .error failure => (Browser.fail initial failure, 0, 0, [])
        | .ok state => runBrowserPrograms fuel captureAfter diagnosticProduction captureSeed evaluateCapture state (program :: followups) 0 []
      let finished := (List.range selectionEventTasks).foldl (fun state _ =>
        if completedNormally state.machine then BrowserRuntime.run taskFuel (BrowserTextSelection.fireNextTask state)
        else state) finished
      -- Explicit diagnostic rendering-event stages. They do not choose a
      -- native frame cadence or advance the mathematical clock.
      let finished := (List.range animationEventStages).foldl (fun state _ =>
        if completedNormally state.machine then BrowserRuntime.run taskFuel (BrowserAnimation.beginDispatch state)
        else state) finished
      let finished := match afterAnimationProgram with
        | some program => if completedNormally finished.machine then
            BrowserRuntime.run fuel (Browser.startProgram finished program) else finished
        | none => finished
      let finished := if completedNormally finished.machine then BrowserRuntime.runTasks taskBudget taskFuel finished else finished
      let (finished,postTaskStagesCompleted) := postTaskStages.foldl (fun (state,count) (program,tasks) =>
        if !completedNormally state.machine then (state,count) else
        let state := BrowserRuntime.run taskFuel (Browser.startProgram state program)
        if !completedNormally state.machine then (state,count) else
        let state := BrowserRuntime.runTasks tasks taskFuel state
        (state,if completedNormally state.machine then count + 1 else count)) (finished,0)
      let rectangles := if !diagnosticProduction then Json.null else Json.arr (["bigCookie","product0","statsButton"].toArray.map fun name =>
        let node := ((Browser.subtree finished finished.document).toOption.getD []).find? (fun id =>
          (finished.nodes[id]?).any (fun node => Browser.getAttribute node "id" == some (JSString.ofString name)))
        let description := match node with
          | none => Json.mkObj [("status",toJson "absent")]
          | some id => match BrowserLayout.rectangle finished id with
            | .error failure => Json.mkObj [("status",toJson "unresolved"),("detail",toJson (reprStr failure))]
            | .ok box => Json.mkObj [("status",toJson "known"),("x",toJson box.x),("y",toJson box.y),
              ("width",toJson box.width),("height",toJson box.height)]
        Json.mkObj [("id",toJson name),("rectangle",description)])
      let requestedNode : Option Browser.Node := match finished.machine.control with
        | .unresolved (.builtin _ (.object object) _ _) =>
          finished.nodes.toList.find? (fun (node : Browser.Node) => node.object == object)
        | _ => none
      let nodeDiagnostic := match requestedNode with
        | none => Json.null
        | some node => Json.mkObj [
            ("tag",toJson (match node.kind with | .element tag => tag | .document => "#document" | _ => "#node")),
            ("idUnits",toJson (((Browser.getAttribute node "id").getD []).map UInt16.toNat)),
            ("classUnits",toJson (((Browser.getAttribute node "class").getD []).map UInt16.toNat)),
            ("styleUnits",toJson (((Browser.getAttribute node "style").getD []).map UInt16.toNat))]
      pure (finished.machine, [("browserLibrary", Json.bool true), ("nodeCount", toJson finished.nodes.size),
        ("diagnosticCanvas", if !diagnosticCanvas then Json.null else
          Json.arr ((finished.nodes.toList.filter (fun node => node.canvasContext.isSome)).map (fun node =>
            Json.mkObj [("matrix",encodeCanvasTransform node.canvasDrawing.transform),
              ("transformHistory",encodeCanvasHistory node.canvasDrawing.transform),
              ("saved",toJson node.canvasDrawing.saved.length),
              ("commands",toJson node.canvasDrawing.commands.length),
              ("commandRecords",Json.arr (node.canvasDrawing.commands.map encodeCanvasCommand).toArray)])).toArray),
        ("diagnosticRectangles",rectangles),
        ("seedrandomCaptureDiagnostics",toJson seedrandomCaptureDiagnostics),
        ("diagnosticContinuation", if !diagnosticProduction then Json.null else
          match status finished.machine with
          | .unresolved _ => Json.mkObj [
              ("builtinStep",toJson (reprStr (status (Builtins.builtinStep finished.machine)))),
              ("browserStep",toJson (reprStr (status (BrowserRuntime.step finished).machine)))]
          | _ => Json.null),
        ("unresolvedNodeTarget",nodeDiagnostic),
        ("timerCount", toJson finished.timers.length), ("randomInputsRemaining", toJson finished.randomInputs.length),
        ("timestampMixkeyActivations",toJson finished.timestampMixkeyActivations),
        ("resourceRequestCount", toJson finished.resourceRequests.length),
        ("resourceRequests", Json.arr (finished.resourceRequests.toArray.map (fun request =>
          Json.mkObj [("kind", toJson request.kind), ("sourceUnits", toJson (request.source.map UInt16.toNat)),
            ("node", toJson request.node), ("order", toJson request.order)]))),
        ("resourceTaskCount", toJson finished.resourceTasks.length),
        ("consoleEvents", Json.arr (finished.consoleEvents.map (fun event =>
          Json.mkObj [("type", toJson event.level), ("arguments", Json.arr (event.arguments.toArray.map encodeValue))]))),
        ("domEventCount", toJson finished.domEvents.size), ("taskBudget", toJson taskBudget),
        ("pendingAnimationEvents",toJson finished.animation.pending.length),
        ("pendingSelectionEvents",toJson finished.textSelection.pending.length),
        ("animationEventStages",toJson animationEventStages),
        ("fixtureCookieOrigin",toJson (match fixtureCookieOrigin with | .file => "file" | .opaqueOrigin => "opaque" | .unconfigured => "unconfigured")),
        ("loadedStylesheetCount",toJson finished.stylesheets.length),
        ("stylesheetsConfigured",toJson finished.stylesheetsConfigured),
        ("windowNameConfigured",toJson finished.windowName.isSome),
        ("resourceBaseURLConfigured",toJson finished.resourceBaseURL.isSome),
        ("taskFuel", toJson taskFuel),
        ("activeResourcePhase", toJson (finished.activeResource.map (·.phase) |>.getD "")),
        ("activeResourceSourceUnits", toJson (finished.activeResource.map (fun active => active.task.request.source.map UInt16.toNat) |>.getD [])),
        ("postTaskStagesCompleted",toJson postTaskStagesCompleted),
        ("executedPrograms", toJson executed), ("completedPrograms", toJson completed),
        ("fuelPerProgram", toJson fuel)])
    else do
      let base := if standardLibrary then Builtins.standardMachine else emptyMachine
      let initial := startProgram { base with epochMilliseconds } program
      pure (if standardLibrary then Builtins.run fuel initial else run fuel initial, [])
  let fields := match status final with
    | .completion (.normal value) => [("status", toJson "complete"), ("value", encodeValue (value.getD .undefined))]
    | .completion (.throw value) => [("status", toJson "throw"), ("value", encodeValue value)] ++ errorDetails final value
    | .completion other => [("status", toJson "abrupt"), ("detail", toJson (reprStr other))]
    | .value value => [("status", toJson "complete"), ("value", encodeValue value)]
    | .unresolved request => [("status", toJson "unresolved"), ("detail", toJson (reprStr request))]
    | .fault fault => [("status", toJson "fault"), ("detail", toJson (reprStr fault))]
    | .running => [("status", toJson "fuel-exhausted")]
    | .idle => [("status", toJson "idle")]
  let diagnosticControl ← match j.getObjVal? "diagnosticControl" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let productionFields := if diagnosticProduction then [("productionProjection",productionProjection final)] else []
  let diagnostics := if diagnosticControl then [("sourceControl",toJson (match final.control with
      | .expression expression => expressionSummary 5 expression
      | .getValue reference | .putValue reference _ => match reference.base with
        | .environment _ name => "binding " ++ name
        | .property _ name => "property " ++ diagnosticText name
        | .unresolvable name => "unresolved name " ++ name
      | _ => controlLabel final.control)),
    ("sourceLoopFrames",Json.arr ((final.continuation.filterMap frameDiagnostic).toArray))] else []
  return Json.mkObj (fields ++ browserFields ++ diagnostics ++ productionFields ++ [("javascriptSemanticsVerified", Json.bool false),
    ("machineControl", toJson (controlLabel final.control)), ("continuationDepth", toJson final.continuation.length),
    ("epochMilliseconds", toJson (toString epochMilliseconds)), ("calendarTimeZone", toJson "UTC"),
    ("fixtureWindowDataCount", toJson fixtureData.size)])

/-- Default mode decodes syntax. --execute runs explicit one-unit test fixtures. -/
def main (args : List String) : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  if args == ["--execute"] then
    match Json.parse input >>= Json.getArr? >>= (fun cases => cases.mapM executeCase) with
    | .error error => (← IO.getStderr).putStrLn error; return 1
    | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0
  if !args.isEmpty then
    (← IO.getStderr).putStrLn "Expected no arguments or --execute"
    return 1
  match Json.parse input >>= decodeArtifact with
  | .error error => (← IO.getStderr).putStrLn error; return 1
  | .ok ast =>
    let output := Json.mkObj [
      ("decoded", Json.bool true), ("nodes", toJson ast.nodes.size),
      ("units", toJson ast.units.size),
      ("unitRoots", toJson (ast.units.map fun unit => unit.root)),
      ("javascriptSemanticsVerified", Json.bool false)]
    (← IO.getStdout).putStrLn output.compress
    return 0

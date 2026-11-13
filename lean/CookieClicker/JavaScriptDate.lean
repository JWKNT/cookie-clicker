import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptCalendar

/-! UTC Date operations for the selected unbounded-clock extension.
Native-range timestamps retain binary64 bits. Beyond that prefix, date slots use
exact integer milliseconds and civil-year calculations use a separate rational
carrier. Ordinary economic arithmetic remains binary64. String-date parsing and
unimplemented API crossings fail explicitly; this module is not a full source
refinement proof.
-/
namespace CookieClicker.JavaScript.Date

private def arg (xs : List Value) (i : Nat) := xs[i]?.getD .undefined
private def key := JSString.ofString
private def bits (v : Value) := match v with | .number n => n | _ => Number.nan
private def invalid (m : Machine) (receiver : Value) (operation : String) :=
  fail m (.unresolved (.calendar operation [receiver]))

private def dateData (m : Machine) (receiver : Value) : Checked (ObjectId × Option Int) := do
  let .object id := receiver | throw (.exception "TypeError" "Date receiver is not a Date")
  let o ← checkedObject m.heap id
  match o.kind with
  | .date time => pure (id, if Number.isFinite time then some (Number.truncateInt time) else none)
  | .dateExtended time => pure (id, some time)
  | _ => throw (.exception "TypeError" "Date receiver is not a Date")

private def fromInt (time : Int) : Option Int := some time
private def clip (value : UInt64) : Option Int :=
  if !Number.isFinite value then none else some (Number.truncateInt value)

private def now (m : Machine) : Int := m.epochMilliseconds+m.elapsed.floor
private def timeValue : Option Int → Value
  | none => .number Number.nan
  | some time => .timestamp (ClockValue.Timestamp.ofInt time)
private def timeKind : Option Int → ObjectKind
  | none => .date Number.nan
  | some time => if time.natAbs ≤ 8640000000000000 then .date (Number.ofInt time)
      else .dateExtended time

private def allocate (m : Machine) (value : Option Int) : Machine :=
  let (id,heap) := m.heap.allocateObject { kind := timeKind value, prototype := m.datePrototype }
  result { m with heap } (.object id)

private def assign (m : Machine) (receiver : Value) (value : Option Int) : Machine :=
  checked m (dateData m receiver) fun (id,_) =>
    checked m (checkedObject m.heap id) fun o =>
      checked m (replaceObject m.heap id { o with kind := timeKind value }) fun heap =>
        result { m with heap } (timeValue value)

private def component (values : List Value) (index : Nat) (default : Int) : Int :=
  if index < values.length then
    match arg values index with
    | .calendar q => calendarTrunc q
    | value => Number.truncateInt (bits value)
  else default
private def validComponent : Value → Bool
  | .calendar _ => true
  | value => Number.isFinite (bits value)

private def fromArguments (values : List Value) : Option Int :=
  if values.any (fun v => !validComponent v) then none
  else
    let y := component values 0 0
    let y := if 0 ≤ y && y ≤ 99 then y+1900 else y
    fromInt (Calendar.fromComponents y (component values 1 0) (component values 2 1)
      (component values 3 0) (component values 4 0) (component values 5 0) (component values 6 0))

private def completeNumbers (m : Machine) (c : BuiltinContinuation) : Machine :=
  if c.phase == "constructor" then allocate m (fromArguments c.locals)
  else if c.phase == "utc" then result m (timeValue (fromArguments c.locals))
  else if c.phase == "setTime" then
    match arg c.locals 0 with
    | .timestamp time => assign m c.thisValue (some time.exact.trunc)
    | .calendar q => assign m c.thisValue (some (calendarTrunc q))
    | value => assign m c.thisValue (clip (bits value))
  else if c.phase == "setFullYear" || c.phase == "setUTCFullYear" then
    checked m (dateData m c.thisValue) fun (_,old) =>
      if c.locals.any (fun v => !validComponent v) then assign m c.thisValue none
      else
        let f := Calendar.fields (old.getD 0)
        assign m c.thisValue (fromInt (Calendar.fromComponents (component c.locals 0 0)
          (component c.locals 1 f.month) (component c.locals 2 f.day) f.hour f.minute f.second f.millisecond))
  else invalid m c.thisValue c.phase

private def collectNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if c.locals.length ≥ c.arguments.length then completeNumbers m c
  else
    let value := arg c.arguments c.locals.length
    if isObject value then primitiveThen m value "number" (.builtin { c with indices := [1] })
    else if (match value with | .calendar _ => true | .timestamp _ => c.phase == "setTime" | _ => false) then
      { m with control := .resumeBuiltin { c with indices := [1] } value }
    else checked m (toNumber value) fun n =>
      { m with control := .resumeBuiltin { c with indices := [1] } (.number n) }

private def getter (m : Machine) (name : String) (receiver : Value) : Machine :=
  checked m (dateData m receiver) fun (_,time) =>
    if name == "getTime" || name == "valueOf" then result m (timeValue time)
    else if ["toString","toDateString","toTimeString","toUTCString","toISOString"].contains name then
      match time with
      | none => if name == "toISOString" then fail m (.exception "RangeError" "Invalid time value")
          else result m (.string (key "Invalid Date"))
      | some t =>
        let output := if name == "toDateString" then Calendar.toDateString t
          else if name == "toTimeString" then Calendar.toTimeString t
          else if name == "toUTCString" then Calendar.toUTCString t
          else if name == "toISOString" then Calendar.toISOString t else Calendar.toString t
        result m (.string (key output))
    else match time with
      | none => result m (.number Number.nan)
      | some t =>
        let f := Calendar.fields t
        let yearGetter := ["getFullYear","getUTCFullYear","getYear"].contains name
        if yearGetter && t.natAbs > 8640000000000000 then
          result m (.calendar ((if name == "getYear" then f.year-1900 else f.year) : Rat))
        else
        let value : Option Int := match name with
          | "getFullYear" | "getUTCFullYear" => some f.year
          | "getYear" => some (f.year-1900)
          | "getMonth" | "getUTCMonth" => some f.month
          | "getDate" | "getUTCDate" => some f.day
          | "getDay" | "getUTCDay" => some f.weekday
          | "getHours" | "getUTCHours" => some f.hour
          | "getMinutes" | "getUTCMinutes" => some f.minute
          | "getSeconds" | "getUTCSeconds" => some f.second
          | "getMilliseconds" | "getUTCMilliseconds" => some f.millisecond
          | "getTimezoneOffset" => some 0
          | _ => none
        match value with
        | some n => result m (.number (Number.ofInt n))
        | none => invalid m receiver name

def resume (m : Machine) (c : BuiltinContinuation) (value : Value) : Machine :=
  if c.phase == "oneArgument" then
    if isObject value then primitiveThen m value "default" (.builtin c)
    else match value with
      | .string _ => invalid m value "Date string parsing"
      | .timestamp time => allocate m (some time.exact.trunc)
      | .calendar q => allocate m (some (calendarTrunc q))
      | _ => checked m (toNumber value) fun n => allocate m (clip n)
  else if c.indices == [1] then
    if isObject value then primitiveThen m value "number" (.builtin c)
    else if (match value with | .calendar _ => true | _ => false) then
      collectNext m { c with locals := c.locals ++ [value], indices := [] }
    else if c.phase == "setTime" then
      match value with
      | .timestamp _ => collectNext m { c with locals := c.locals ++ [value], indices := [] }
      | _ => checked m (toNumber value) fun n =>
        collectNext m { c with locals := c.locals ++ [.number n], indices := [] }
    else checked m (toNumber value) fun n =>
      collectNext m { c with locals := c.locals ++ [.number n], indices := [] }
  else invalid m c.thisValue c.phase

def dispatch (m : Machine) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  let c : BuiltinContinuation := { id := ⟨"Date",id.name⟩, phase := "", thisValue := receiver, arguments }
  if id.namespaceName == "global" && id.name == "Date" then
    if !construct then result m (.string (key (Calendar.toString (now m))))
    else if arguments.isEmpty then allocate m (some (now m))
    else if arguments.length == 1 then
      match arg arguments 0 with
      | .object object => checked m (checkedObject m.heap object) fun o =>
        match o.kind with
        | .date time => allocate m (clip time)
        | .dateExtended time => allocate m (some time)
        | _ => resume m { c with phase := "oneArgument" } (arg arguments 0)
      | value => resume m { c with phase := "oneArgument" } value
    else collectNext m { c with phase := "constructor", arguments := arguments.take 7 }
  else if construct then fail m (.exception "TypeError" "Date method is not a constructor")
  else if id.namespaceName == "Date" && id.name == "now" then result m (.timestamp (ClockValue.Timestamp.ofInt (now m)))
  else if id.namespaceName == "Date" && id.name == "UTC" then
    collectNext m { c with phase := "utc", arguments := if arguments.isEmpty then [.undefined] else arguments.take 7 }
  else if id.namespaceName == "Date.prototype" && ["setTime","setFullYear","setUTCFullYear"].contains id.name then
    checked m (dateData m receiver) fun _ => collectNext m {
      c with
      phase := id.name
      arguments := if arguments.isEmpty then [.undefined] else arguments.take (if id.name == "setTime" then 1 else 3) }
  else if id.namespaceName == "Date.prototype" &&
      ["getTime","valueOf","getFullYear","getUTCFullYear","getYear","getMonth","getUTCMonth",
       "getDate","getUTCDate","getDay","getUTCDay","getHours","getUTCHours","getMinutes","getUTCMinutes",
       "getSeconds","getUTCSeconds","getMilliseconds","getUTCMilliseconds","getTimezoneOffset",
       "toString","toDateString","toTimeString","toUTCString","toISOString"].contains id.name then
    getter m id.name receiver
  else invalid m receiver id.name

end CookieClicker.JavaScript.Date

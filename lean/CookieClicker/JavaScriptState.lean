import CookieClicker.JavaScriptSyntax
import CookieClicker.JavaScriptClockValue

/-! Explicit machine data for JavaScript source execution.
Object identities and lexical environments are heap indices. A closure stores
source syntax and an environment index; it never stores a Lean callback.
Host requests are unresolved machine states, not assumed transition functions.
This is the basis of an interpreter, not a complete browser implementation.
-/
namespace CookieClicker.JavaScript

abbrev ObjectId := Nat
abbrev EnvId := Nat
abbrev EventId := Nat

inductive Value where
  | undefined
  | null
  | boolean (value : Bool)
  | number (bits : UInt64)
  | timestamp (value : ClockValue.Timestamp)
  | calendar (value : Rat)
  | string (value : JSString)
  | timestampText (value : Array UInt16)
  | textIndex (value : Int)
  | object (id : ObjectId)
  deriving Repr, DecidableEq

def Value.ofLiteral : Literal → Value
  | .null => .null
  | .boolean value => .boolean value
  | .number bits => .number bits
  | .string value => .string value

inductive PropertyDescriptor where
  | data (value : Value) (writable enumerable configurable : Bool)
  | accessor (getter setter : Option ObjectId) (enumerable configurable : Bool)
  deriving Repr, DecidableEq

structure OwnProperty where
  name : JSString
  descriptor : PropertyDescriptor
  deriving Repr, DecidableEq

/-- Absent fields differ from explicit undefined accessors. -/
structure DescriptorUpdate where
  value : Option Value := none
  writable : Option Bool := none
  getter : Option (Option ObjectId) := none
  setter : Option (Option ObjectId) := none
  enumerable : Option Bool := none
  configurable : Option Bool := none
  deriving Repr, DecidableEq

structure FunctionClosure where
  name : Option String
  parameters : List String
  body : List Stmt
  scope : EnvId
  strict : Bool
  sourceText : Option JSString
  deriving Repr

/-- Names identify unresolved or implemented primitives; they are not functions. -/
structure BuiltinId where
  namespaceName : String
  name : String
  deriving Repr, DecidableEq

inductive ObjectKind where
  | ordinary
  | array
  | function (closure : FunctionClosure)
  | builtin (id : BuiltinId)
  | stringWrapper (value : JSString)
  | timestampTextWrapper (value : Array UInt16)
  | textIndexWrapper (value : Int)
  | numberWrapper (bits : UInt64)
  | timestampWrapper (value : ClockValue.Timestamp)
  | calendarWrapper (value : Rat)
  | booleanWrapper (value : Bool)
  | regexp (pattern : JSString) (flags : String)
  | date (timeBits : UInt64)
  | dateExtended (milliseconds : Int)
  | error (name : String)
  | arguments (parameterMap : List (JSString × EnvId × String))
  | host (className : String) (hostId : Nat)
  deriving Repr

structure JSObject where
  kind : ObjectKind := .ordinary
  timestampTextSequence : Bool := false
  prototype : Option ObjectId := none
  extensible : Bool := true
  /-- Insertion order is retained; enumeration has a separate semantics. -/
  properties : List OwnProperty := []
  nativeFunctionText : Option JSString := none
  /-- False marks a partial native catalogue, never an empty native object. -/
  propertiesComplete : Bool := true
  /-- These own descriptors require semantics that are not yet supplied. -/
  unresolvedOwnNames : List JSString := []
  /-- Source accessors are callable but cannot be used with new. -/
  constructable : Bool := true
  deriving Repr

structure Binding where
  name : String
  value : Value := .undefined
  mutable : Bool := true
  deletable : Bool := false
  initialized : Bool := true
  deriving Repr, DecidableEq

inductive EnvironmentRecord where
  | declarative (bindings : List Binding)
  | object (object : ObjectId) (provideThis : Bool)
  deriving Repr, DecidableEq

structure LexicalEnvironment where
  record : EnvironmentRecord
  outer : Option EnvId
  deriving Repr, DecidableEq

structure Heap where
  objects : Array JSObject := #[]
  environments : Array LexicalEnvironment := #[]
  deriving Repr

def Heap.object? (heap : Heap) (id : ObjectId) : Option JSObject := heap.objects[id]?
def Heap.environment? (heap : Heap) (id : EnvId) : Option LexicalEnvironment :=
  heap.environments[id]?

def Heap.allocateObject (heap : Heap) (object : JSObject) : ObjectId × Heap :=
  (heap.objects.size, { heap with objects := heap.objects.push object })

def Heap.allocateEnvironment (heap : Heap) (environment : LexicalEnvironment) : EnvId × Heap :=
  (heap.environments.size, { heap with environments := heap.environments.push environment })

def Heap.writeObject (heap : Heap) (id : ObjectId) (object : JSObject) : Option Heap :=
  if id < heap.objects.size then some { heap with objects := heap.objects.set! id object }
  else none

def Heap.writeEnvironment (heap : Heap) (id : EnvId)
    (environment : LexicalEnvironment) : Option Heap :=
  if id < heap.environments.size then
    some { heap with environments := heap.environments.set! id environment }
  else none

inductive ReferenceBase where
  | unresolvable (name : String)
  | environment (id : EnvId) (name : String)
  | property (base : Value) (name : JSString)
  deriving Repr, DecidableEq

structure Reference where
  base : ReferenceBase
  strict : Bool
  deriving Repr, DecidableEq

inductive ExpressionResult where
  | value (value : Value)
  | reference (reference : Reference)
  deriving Repr, DecidableEq

inductive Completion where
  | normal (value : Option Value)
  | return (value : Value)
  | throw (value : Value)
  | break (label : Option String) (value : Option Value)
  | continue (label : Option String) (value : Option Value)
  deriving Repr, DecidableEq

def Completion.value : Completion → Option Value
  | .normal value | .break _ value | .continue _ value => value
  | .return value | .throw value => some value

def Completion.updateEmpty (completion : Completion) (previous : Option Value) : Completion :=
  match completion with
  | .normal none => .normal previous
  | .break label none => .break label previous
  | .continue label none => .continue label previous
  | other => other

structure ExecutionContext where
  lexicalEnvironment : EnvId
  variableEnvironment : EnvId
  thisValue : Value
  strict : Bool
  deriving Repr, DecidableEq

inductive Callback where
  | call (function : Value) (thisValue : Value) (arguments : List Value)
  | script (program : Program)
  deriving Repr

structure ScheduledEvent where
  id : EventId
  due : Rat
  order : Nat
  interval : Option Rat
  callback : Callback
  deriving Repr

structure EnumerationShape where
  object : ObjectId
  prototype : Option ObjectId
  rawKeys : List (JSString × Bool)
  stringLength : Option Nat
  deriving Repr, DecidableEq

structure ForInState where
  object : ObjectId
  remaining : List JSString
  shape : List EnumerationShape
  binding : ForInBinding
  body : Stmt
  labels : List String
  previous : Option Value
  deriving Repr

/-- Standard-library code can suspend while a source getter or callback runs.
The resume state contains data only; its phase must have an implemented rule. -/
structure BuiltinContinuation where
  id : BuiltinId
  phase : String
  thisValue : Value
  arguments : List Value := []
  locals : List Value := []
  indices : List Nat := []
  deriving Repr, DecidableEq

inductive UnresolvedRequest where
  | unsupportedSyntax (tag : String)
  | builtin (id : BuiltinId) (thisValue : Value) (arguments : List Value)
      (construct : Bool)
  | builtinContinuation (continuation : BuiltinContinuation) (value : Value)
  | nativeCallbackResult (continuation : BuiltinContinuation) (completion : Completion)
  | hostGet (className : String) (hostId : Nat) (property : JSString)
  | hostHas (className : String) (hostId : Nat) (property : JSString)
  | hostPut (className : String) (hostId : Nat) (property : JSString) (value : Value)
  | propertyEnumeration (object : ObjectId)
  | regexp (pattern : JSString) (flags : String)
  | primitiveConversion (value : Value) (hint : String)
  | freeRandom
  | calendar (operation : String) (arguments : List Value)
  deriving Repr, DecidableEq

inductive MachineFault where
  | missingObject (id : ObjectId)
  | missingEnvironment (id : EnvId)
  | cyclicEnvironment
  | cyclicPrototype
  | invalidContinuation (description : String)
  | malformedSyntax (description : String)
  deriving Repr, DecidableEq

/-- Frames retain evaluation order and pending abrupt completions. -/
inductive Frame where
  | statementList (remaining : List Stmt) (previous : Option Value)
  | expressionStatement
  | valueBoundary
  | sequence (remaining : List Expr)
  | unary (operator : UnaryOp)
  | update (operator : UpdateOp) (isPrefix : Bool)
  | binaryLeft (operator : BinaryOp) (right : Expr)
  | binaryRight (operator : BinaryOp) (left : Value)
  | binaryPrimitiveLeft (operator : BinaryOp) (right : Value)
  | binaryPrimitiveRight (operator : BinaryOp) (left : Value)
  | logical (operator : LogicalOp) (right : Expr)
  | assignmentLeft (operator : AssignmentOp) (right : Expr)
  | assignmentRead (operator : AssignmentOp) (reference : Reference) (right : Expr)
  | assignmentRight (operator : AssignmentOp) (reference : Reference) (old : Option Value)
  | assignmentConverted (reference : Reference)
  | updateRead (operator : UpdateOp) (reference : Reference) (isPrefix : Bool)
  | putResult (result : Value)
  | conditional (consequent alternate : Expr)
  | memberObject (property : Expr) (computed : Bool)
  | memberProperty (object : Value)
  | callCallee (arguments : List Expr) (construct : Bool)
  | callResolved (thisValue : Value) (arguments : List Expr) (construct : Bool)
  | clockReadCallee (integer : Bool) (argument : Expr)
  | clockReadArgument (integer : Bool) (function : Value)
  | callArguments (function thisValue : Value) (done : List Value)
      (remaining : List Expr) (construct : Bool)
  | arrayElement (object : ObjectId) (index : Nat) (remaining : List (Option Expr))
  | objectProperty (object : ObjectId) (key : PropertyName) (kind : PropertyKind)
      (remaining : List ObjectProperty)
  | functionName (name : JSString)
  | accessorFunction
  | variableInitializer (name : String) (remaining : List (String × Option Expr))
  | variableWrite (remaining : List (String × Option Expr))
  | returnValue
  | throwValue
  | ifTest (consequent : Stmt) (alternate : Option Stmt)
  | whileTest (test : Expr) (body : Stmt) (labels : List String) (previous : Option Value)
  | whileBody (test : Expr) (body : Stmt) (labels : List String) (previous : Option Value)
  | forInitial (test update : Option Expr) (body : Stmt) (labels : List String)
  | forTest (test update : Option Expr) (body : Stmt) (labels : List String)
      (previous : Option Value)
  | forBody (test update : Option Expr) (body : Stmt) (labels : List String)
      (previous : Option Value)
  | forUpdate (test update : Option Expr) (body : Stmt) (labels : List String)
      (previous : Option Value)
  | forInObject (binding : ForInBinding) (body : Stmt) (labels : List String)
  | forInReference (state : ForInState) (key : JSString)
  | forInAssigned (state : ForInState)
  | forInBody (state : ForInState)
  | tryHandler (handler : Option (String × Stmt)) (finalizer : Option Stmt)
  | finallyComplete (previous : Completion)
  | label (name : String)
  | restoreEnvironment (previous : EnvId)
  | callBoundary (previous : ExecutionContext) (constructObject : Option ObjectId)
  | eventBoundary (id : EventId) (previous : ExecutionContext)
  | nativeCallback (continuation : BuiltinContinuation) (previous : ExecutionContext)
  | builtin (continuation : BuiltinContinuation)
  deriving Repr

inductive Control where
  | expression (expression : Expr)
  | statement (statement : Stmt)
  | expressionResult (result : ExpressionResult)
  | completion (completion : Completion)
  | getValue (reference : Reference)
  | putValue (reference : Reference) (value : Value)
  | invoke (function thisValue : Value) (arguments : List Value) (construct : Bool)
  | toPrimitive (value : Value) (hint : String)
  | declarationScan (pending : List (Bool × Stmt)) (variables : List String)
      (functions : List FunctionClosure) (body : List Stmt)
  | declarationVariables (remaining : List String) (functions : List FunctionClosure)
      (body : List Stmt)
  | declarationFunctions (remaining : List FunctionClosure) (body : List Stmt)
  | forInNext (state : ForInState)
  | resumeBuiltin (continuation : BuiltinContinuation) (value : Value)
  | unresolved (request : UnresolvedRequest)
  | fault (fault : MachineFault)
  | idle
  deriving Repr

structure Machine where
  heap : Heap
  context : ExecutionContext
  control : Control
  continuation : List Frame := []
  globalObject : ObjectId
  objectPrototype : Option ObjectId := none
  functionPrototype : Option ObjectId := none
  arrayPrototype : Option ObjectId := none
  stringPrototype : Option ObjectId := none
  numberPrototype : Option ObjectId := none
  booleanPrototype : Option ObjectId := none
  regexpPrototype : Option ObjectId := none
  datePrototype : Option ObjectId := none
  throwTypeErrorIntrinsic : Option ObjectId := none
  /-- Initial native @@unscopables for supported inline-handler object scopes.
  Symbol access and mutation remain unresolved; this is not a general `with`
  environment implementation. Each entry belongs to one allocated scope. -/
  objectEnvironmentExclusions : List (EnvId × List JSString) := []
  events : List ScheduledEvent := []
  nextEventId : EventId := 0
  /-- Mathematical elapsed time; native Date conversion remains separate. -/
  elapsed : Rat := 0
  epochMilliseconds : Int := 0
  freeDrawCount : Nat := 0
  deriving Repr

end CookieClicker.JavaScript

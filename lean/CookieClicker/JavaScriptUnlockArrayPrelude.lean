import CookieClicker.JavaScriptUnlockArrayLocals
import CookieClicker.JavaScriptTypeofRead
import CookieClicker.JavaScriptReadCombinators
import CookieClicker.JavaScriptTieredRegistry

namespace CookieClicker.JavaScript.UnlockArrayPrelude
open SourceRead UnlockArrayLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def guard : Expr := .binary .strictEqual (.unary .typeOf (.identifier "what"))
  (.literal (.string (JSString.ofString "string")))
def stringBranch : Stmt := match BuildingCallbackSyntax.UnlockBody with
  | .block [.ifThenElse _ body _] => body
  | _ => .empty
def argument : Expr := .member (.identifier "what") (.identifier "i") true
def body : Stmt := .block [.expression (MemberCall.expression "Unlock" argument)]
def loop : Stmt := .forIn (.variable "i") (.identifier "what") body

theorem source_body : BuildingCallbackSyntax.UnlockBody=
    .block [.ifThenElse guard stringBranch (some (.block [loop]))] := rfl

theorem array_guard (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (array : ObjectId) (arguments : Value) (i : Value) (suffix : Array LexicalEnvironment)
    (object : JSObject) (present : checkedObject (heap objects leading outer ⟨.object array,arguments,i⟩ suffix) array=.ok object)
    (kind : object.kind=.array) :
    Reads (start base objects leading outer ⟨.object array,arguments,i⟩ suffix) guard (.boolean false) 9 := by
  let state:=start base objects leading outer ⟨.object array,arguments,i⟩ suffix
  have typeRead : Reads state (.unary .typeOf (.identifier "what")) (.string (JSString.ofString "object")) 5 := by
    apply typeof_local state "what" (.object array) (.string (JSString.ofString "object"))
      (bindings ⟨.object array,arguments,i⟩) (some outer)
      (checked_local objects leading outer _ suffix) (by simp [bindings])
      (read_what objects leading outer _ suffix)
    simp [state,start,unary,valueType,present,kind,bind,Except.bind,pure,Except.pure]
  exact binary_value state .strictEqual _ _ _ _ _ 5 1 typeRead (literal state (.string (JSString.ofString "string")))
    rfl rfl (by decide) (by rfl)

def afterPrefix (base : Machine) (array : ObjectId) (shape : List EnumerationShape) : Machine := {
  base with
  control:=.forInNext ⟨array,enumerationNames shape,shape,.variable "i",body,[],none⟩
  continuation:=.statementList [] none::.statementList [] none::base.continuation }

theorem native_prefix (base : Machine) (array : ObjectId) (shape : List EnumerationShape)
    (condition : Reads base guard (.boolean false) 9)
    (what : Reads base (.identifier "what") (.object array) 3)
    (found : enumerationShape base.heap (base.heap.objects.size+1) array=.ok shape) (fuel : Nat) :
    Builtins.run (18+fuel) {base with control:=.statement BuildingCallbackSyntax.UnlockBody}=
      Builtins.run fuel (afterPrefix base array shape) := by
  rw [source_body,show 18+fuel=2+(9+(2+(5+fuel))) by omega,Nat.add_comm 2 (9+(2+(5+fuel)))]
  change Builtins.run (9+(2+(5+fuel))) {base with
    control:=.expression guard
    continuation:=.ifTest stringBranch (some (.block [loop]))::.statementList [] none::base.continuation}=_
  rw [condition _ (by rfl),Nat.add_comm 2 (5+fuel)]
  change Builtins.run (5+fuel) {base with
    control:=.statement loop
    continuation:=.statementList [] none::.statementList [] none::base.continuation}=_
  have applied:=TieredRegistry.native_forIn_start
    {base with continuation:=.statementList [] none::.statementList [] none::base.continuation}
    (.identifier "what") (.variable "i") body array shape 3 what found fuel
  simpa only [loop,afterPrefix,labels] using applied

end CookieClicker.JavaScript.UnlockArrayPrelude

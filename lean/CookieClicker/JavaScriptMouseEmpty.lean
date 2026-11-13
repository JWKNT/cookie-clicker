import CookieClicker.JavaScriptMouseMachine
import CookieClicker.JavaScriptTieredRegistry

namespace CookieClicker.JavaScript.MouseEmpty
open SourceRead TieredRead MouseMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def godStatement : Stmt := (MouseSource.body.drop 41).headD .empty
def godConsequent : Stmt := match godStatement with | .ifThenElse _ consequent _ => consequent | _ => .empty

def buffsStatement : Stmt := (MouseSource.body.drop 42).headD .empty
def buffsBody : Stmt := match buffsStatement with | .forIn _ _ body => body | _ => .empty

def buffsExpression : Expr := .member (.identifier "Game") (.identifier "buffs") false

theorem god_source : godStatement=.ifThenElse (.member (.identifier "Game") (.identifier "hasGod") false) godConsequent none := rfl

theorem buffs_source : buffsStatement=.forIn (.variable "i") buffsExpression buffsBody := rfl

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  game : ObjectId
  gameObject : JSObject
  present : checkedObject (machine base old state).heap game=.ok gameObject
  ordinary : gameObject.kind=.ordinary
  absent : lookupProperty (machine base old state).heap game (JSString.ofString "hasGod")=.ok none
  gameRead : Reads (machine base old state) (.identifier "Game") (.object game) 3
  buffs : ObjectId
  buffsEdge : DataEdge (machine base old state) game (JSString.ofString "buffs") (.object buffs)
  shape : List EnumerationShape
  found : enumerationShape (machine base old state).heap ((machine base old state).heap.objects.size+1) buffs=.ok shape
  empty : enumerationNames shape=[]

theorem Inputs.native_noGod {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (9+fuel) {machine base old state with control:=.statement godStatement}=
      Builtins.run fuel {machine base old state with control:=.completion (.normal none)} := by
  have read:=dot_missing (machine base old state) (.identifier "Game") input.game "hasGod" input.gameObject
    3 input.gameRead input.present (Or.inl input.ordinary) input.absent
  rw [god_source]
  exact SourceRead.false_branch (machine base old state) _ godConsequent .undefined 7 read rfl fuel

theorem Inputs.native_emptyBuffs {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (10+fuel) {machine base old state with control:=.statement buffsStatement}=
      Builtins.run fuel {machine base old state with control:=.completion (.normal none)} := by
  have read : Reads (machine base old state) buffsExpression (.object input.buffs) 7 :=
    input.buffsEdge.dot _ 3 input.gameRead
  rw [buffs_source,show 10+fuel=9+(1+fuel) by omega,
    TieredRegistry.native_forIn_start (machine base old state) buffsExpression (.variable "i") buffsBody
      input.buffs input.shape 7 read input.found]
  exact TieredLoop.empty_complete (machine base old state)
    ⟨input.buffs,enumerationNames input.shape,input.shape,.variable "i",buffsBody,
      labels (machine base old state).continuation,none⟩ input.empty input.found fuel

end CookieClicker.JavaScript.MouseEmpty

namespace CookieClicker.JavaScript.MouseEmpty
open MouseMachine

def Inputs.reframe {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (continuation : List Frame) :
    Inputs {base with continuation} old state := {
  game:=input.game,gameObject:=input.gameObject,present:=input.present,ordinary:=input.ordinary,
  absent:=input.absent,gameRead:=input.gameRead,buffs:=input.buffs,buffsEdge:={object:=input.buffsEdge.object,present:=input.buffsEdge.present,kind:=input.buffsEdge.kind,property:=input.buffsEdge.property},
  shape:=input.shape,found:=input.found,empty:=input.empty }

end CookieClicker.JavaScript.MouseEmpty

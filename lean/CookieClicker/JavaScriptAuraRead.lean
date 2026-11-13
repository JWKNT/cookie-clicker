import CookieClicker.JavaScriptAuraLocals
import CookieClicker.JavaScriptReadCombinators

/-! Native reads in auraMult when both selected auras are the empty slot.
All property paths and comparisons execute the retained source semantics. -/
namespace CookieClicker.JavaScript.AuraRead
open SourceRead TieredRead AuraLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def selectedName (selector : String) : Expr :=
  .member (.member (.member (.identifier "Game") (.identifier "dragonAuras") false)
    (.member (.identifier "Game") (.identifier selector) false) true) (.identifier "name") false

def noAura : JSString := JSString.ofString "No aura"
def reality : JSString := JSString.ofString "Reality Bending"

structure World (base : Machine) where
  game : ObjectId
  auras : ObjectId
  emptyAura : ObjectId
  table : DataEdge base game (JSString.ofString "dragonAuras") (.object auras)
  first : DataEdge base game (JSString.ofString "dragonAura") (.number 0)
  second : DataEdge base game (JSString.ofString "dragonAura2") (.number 0)
  zeroEntry : DataEdge base auras (JSString.ofString "0") (.object emptyAura)
  name : DataEdge base emptyAura (JSString.ofString "name") (.string noAura)

theorem selected_name (base : Machine) (world : World base) (selector : String)
    (index : DataEdge base world.game (JSString.ofString selector) (.number 0))
    (game : Reads base (.identifier "Game") (.object world.game) 3) :
    Reads base (selectedName selector) (.string noAura) 23 := by
  apply world.name.dot _ 19
  exact world.zeroEntry.key _ _ (.number 0) 7 7
    (world.table.dot _ 3 game) (index.dot _ 3 game) rfl (by rfl)

theorem local_what (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "what") values.what 3 := by
  apply local_identifier _ "what" values.what (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · simp [bindings]
  · exact read_what objects leading outer values suffix

theorem local_n (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "n") values.n 3 := by
  apply local_identifier _ "n" values.n (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_n values
  · exact read_n objects leading outer values suffix

def firstTest : Expr := .logical .or
  (.binary .equal (selectedName "dragonAura") (.identifier "what"))
  (.binary .equal (selectedName "dragonAura2") (.identifier "what"))

def realityTest : Expr := .logical .or
  (.binary .equal (selectedName "dragonAura") (.literal (.string reality)))
  (.binary .equal (selectedName "dragonAura2") (.literal (.string reality)))

def levelTest : Expr := .binary .greaterEqual
  (.member (.identifier "Game") (.identifier "dragonLevel") false)
  (.binary .add (.member (.member (.member (.identifier "Game")
    (.identifier "dragonAurasBN") false) (.identifier "what") true) (.identifier "id") false)
    (.literal (.number 4616189618054758400)))

theorem first_test (base : Machine) (world : World base) (what : JSString)
    (other : noAura ≠ what)
    (game : Reads base (.identifier "Game") (.object world.game) 3)
    (parameter : Reads base (.identifier "what") (.string what) 3) :
    Reads base firstTest (.boolean false) 61 := by
  have left := string_equal base _ _ noAura what 23 3
    (selected_name base world "dragonAura" world.first game) parameter
  have right := string_equal base _ _ noAura what 23 3
    (selected_name base world "dragonAura2" world.second game) parameter
  simp only [other,decide_false] at left right
  exact false_or base _ _ (.boolean false) (.boolean false) 29 29 left right rfl

theorem reality_test (base : Machine) (world : World base)
    (game : Reads base (.identifier "Game") (.object world.game) 3) :
    Reads base realityTest (.boolean false) 57 := by
  have left := string_equal base _ _ noAura reality 23 1
    (selected_name base world "dragonAura" world.first game) (literal base (.string reality))
  have right := string_equal base _ _ noAura reality 23 1
    (selected_name base world "dragonAura2" world.second game) (literal base (.string reality))
  have different : noAura ≠ reality := by decide
  simp only [different,decide_false] at left right
  exact false_or base _ _ (.boolean false) (.boolean false) 27 27 left right rfl

theorem second_test (base : Machine) (world : World base)
    (game : Reads base (.identifier "Game") (.object world.game) 3) :
    Reads base (.logical .and realityTest levelTest) (.boolean false) 59 :=
  false_and base realityTest levelTest (.boolean false) 57 (reality_test base world game) rfl

def firstBranch : Stmt := .ifThenElse firstTest
  (.expression (.assignment .assign (.identifier "n") (.literal (.number Number.one)))) none
def secondBranch : Stmt := .ifThenElse (.logical .and realityTest levelTest)
  (.expression (.assignment .add (.identifier "n") (.literal (.number 4591870180066957722)))) none

theorem source_body : AuraLocals.body = [
    .variable [("n",some (.literal (.number 0)))],firstBranch,secondBranch,
    .return (some (.identifier "n"))] := rfl

end CookieClicker.JavaScript.AuraRead

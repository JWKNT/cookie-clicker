import CookieClicker.JavaScriptGainsCommonCache
import CookieClicker.JavaScriptPropertyCompound
import CookieClicker.JavaScriptPropertyComputed

namespace CookieClicker.JavaScript.GainsCacheWrites
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure Writable (base : Machine) (id : ObjectId) (key : JSString) where
  object : JSObject
  previous : Value
  present : base.heap.object? id=some object
  ordinary : object.kind=.ordinary
  own : ownProperty object key=some (.data previous true true true)
  lookup : lookupProperty base.heap id key=.ok (some (.data previous true true true))

def Writable.after {base : Machine} {id : ObjectId} {key : JSString}
    (write : Writable base id key) (value : Value) : Machine := {
  base with
  heap:=PropertyFrame.write base.heap id write.object key value true true
  control:=.completion (.normal (some value)) }

def totalStatement : Stmt := (GainsCommonCache.body.drop 4).headD .empty

def totalExpression : Expr := .binary .multiply
  (.member (.identifier "me") (.identifier "amount") false)
  (.member (.identifier "me") (.identifier "storedCps") false)

theorem source_total : totalStatement=.expression (.assignment .assign
    (.member (.identifier "me") (.identifier "storedTotalCps") false) totalExpression) := rfl

theorem total_read (base : Machine) (me : ObjectId) (amount cps : UInt64)
    (read : Reads base (.identifier "me") (.object me) 3)
    (amountEdge : DataEdge base me (JSString.ofString "amount") (.number amount))
    (cpsEdge : DataEdge base me (JSString.ofString "storedCps") (.number cps)) :
    Reads base totalExpression (.number (Number.mul amount cps)) 17 := by
  apply binary_value base .multiply _ _ (.number amount) (.number cps) _ 7 7
    (amountEdge.dot _ _ read) (cpsEdge.dot _ _ read) rfl rfl (by decide)
  rfl

/-- The native per-building total uses binary64 multiplication and writes the
existing writable cache field with the original descriptor flags. -/
theorem native_total (base : Machine) (me : ObjectId) (amount cps : UInt64)
    (read : Reads base (.identifier "me") (.object me) 3)
    (amountEdge : DataEdge base me (JSString.ofString "amount") (.number amount))
    (cpsEdge : DataEdge base me (JSString.ofString "storedCps") (.number cps))
    (write : Writable base me (JSString.ofString "storedTotalCps")) (fuel : Nat) :
    Builtins.run (28+fuel) {base with control:=.statement totalStatement}=
      Builtins.run fuel (write.after (.number (Number.mul amount cps))) := by
  rw [source_total,show 28+fuel=8+(17+(3+fuel)) by omega,
    PropertyAssign.dot_prefix base (.identifier "me") totalExpression me "storedTotalCps" 3 read]
  have rhs := total_read base me amount cps read amountEdge cpsEdge
  refine (rhs _ (by rfl) (3+fuel)).trans ?_
  exact PropertyAssign.dot_suffix base me "storedTotalCps" write.object write.previous
    (.number (Number.mul amount cps)) true true write.present write.ordinary write.own write.lookup fuel

def sumStatement : Stmt := (GainsCommonCache.body.drop 5).headD .empty

def totalReadExpression : Expr := .member (.identifier "me") (.identifier "storedTotalCps") false

theorem source_sum : sumStatement=.expression (.assignment .add
    (.member (.identifier "Game") (.identifier "cookiesPs") false) totalReadExpression) := rfl

/-- The actual ordered accumulator update, without replacing its rounded sum
by an associative or real-number sum. -/
theorem native_sum (base : Machine) (game me : ObjectId) (old total : UInt64)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (totalEdge : DataEdge base me (JSString.ofString "storedTotalCps") (.number total))
    (write : Writable base game (JSString.ofString "cookiesPs"))
    (previous : write.previous=.number old) (fuel : Nat) :
    Builtins.run (21+fuel) {base with control:=.statement sumStatement}=
      Builtins.run fuel (write.after (.number (Number.add old total))) := by
  rw [source_sum,show 21+fuel=10+(7+(4+fuel)) by omega]
  have present : checkedObject base.heap game=.ok write.object := by simp [checkedObject,write.present]
  have lookup : lookupProperty base.heap game (JSString.ofString "cookiesPs")=
      .ok (some (.data (.number old) true true true)) := by simpa only [previous] using write.lookup
  have own : ownProperty write.object (JSString.ofString "cookiesPs")=
      some (.data (.number old) true true true) := by simpa only [previous] using write.own
  rw [PropertyCompound.dot_prefix base (.identifier "Game") totalReadExpression game "cookiesPs" .add
    (by decide) (.number old) write.object 3 gameRead present write.ordinary lookup]
  have rhs := totalEdge.dot (.identifier "me") 3 meRead
  refine (rhs _ (by rfl) (4+fuel)).trans ?_
  exact PropertyCompound.dot_suffix base game "cookiesPs" .add .add rfl write.object
    (.number old) (.number total) (.number (Number.add old total)) rfl rfl (by decide) rfl
    write.present write.ordinary own lookup fuel

def typeStatement : Stmt := (GainsCommonCache.body.drop 6).headD .empty

def tableExpression : Expr := .member (.identifier "Game") (.identifier "cookiesPsByType") false

def nameExpression : Expr := .member (.identifier "me") (.identifier "name") false

theorem source_type : typeStatement=.expression (.assignment .assign
    (.member tableExpression nameExpression true) totalReadExpression) := rfl

theorem native_type (base : Machine) (game me table : ObjectId) (name : JSString) (total : UInt64)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (tableEdge : DataEdge base game (JSString.ofString "cookiesPsByType") (.object table))
    (nameEdge : DataEdge base me (JSString.ofString "name") (.string name))
    (totalEdge : DataEdge base me (JSString.ofString "storedTotalCps") (.number total))
    (write : Writable base table name) (fuel : Nat) :
    Builtins.run (30+fuel) {base with control:=.statement typeStatement}=
      Builtins.run fuel (write.after (.number total)) := by
  rw [source_type,show 30+fuel=20+(7+(3+fuel)) by omega]
  have tableRead := tableEdge.dot (.identifier "Game") 3 gameRead
  have nameRead := nameEdge.dot (.identifier "me") 3 meRead
  rw [PropertyComputed.key_prefix base tableExpression nameExpression totalReadExpression table name
    7 7 tableRead nameRead]
  have rhs := totalEdge.dot (.identifier "me") 3 meRead
  refine (rhs _ (by rfl) (3+fuel)).trans ?_
  exact PropertyComputed.key_suffix base table name write.object write.previous (.number total)
    true true write.present write.ordinary write.own write.lookup fuel

end CookieClicker.JavaScript.GainsCacheWrites

import CookieClicker.JavaScriptGainsCacheWrites
import CookieClicker.JavaScriptPropertyAssignCreate

/-! Reset creates an empty cookiesPsByType object. The first calculation
therefore creates a property instead of writing an existing cache entry. -/
namespace CookieClicker.JavaScript.GainsCacheCreate
open SourceRead TieredRead GainsCacheWrites
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem native_type_new (base : Machine) (game me table : ObjectId) (name : JSString) (total : UInt64)
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (tableEdge : DataEdge base game (JSString.ofString "cookiesPsByType") (.object table))
    (nameEdge : DataEdge base me (JSString.ofString "name") (.string name))
    (totalEdge : DataEdge base me (JSString.ofString "storedTotalCps") (.number total))
    (object : JSObject) (present : base.heap.object? table=some object)
    (ordinary : object.kind=.ordinary) (extensible : object.extensible=true)
    (own : ownProperty object name=none) (lookup : lookupProperty base.heap table name=.ok none)
    (fuel : Nat) :
    Builtins.run (30+fuel) {base with control:=.statement typeStatement}=
      Builtins.run fuel {base with
        heap:=PropertyFrame.write base.heap table object name (.number total) true true
        control:=.completion (.normal (some (.number total)))} := by
  rw [source_type,show 30+fuel=20+(7+(3+fuel)) by omega]
  have tableRead := tableEdge.dot (.identifier "Game") 3 gameRead
  have nameRead := nameEdge.dot (.identifier "me") 3 meRead
  rw [PropertyComputed.key_prefix base tableExpression nameExpression totalReadExpression table name
    7 7 tableRead nameRead]
  have rhs := totalEdge.dot (.identifier "me") 3 meRead
  refine (rhs _ (by rfl) (3+fuel)).trans ?_
  exact PropertyAssignCreate.key_suffix base table name object (.number total)
    present ordinary extensible own lookup fuel

end CookieClicker.JavaScript.GainsCacheCreate

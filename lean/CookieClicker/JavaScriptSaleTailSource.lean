import CookieClicker.JavaScriptSaleTailFrame

namespace CookieClicker.JavaScript.SaleTailSource
open SourceRead SaleTailFrame SaleNumericSource
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def withContinuation {base : Machine} (entry : SaleTailFrame.Entry base) (continuation : List JavaScript.Frame) :
    SaleTailFrame.Entry {base with continuation} := {
  entry with
  priceLocal:={entry.priceLocal with},priceSlot:={entry.priceSlot with}
  recalculate:={entry.recalculate with},buildingsOwned:={entry.buildingsOwned with}
  successSlot:=entry.successSlot.withContinuation continuation
  gameWindow:={entry.gameWindow with},sellFunction:={entry.sellFunction with}
  amountEdge:={entry.amountEdge with},idEdge:={entry.idEdge with} }

theorem source_price {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (12+fuel) {base with control:=.statement (sourceStatement 6)}=
    Builtins.run fuel {entry.afterPrice with control:=.completion (.normal (some (.number entry.price)))} :=
  BuildingStore.assign_this base "price" entry.priceSlot entry.receiver (.identifier "price")
    (.number entry.price) 3 entry.priceLocal.reads fuel

theorem source_sellFunction {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (7+fuel) {entry.afterPrice with control:=.statement (sourceStatement 7)}=
    Builtins.run fuel {entry.afterPrice with control:=.completion (.normal none)} :=
  false_branch _ _ _ entry.sellFunctionValue 5 entry.sellRead entry.noSellFunction fuel

theorem source_recalculate {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (12+fuel) {entry.afterPrice with control:=.statement (sourceStatement 8)}=
    Builtins.run fuel {entry.afterRecalculate with control:=.completion (.normal (some (.number Number.one)))} := by
  have idEq : entry.recalculateAfterPrice.id=entry.game:=entry.recalculateId
  have read : Reads entry.afterPrice (.identifier "Game") (.object entry.recalculateAfterPrice.id) 3 := by
    rw [idEq];exact entry.gameReadAfterPrice
  conv => lhs;arg 1;rw [show 12+fuel=3+5+(1+(3+fuel)) by omega]
  refine (PropertyAssign.dot_prefix entry.afterPrice (.identifier "Game") (.literal (.number Number.one))
    entry.recalculateAfterPrice.id "recalculateGains" 3 read (1+(3+fuel))).trans ?_
  change Builtins.run (1+(3+fuel)) {entry.afterPrice with
    control:=.expression (.literal (.number Number.one))
    continuation:=.assignmentRight .assign (PropertyAssign.reference entry.afterPrice entry.recalculateAfterPrice.id "recalculateGains")
      none::.expressionStatement::base.continuation}=_
  rw [literal _ _ _ (by rfl)]
  exact PropertyAssign.dot_suffix entry.afterPrice entry.recalculateAfterPrice.id "recalculateGains"
    entry.recalculateAfterPrice.object entry.recalculateAfterPrice.oldValue (.number Number.one)
    entry.recalculateAfterPrice.enumerable entry.recalculateAfterPrice.configurable
    (OriginalPropertyWrite.original_present entry.recalculateAfterPrice) entry.recalculateAfterPrice.kind
    entry.recalculateAfterPrice.own entry.recalculateAfterPrice.lookup fuel

theorem source_row {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (entry.rowTicks+2+fuel) {entry.afterRecalculate with control:=.statement (sourceStatement 9)}=
    Builtins.run fuel {entry.afterRecalculate with control:=.completion (.normal none)} :=
  false_branch _ _ _ (.boolean false) entry.rowTicks entry.rowRead rfl fuel

theorem source_owned {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (13+fuel) {entry.afterRecalculate with control:=.statement (sourceStatement 10)}=
    Builtins.run fuel {entry.afterOwned with control:=.completion (.normal (some (.number entry.owned)))} := by
  have idEq : entry.ownedAfterRecalculate.id=entry.game:=entry.ownedId
  have oldValue : entry.ownedAfterRecalculate.oldValue=.number entry.owned:=entry.ownedValue
  have read : Reads entry.afterRecalculate (.identifier "Game") (.object entry.ownedAfterRecalculate.id) 3 := by
    rw [idEq];exact entry.gameReadAfterRecalculate
  exact PropertyUpdate.source_update entry.afterRecalculate (.identifier "Game") entry.ownedAfterRecalculate.id
    entry.ownedAfterRecalculate.object "BuildingsOwned" .decrement false entry.owned
    entry.ownedAfterRecalculate.enumerable entry.ownedAfterRecalculate.configurable 3 read
    (OriginalPropertyWrite.original_present entry.ownedAfterRecalculate) entry.ownedAfterRecalculate.kind
    (by simpa only [oldValue] using entry.ownedAfterRecalculate.own)
    (by simpa only [SaleTailFrame.Entry.afterRecalculate,oldValue] using entry.ownedAfterRecalculate.lookup) fuel

theorem source_success {base : Machine} (entry : SaleTailFrame.Entry base) (fuel : Nat) :
    Builtins.run (8+fuel) {entry.afterOwned with control:=.statement (sourceStatement 11)}=
    Builtins.run fuel entry.changed :=
  LocalAssign.source_assignment entry.afterOwned "success" entry.successAfterOwned (.literal (.number Number.one))
    (.number Number.one) 1 (literal _ _) rfl fuel

def atPriceWrite {base : Machine} (_entry : SaleTailFrame.Entry base) (previous : Option Value) : Machine := {base with
  control:=.statement (sourceStatement 6)
  continuation:=.statementList (successBody.drop 7) previous::base.continuation}

theorem actual_suffix {base : Machine} (entry : SaleTailFrame.Entry base) (previous : Option Value) (fuel : Nat) :
    Builtins.run (entry.rowTicks+60+fuel) (atPriceWrite entry previous)=Builtins.run fuel entry.changed := by
  conv => lhs;arg 1;rw [show entry.rowTicks+60+fuel=12+(1+(7+(1+(12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel))))))))))) by omega]
  refine (source_price (withContinuation entry (.statementList (successBody.drop 7) previous::base.continuation))
    (1+(7+(1+(12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))))))))).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 (7+(1+(12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel))))))))))]
  change Builtins.run (7+(1+(12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))))))) {entry.afterPrice with
    control:=.statement (sourceStatement 7)
    continuation:=.statementList (successBody.drop 8) (some (.number entry.price))::base.continuation}=_
  refine (source_sellFunction (withContinuation entry (.statementList (successBody.drop 8) (some (.number entry.price))::base.continuation))
    (1+(12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))))))).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 (12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel))))))))]
  change Builtins.run (12+(1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))))) {entry.afterPrice with
    control:=.statement (sourceStatement 8)
    continuation:=.statementList (successBody.drop 9) (some (.number entry.price))::base.continuation}=_
  refine (source_recalculate (withContinuation entry (.statementList (successBody.drop 9) (some (.number entry.price))::base.continuation))
    (1+(entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))))).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 (entry.rowTicks+2+(1+(13+(1+(8+(1+fuel))))))]
  change Builtins.run (entry.rowTicks+2+(1+(13+(1+(8+(1+fuel)))))) {entry.afterRecalculate with
    control:=.statement (sourceStatement 9)
    continuation:=.statementList (successBody.drop 10) (some (.number Number.one))::base.continuation}=_
  refine (source_row (withContinuation entry (.statementList (successBody.drop 10) (some (.number Number.one))::base.continuation))
    (1+(13+(1+(8+(1+fuel)))))).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 (13+(1+(8+(1+fuel))))]
  change Builtins.run (13+(1+(8+(1+fuel)))) {entry.afterRecalculate with
    control:=.statement (sourceStatement 10)
    continuation:=.statementList (successBody.drop 11) (some (.number Number.one))::base.continuation}=_
  refine (source_owned (withContinuation entry (.statementList (successBody.drop 11) (some (.number Number.one))::base.continuation))
    (1+(8+(1+fuel)))).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 (8+(1+fuel))]
  change Builtins.run (8+(1+fuel)) {entry.afterOwned with
    control:=.statement (sourceStatement 11)
    continuation:=.statementList [] (some (.number entry.owned))::base.continuation}=_
  refine (source_success (withContinuation entry (.statementList [] (some (.number entry.owned))::base.continuation)) (1+fuel)).trans ?_
  conv => lhs;arg 1;rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SaleTailSource

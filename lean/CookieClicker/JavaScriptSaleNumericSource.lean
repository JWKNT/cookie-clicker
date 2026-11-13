import CookieClicker.JavaScriptSaleNumericFrame
import CookieClicker.JavaScriptGodzamokSyntax

namespace CookieClicker.JavaScript.SaleNumericSource
open SourceRead SaleNumericFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def sellStatements : List Stmt := match GodzamokSyntax.sellBody with | .block body=>body | _=>[]
def loopBody : List Stmt := match (sellStatements[5]?).getD .empty with
  | .forLoop _ _ _ (.block body)=>body | _=>[]
def successBody : List Stmt := match (loopBody[3]?).getD .empty with
  | .ifThenElse _ (.block body) _=>body | _=>[]
def sourceStatement (index : Nat) : Stmt := (successBody[index]?).getD .empty

def withContinuation {base : Machine} (entry : Entry base) (continuation : List JavaScript.Frame) :
    Entry {base with continuation} := {
  entry with
  soldSlot:=entry.soldSlot.withContinuation continuation
  moniSlot:=entry.moniSlot.withContinuation continuation
  soldRead:={entry.soldRead with}
  moniRead:={entry.moniRead with}
  priceRead:={entry.priceRead with}
  maximum:={entry.maximum with mathRead:=entry.maximum.mathRead} }

theorem source_sold {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (9+fuel) {base with control:=.statement (sourceStatement 0)}=
    Builtins.run fuel {entry.afterSold with control:=.completion (.normal (some (.number entry.sold)))} :=
  LocalNumeric.source_update base "sold" entry.soldSlot entry.sold entry.soldRead.read .increment false fuel

theorem source_moni {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (13+fuel) {entry.afterSold with control:=.statement (sourceStatement 1)}=
    Builtins.run fuel {entry.afterMoni with control:=.completion (.normal (some (.number entry.newMoni)))} :=
  LocalNumeric.source_add entry.afterSold "moni" entry.nextMoniSlot entry.moni entry.price (.identifier "price") 3
    entry.moniAfterSold.read entry.priceAfterSold.reads fuel

theorem source_cookies {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (17+fuel) {entry.afterMoni with control:=.statement (sourceStatement 2)}=
    Builtins.run fuel {entry.afterCookies with control:=.completion (.normal (some (.number entry.newCookies)))} := by
  conv => lhs; arg 1; rw [show 17+fuel=3+7+(3+(4+fuel)) by omega]
  refine (PropertyCompound.dot_prefix entry.afterMoni (.identifier "Game") (.identifier "price") entry.counter.game
    "cookies" .add (by decide) (.number entry.cookies) entry.counter.gameObject 3 entry.gameReadMoni
    (by rw [entry.moniHeap];exact CounterObjects.checked_game entry.counter _)
    entry.counter.gameKind
    (by rw [entry.moniHeap];exact CounterObjects.cookies_lookup entry.counter _)
    (3+(4+fuel))).trans ?_
  change Builtins.run (3+(4+fuel)) {entry.afterMoni with
    control:=.expression (.identifier "price")
    continuation:=.assignmentRight .add (PropertyAssign.reference entry.afterMoni entry.counter.game "cookies")
      (some (.number entry.cookies))::.expressionStatement::base.continuation}=_
  rw [entry.priceAfterMoni.reads _ (by rfl)]
  refine (PropertyCompound.dot_suffix entry.afterMoni entry.counter.game "cookies" .add .add rfl
    entry.counter.gameObject (.number entry.cookies) (.number entry.price) (.number entry.newCookies)
    rfl rfl (by decide) rfl (by rw [entry.moniHeap];exact entry.counter.gameRead)
    entry.counter.gameKind entry.counter.cookiesOwn
    (by rw [entry.moniHeap];exact CounterObjects.cookies_lookup entry.counter _) fuel).trans ?_
  rw [entry.cookiesWrite]
  rfl

theorem source_earned {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (38+fuel) {entry.afterCookies with control:=.statement (sourceStatement 3)}=
    Builtins.run fuel {entry.afterEarned with control:=.completion (.normal (some (.number entry.newEarned)))} := by
  conv => lhs; arg 1; rw [show 38+fuel=3+5+(27+(3+fuel)) by omega]
  refine (PropertyAssign.dot_prefix entry.afterCookies (.identifier "Game") _ entry.counter.game
    "cookiesEarned" 3 entry.gameReadCookies (27+(3+fuel))).trans ?_
  change Builtins.run (27+(3+fuel)) {entry.afterCookies with
    control:=.expression (BuildingMathRead.call "max"
      [.member (.identifier "Game") (.identifier "cookies") false,
       .member (.identifier "Game") (.identifier "cookiesEarned") false])
    continuation:=.assignmentRight .assign (PropertyAssign.reference entry.afterCookies entry.counter.game "cookiesEarned")
      none::.expressionStatement::base.continuation}=_
  rw [entry.maximumRead _ (by rfl)]
  exact PropertyAssign.dot_suffix entry.afterCookies entry.counter.game "cookiesEarned" entry.cookiesFrame.gameObject
    (.number entry.earned) (.number entry.newEarned) true true entry.cookiesFrame.gameRead
    entry.cookiesFrame.gameKind entry.cookiesFrame.earnedOwn (CounterObjects.earned_lookup entry.cookiesFrame _) fuel

theorem source_amount {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (11+fuel) {entry.afterEarned with control:=.statement (sourceStatement 4)}=
    Builtins.run fuel {entry.afterAmount with control:=.completion (.normal (some (.number entry.amount)))} := by
  exact PropertyUpdate.source_update entry.afterEarned .this entry.building entry.buildingObject "amount"
    .decrement false entry.amount true true 1
    (by have read:=CursorGetPriceRead.this_read entry.afterEarned; change Reads entry.afterEarned .this base.context.thisValue 1 at read; simpa only [entry.receiver] using read)
    entry.buildingPresentEarned entry.buildingKind entry.amountOwn entry.amountLookupEarned fuel

def atNextPrice {base : Machine} (entry : Entry base) : Machine := {entry.afterAmount with
  control:=.statement (sourceStatement 5)
  continuation:=.statementList (successBody.drop 6) (some (.number entry.amount))::base.continuation}

theorem actual_block_prefix {base : Machine} (entry : Entry base) (fuel : Nat) :
    Builtins.run (94+fuel) {base with control:=.statement (.block successBody)}=
    Builtins.run fuel (atNextPrice entry) := by
  conv => lhs; arg 1; rw [show 94+fuel=1+(9+(1+(13+(1+(17+(1+(38+(1+(11+(1+fuel)))))))))) by omega,Nat.add_comm 1 (9+(1+(13+(1+(17+(1+(38+(1+(11+(1+fuel))))))))))]
  change Builtins.run (9+(1+(13+(1+(17+(1+(38+(1+(11+(1+fuel)))))))))) {base with
    control:=.statement (sourceStatement 0)
    continuation:=.statementList (successBody.drop 1) none::base.continuation}=_
  refine (source_sold (withContinuation entry (.statementList (successBody.drop 1) none::base.continuation))
    (1+(13+(1+(17+(1+(38+(1+(11+(1+fuel)))))))))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (13+(1+(17+(1+(38+(1+(11+(1+fuel))))))))]
  change Builtins.run (13+(1+(17+(1+(38+(1+(11+(1+fuel)))))))) {entry.afterSold with
    control:=.statement (sourceStatement 1)
    continuation:=.statementList (successBody.drop 2) (some (.number entry.sold))::base.continuation}=_
  refine (source_moni (withContinuation entry (.statementList (successBody.drop 2) (some (.number entry.sold))::base.continuation))
    (1+(17+(1+(38+(1+(11+(1+fuel)))))))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (17+(1+(38+(1+(11+(1+fuel))))))]
  change Builtins.run (17+(1+(38+(1+(11+(1+fuel)))))) {entry.afterMoni with
    control:=.statement (sourceStatement 2)
    continuation:=.statementList (successBody.drop 3) (some (.number entry.newMoni))::base.continuation}=_
  refine (source_cookies (withContinuation entry (.statementList (successBody.drop 3) (some (.number entry.newMoni))::base.continuation))
    (1+(38+(1+(11+(1+fuel)))))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (38+(1+(11+(1+fuel))))]
  change Builtins.run (38+(1+(11+(1+fuel)))) {entry.afterCookies with
    control:=.statement (sourceStatement 3)
    continuation:=.statementList (successBody.drop 4) (some (.number entry.newCookies))::base.continuation}=_
  refine (source_earned (withContinuation entry (.statementList (successBody.drop 4) (some (.number entry.newCookies))::base.continuation))
    (1+(11+(1+fuel)))).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 (11+(1+fuel))]
  change Builtins.run (11+(1+fuel)) {entry.afterEarned with
    control:=.statement (sourceStatement 4)
    continuation:=.statementList (successBody.drop 5) (some (.number entry.newEarned))::base.continuation}=_
  refine (source_amount (withContinuation entry (.statementList (successBody.drop 5) (some (.number entry.newEarned))::base.continuation))
    (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SaleNumericSource

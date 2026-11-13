import CookieClicker.JavaScriptUnlockArrayCall
import CookieClicker.JavaScriptArrayPairShape
import CookieClicker.JavaScriptArrayPairCall

namespace CookieClicker.JavaScript.UnlockPair
open UnlockArrayWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Inputs (base : Machine) (first second : JSString) where
  left : UnlockFrame.Frame first Number.one
  right : UnlockFrame.Frame second Number.one
  objects : base.heap.objects=left.objects
  rightObjects : right.objects=left.objects
  game : right.game=left.game
  window : right.window=left.window
  scopes : HasEnvironment.Scopes left.window
  environments : base.heap.environments=scopes.environments
  global : base.globalObject=left.window
  exclusions : base.objectEnvironmentExclusions=[]
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (UnlockInvocation.closure scopes.closureScope source)
  gameUnlock : lookupProperty base.heap left.game (JSString.ofString "Unlock")=
    .ok (some (.data (.object function) true true true))
  gameRead : SourceRead.Reads base (.identifier "Game") (.object left.game) 3
  prototype : ObjectId
  proto : base.arrayPrototype=some prototype
  parent : List EnumerationShape
  parentShape : enumerationShape base.heap (base.heap.objects.size+1) prototype=.ok parent
  hidden : ∀ pair∈parent.flatMap EnumerationShape.keys,pair.2=false

def before {base : Machine} {first second : JSString} (_ : Inputs base first second) : Machine :=
  ArrayPair.after base first second

theorem game_present {base : Machine} {first second : JSString} (i : Inputs base first second) :
    checkedObject base.heap i.left.game=.ok i.left.gameObject := by
  simp [checkedObject,Heap.object?,i.objects,i.left.gameRead]

theorem window_present {base : Machine} {first second : JSString} (i : Inputs base first second) :
    checkedObject base.heap i.left.window=.ok i.left.windowObject := by
  simp [checkedObject,Heap.object?,i.objects,i.left.windowRead]

theorem window_game {base : Machine} {first second : JSString} (i : Inputs base first second) :
    lookupProperty base.heap i.left.window (JSString.ofString "Game")=
      .ok (some (.data (.object i.left.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,i.objects,i.left.windowRead,
    i.left.windowKnown,i.left.windowGame,Except.bind,bind,Except.pure,pure]

def world {base : Machine} {first second : JSString} (i : Inputs base first second) : World (before i) := {
  window:=i.left.window,game:=i.left.game,array:=base.heap.objects.size,function:=i.function,source:=i.source
  scopes:=i.scopes,windowObject:=i.left.windowObject,functionObject:=i.functionObject
  arrayObject:=ArrayPair.object base first second
  windowPresent:=HeapExtension.checked_object (ArrayPair.extension base first second) _ _ (window_present i)
  windowKind:=i.left.windowKind
  windowGame:=HeapExtension.lookup_property (ArrayPair.extension base first second) _ _ _ (window_game i)
  functionPresent:=HeapExtension.checked_object (ArrayPair.extension base first second) _ _ i.functionPresent
  functionKind:=i.functionKind
  gameUnlock:={
    object:=i.left.gameObject
    present:=HeapExtension.checked_object (ArrayPair.extension base first second) _ _ (game_present i)
    kind:=Or.inl i.left.gameKind
    property:=HeapExtension.lookup_property (ArrayPair.extension base first second) _ _ _ i.gameUnlock }
  arrayPresent:=ArrayPair.checked_push base.heap (ArrayPair.object base first second)
  arrayKind:=rfl }

def leftRow {base : Machine} {first second : JSString} (i : Inputs base first second) : Row (world i) := {
  key:=JSString.ofString "0",name:=first,entry:=ArrayPair.first_property base first second
  frame:=extendFrame base (before i) i.left i.objects (ArrayPair.extension base first second)
  game:=rfl,window:=rfl,objects:=rfl }

def rightRow {base : Machine} {first second : JSString} (i : Inputs base first second) : Row (world i) := {
  key:=JSString.ofString "1",name:=second,entry:=ArrayPair.second_property base first second
  frame:=extendFrame base (before i) i.right (i.objects.trans i.rightObjects.symm) (ArrayPair.extension base first second)
  game:=i.game,window:=i.window,objects:=rfl }

def rows {base : Machine} {first second : JSString} (i : Inputs base first second) : List (Row (world i)) :=
  [leftRow i,rightRow i]

def shape {base : Machine} {first second : JSString} (i : Inputs base first second) : List EnumerationShape :=
  ArrayPair.ownShape base::i.parent

theorem shape_found {base : Machine} {first second : JSString} (i : Inputs base first second) :
    enumerationShape (before i).heap ((before i).heap.objects.size+1) (world i).array=.ok (shape i) :=
  ArrayPair.actual_shape base first second i.prototype i.parent i.proto i.parentShape

theorem shape_keys {base : Machine} {first second : JSString} (i : Inputs base first second) :
    enumerationNames (shape i)=(rows i).map Row.key :=
  ArrayPair.names base i.parent i.hidden

def returned {base : Machine} {first second : JSString} (i : Inputs base first second) : Machine :=
  UnlockArrayCall.returned (rows i)

end CookieClicker.JavaScript.UnlockPair

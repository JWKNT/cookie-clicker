import CookieClicker.JavaScriptArrayPair
import CookieClicker.JavaScriptEnumerationFrame

namespace CookieClicker.JavaScript.ArrayPair
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def ownShape (base : Machine) : EnumerationShape :=
  ⟨base.heap.objects.size,base.arrayPrototype,
    [(JSString.ofString "length",false),(JSString.ofString "0",true),(JSString.ofString "1",true)],none⟩

theorem own_keys (base : Machine) : (ownShape base).keys=
    [(JSString.ofString "0",true),(JSString.ofString "1",true),(JSString.ofString "length",false)] := by
  change orderedKeys
    [(JSString.ofString "length",false),(JSString.ofString "0",true),(JSString.ofString "1",true)] none=_
  cbv

theorem fold_non_enumerable (pairs : List (JSString × Bool))
    (all : ∀ pair∈pairs,pair.2=false) (seen names : List JSString) :
    (pairs.foldl (fun (seen,names) (key,enumerable) =>
      if seen.contains key then (seen,names)
      else (seen++[key],if enumerable then names++[key] else names)) (seen,names)).2=names := by
  induction pairs generalizing seen with
  | nil => rfl
  | cons pair pairs ih =>
    obtain ⟨key,enumerable⟩:=pair
    have no:=all (key,enumerable) (by simp)
    change enumerable=false at no
    subst enumerable
    have rest : ∀ pair∈pairs,pair.2=false := by intro pair member;exact all pair (by simp [member])
    simp only [List.foldl_cons,Bool.false_eq_true,↓reduceIte]
    split <;> exact ih rest _

theorem names (base : Machine) (parent : List EnumerationShape)
    (hidden : ∀ pair∈parent.flatMap EnumerationShape.keys,pair.2=false) :
    enumerationNames (ownShape base::parent)=[JSString.ofString "0",JSString.ofString "1"] := by
  unfold enumerationNames
  rw [List.flatMap_cons,own_keys,List.foldl_append]
  change ((parent.flatMap EnumerationShape.keys).foldl _
    ([JSString.ofString "0",JSString.ofString "1",JSString.ofString "length"],
     [JSString.ofString "0",JSString.ofString "1"])).2=_
  exact fold_non_enumerable _ hidden _ _

theorem extension (base : Machine) (first second : JSString) :
    HeapExtension.Extends base.heap (after base first second).heap :=
  HeapExtension.append_object base.heap (object base first second)

theorem actual_shape (base : Machine) (first second : JSString) (prototype : ObjectId)
    (parent : List EnumerationShape) (proto : base.arrayPrototype=some prototype)
    (found : enumerationShape base.heap (base.heap.objects.size+1) prototype=.ok parent) :
    enumerationShape (after base first second).heap ((after base first second).heap.objects.size+1)
      base.heap.objects.size=.ok (ownShape base::parent) := by
  have inherited:=EnumerationFrame.shape_of_extension (extension base first second)
    (base.heap.objects.size+1) (base.heap.objects.size+1) (Nat.le_refl _) prototype parent found
  simp only [after,Array.size_push]
  rw [enumerationShape]
  simp only [checked_push,object,Except.bind,bind,Except.pure,pure]
  simp only [Bool.not_true,Bool.not_false,Bool.or_false,Bool.false_eq_true,↓reduceIte,List.isEmpty_nil]
  simp only [after,object,proto] at inherited
  simp only [proto,Except.bind,bind]
  rw [inherited]
  simp only [Except.bind,bind,Except.pure,pure,ownShape,rawOwnKeys,enumerationStringLength,proto]
  rfl

theorem first_property (base : Machine) (first second : JSString) :
    lookupProperty (after base first second).heap base.heap.objects.size (JSString.ofString "0")=
      .ok (some (.data (.string first) true true true)) := by
  have own : ownProperty (object base first second) (JSString.ofString "0")=
      some (.data (.string first) true true true) := rfl
  simp only [lookupProperty,after,Array.size_push]
  rw [findProperty]
  simp only [checked_push,Except.bind,bind]
  simp only [show (object base first second).unresolvedOwnNames=[] from rfl,List.not_mem_nil,↓reduceIte,own]
  rfl

theorem second_property (base : Machine) (first second : JSString) :
    lookupProperty (after base first second).heap base.heap.objects.size (JSString.ofString "1")=
      .ok (some (.data (.string second) true true true)) := by
  have own : ownProperty (object base first second) (JSString.ofString "1")=
      some (.data (.string second) true true true) := rfl
  simp only [lookupProperty,after,Array.size_push]
  rw [findProperty]
  simp only [checked_push,Except.bind,bind]
  simp only [show (object base first second).unresolvedOwnNames=[] from rfl,List.not_mem_nil,↓reduceIte,own]
  rfl

end CookieClicker.JavaScript.ArrayPair

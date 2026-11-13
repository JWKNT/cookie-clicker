import CookieClicker.JavaScriptArc4GenerateRead

/-! The retained source expression through its first state-array swap.
Both index updates and the picked byte assignment occur in native order. -/
namespace CookieClicker.JavaScript.Arc4GenerateBody
open Arc4Generate Arc4GeneratorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def loop : Stmt := match SeedrandomArc4Syntax.generatorBody with
  | .block (statement::_) => statement
  | _ => .empty
def test : Expr := match loop with
  | .forLoop _ (some test) _ _ => test
  | _ => .literal (.boolean false)
def body : Stmt := match loop with
  | .forLoop _ _ _ body => body
  | _ => .empty

def secondSwap : Expr := .assignment .assign (.member (.identifier "h") (.identifier "g") true) (.identifier "b")
def start (i : Arc4Generate.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (objects i) (argument i) (initialValues i) (.statement body)
    (.forBody (some test) none body [] previous :: tail)
def firstWrite (i : Arc4Generate.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (objects i) (argument i) (updatedValues i)
    (.putValue ⟨.property (.object (array i)) (MixkeyIndex.key (fIndex i)),false⟩ (.number (Number.ofNat (moved i))))
    (.binaryLeft .add secondSwap :: .binaryRight .bitAnd (.number (Number.ofNat 255)) ::
      .memberProperty (.object (array i)) :: .binaryRight .add (.number (product i)) ::
      .assignmentRight .assign ⟨.environment (localIndex (source i)) "c",false⟩ none ::
      .sequence [] :: .expressionStatement :: .forBody (some test) none body [] previous :: tail)

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.mul
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty writeProperty source objects argument array count oldB accumulator oldF oldG fIndex picked gIndex moved
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c read_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h
  f_key g_key Arc4Schedule.native_add native_mul native_f_mask_literal native_g_mask
  Arc4GenerateRead.native_picked Arc4GenerateRead.native_moved

theorem actual_first_prefix (i : Arc4Generate.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (99+fuel) (start i previous tail)=Builtins.run fuel (firstWrite i previous tail) := by
  rw [Nat.add_comm 99 fuel]
  cbv

end CookieClicker.JavaScript.Arc4GenerateBody

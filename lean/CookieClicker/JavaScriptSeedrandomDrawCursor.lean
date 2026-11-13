import CookieClicker.JavaScriptSeedrandomDrawGenerator

/-! A source random cursor retains a checked callable generator after each
actual byte call. The heap updates follow the source call result. -/
namespace CookieClicker.JavaScript.SeedrandomDrawCursor
open SeedrandomDrawLocals SeedrandomDrawBacking SeedrandomDrawGenerator
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] RetainedArc4GenerateComplete.finished

structure Cursor where
  frame : SeedrandomDrawSource.Frame
  generator : Generator frame.source frame.objects

theorem initial_source (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId) :
    (initialFrame i objects g argument).source=i := rfl

theorem initial_objects (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId) :
    (initialFrame i objects g argument).objects=nextObjects i objects g argument {} #[] 6 (by decide) := rfl

attribute [local irreducible] initialFrame nextObjects nextHistory output returnedGenerator

def initial (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId) : Cursor := {
  frame := {
    source := i,objects := nextObjects i objects g argument {} #[] 6 (by decide),argument := argument
    history := nextHistory i objects g argument {} #[] 6 (by decide)
    a := output i objects g argument {} #[] 6 (by decide),b := Number.ofNat (2^48),c := Number.positiveZero }
  generator := returnedGenerator i objects g argument {} #[] 6 (by decide) }

def grownValues (cursor : Cursor) := SeedrandomDrawSource.values (SeedrandomDrawCalls.grown cursor.frame)
def beforeByte (cursor : Cursor) : SeedrandomDrawSource.Frame := {
  source := cursor.frame.source
  objects := nextObjects cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (grownValues cursor) cursor.frame.history 1 (by decide)
  argument := cursor.frame.argument
  history := nextHistory cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (grownValues cursor) cursor.frame.history 1 (by decide)
  a := Number.mul (Number.add cursor.frame.a cursor.frame.c) (Number.ofNat 256)
  b := Number.mul cursor.frame.b (Number.ofNat 256)
  c := cursor.frame.c }
def byte (cursor : Cursor) :=
  output cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (grownValues cursor) cursor.frame.history 1 (by decide)
def next (cursor : Cursor) : Cursor := by
  refine ⟨SeedrandomDrawCalls.afterByte (beforeByte cursor) (byte cursor),?_⟩
  change Generator cursor.frame.source
    (nextObjects cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
      (grownValues cursor) cursor.frame.history 1 (by decide))
  exact returnedGenerator cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (grownValues cursor) cursor.frame.history 1 (by decide)

theorem actual_growth_body (cursor : Cursor) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (283+fuel) (SeedrandomDrawSource.growthAtBody cursor.frame previous tail)=
      Builtins.run fuel (SeedrandomDrawSource.growthStart (next cursor).frame (some (.number (byte cursor))) tail) := by
  let f := cursor.frame
  let grown := SeedrandomDrawCalls.grown f
  let g := cursor.generator
  rw [show 283+fuel=45+((3+(229+(5+fuel)))+1) by omega,SeedrandomDrawCalls.actual_growth_prefix]
  change Builtins.run (3+(229+(5+fuel)))
    (Builtins.builtinStep (SeedrandomDrawCalls.growthRead f previous tail))=_
  rw [SeedrandomDrawCalls.actual_growth_read _ g.callee _ _ g.object g.instanceRead g.shape.kind g.shape.unresolved g.methodRead,
    SeedrandomDrawCalls.actual_growth_invoke]
  change Builtins.run (136*1+93+(5+fuel))
    (machine grown.source grown.objects grown.argument (SeedrandomDrawSource.values grown) grown.history
      (.invoke (.object g.callee) (.object grown.source.generator) [.number (Number.ofNat 1)] false)
      (SeedrandomDrawCalls.growthCallTail f previous tail))=_
  rw [actual_complete_call grown.source grown.objects g grown.argument (SeedrandomDrawSource.values grown) grown.history 1 (by decide)]
  exact SeedrandomDrawCalls.actual_growth_after (beforeByte cursor) (byte cursor) previous tail fuel

def projectGenerator {i : Inputs} {objects : Array JSObject} (g : Generator i objects) : CookieClicker.Arc4Orbit.State :=
  ⟨fun b => g.arrayFrame.bytes b.toNat,g.oldF,g.oldG⟩

theorem returned_project (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :
    projectGenerator (returnedGenerator i objects g argument v history count small)=
      FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next count (projectGenerator g) := by
  unfold projectGenerator returnedGenerator
  change RetainedArc4SourceOrbit.project
    (RetainedArc4GeneratorMemory.completed (Call i objects g argument v history count small)).cursor=_
  unfold RetainedArc4GeneratorMemory.completed RetainedArc4GeneratorBodyComplete.completed
  rw [RetainedArc4GenerateComplete.finished]
  exact RetainedArc4SourceOrbit.project_traverse count
    (RetainedArc4GeneratorBodyComplete.initial
      (RetainedArc4GeneratorCall.initialized (Call i objects g argument v history count small))) (Nat.le_refl count)

theorem output_one (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) :
    output i objects g argument v history 1 (by decide)=
      Number.ofNat (CookieClicker.Arc4Orbit.output (projectGenerator g)).toNat := by
  unfold output
  let input := Call i objects g argument v history 1 (by decide)
  let cursor := RetainedArc4GeneratorInitialize.cursor (RetainedArc4GeneratorCall.initialized input)
  change (RetainedArc4GenerateComplete.finished
    (RetainedArc4GeneratorBodyComplete.initial (RetainedArc4GeneratorCall.initialized input))).cursor.accumulator=_
  rw [RetainedArc4GenerateComplete.finished]
  change (RetainedArc4GenerateCursor.next cursor).accumulator=_
  rw [RetainedArc4GenerateCursor.next_accumulator,RetainedArc4SourceOrbit.actual_output]
  change Number.add (Number.mul 0 (Number.ofNat 256))
    (Number.ofNat (CookieClicker.Arc4Orbit.output (projectGenerator g)).toNat)=_
  rw [show Number.mul 0 (Number.ofNat 256)=Number.ofNat 0 by decide +kernel]
  apply NaturalArithmetic.native_add_zero_left
  have small := (CookieClicker.Arc4Orbit.output (projectGenerator g)).toNat_lt
  omega

def project (cursor : Cursor) : SeedrandomNormalizationLoops.State :=
  ⟨cursor.frame.a,cursor.frame.b,cursor.frame.c,projectGenerator cursor.generator⟩

theorem project_next (cursor : Cursor) : project (next cursor)=SeedrandomNormalizationLoops.growthStep (project cursor) := by
  have generator := returned_project cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (SeedrandomDrawSource.values (SeedrandomDrawCalls.grown cursor.frame)) cursor.frame.history 1 (by decide)
  have value := output_one cursor.frame.source cursor.frame.objects cursor.generator cursor.frame.argument
    (SeedrandomDrawSource.values (SeedrandomDrawCalls.grown cursor.frame)) cursor.frame.history
  simp only [project,next,beforeByte,SeedrandomDrawCalls.afterByte,byte,grownValues,id]
  rw [value,generator]
  rfl

end CookieClicker.JavaScript.SeedrandomDrawCursor

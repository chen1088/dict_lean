import DictatorshipTesting.Paper.Defs.S02_IntDef_IsPreimageDictator
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_HammingDist`
- `DictatorshipTesting.Paper.S02_Thm2_01_BooleanU1Classification`
- `DictatorshipTesting.Paper.S04_Lem4_07_IndependentRepetition`
-/
/-!
Definition file for `IsDictator`.
-/

noncomputable section

namespace DictatorshipTesting

/-- The paper's dictator class `𝓓`. -/
def IsDictator {α : Type*} (f : BoolFn α) : Prop :=
  IsImageDictator f ∨ IsPreimageDictator f

end DictatorshipTesting

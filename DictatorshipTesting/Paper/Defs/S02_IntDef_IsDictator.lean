import DictatorshipTesting.Paper.Defs.S02_IntDef_IsPreimageDictator
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_HammingDist`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
- `DictatorshipTesting.Paper.S02_Thm2_01_BooleanU1Classification`
-/


/-!
Definition file for `IsDictator`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The paper's dictator class `𝓓`. -/
def IsDictator {α : Type*} (f : BoolFn α) : Prop :=
  IsImageDictator f ∨ IsPreimageDictator f

end DictatorshipTesting

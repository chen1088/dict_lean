import DictatorshipTesting.Paper.Defs.S02_Def2_05_IsPreimageDictator

/-!
Definition file for `IsDictator`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The paper's dictator class `𝓓`. -/
def IsDictator {α : Type*} (f : BoolFn α) : Prop :=
  IsImageDictator f ∨ IsPreimageDictator f

end DictatorshipTesting

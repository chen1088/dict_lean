import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Definition 5.18
Title in paper: Matching characters.

Status: re-exports the cube character model currently used for matching-cube
Fourier calculations.
-/

noncomputable section

namespace DictatorshipTesting

/-- Matching-cube character in the current Lean model. -/
abbrev S05_matchingCharacter {m : Nat} (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  cubeChar S x

end DictatorshipTesting

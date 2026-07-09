import DictatorshipTesting.Paper.S03_Def3_11_CubeLowDegreeOnePart

/-!
Definition file for `cubeHighDegreeEnergy`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Fourier energy on coefficients of degree at least two. -/
def cubeHighDegreeEnergy {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => 2 ≤ S.card)),
    (cubeFourierCoeff g S) ^ (2 : ℕ)

end DictatorshipTesting

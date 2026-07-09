import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Aux_CubeFourierTranslate`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion`
- `DictatorshipTesting.Paper.S05_Def5_15_MatchingCharacters`
-/


namespace DictatorshipTesting

/-- A Boolean-cube character squares to `1`. -/
theorem cubeChar_mul_self {m : ℕ} (S : Finset (Fin m)) (x : Cube m) :
    cubeChar S x * cubeChar S x = 1 := by
  unfold cubeChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro r _hr
  by_cases hx : x r <;> simp [hx]

end DictatorshipTesting

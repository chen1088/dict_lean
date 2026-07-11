import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeChar

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_11a_MatchingCharacters`
- `DictatorshipTesting.Paper.S02_Int_CubeFourierTranslate`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion`
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

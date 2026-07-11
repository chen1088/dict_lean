import DictatorshipTesting.Paper.Defs.S02_Def2_02a_CubeLowDegreeOnePart
import DictatorshipTesting.Paper.S02_Int_CubeFourierTranslate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection`
-/


/-!
# Lemma 4.2: The definition of `P_M` is independent of representatives
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 4.2: the definition of `P_M` is independent of representatives. -/
theorem S04_Lem4_02_PMIndependentOfRepresentatives {m : ℕ}
    (g : Cube m → ℝ) (z x : Cube m) :
    cubeLowDegreeOnePart (fun y => g (cubeXor z y)) x =
      cubeLowDegreeOnePart g (cubeXor z x) := by
  unfold cubeLowDegreeOnePart
  apply Finset.sum_congr rfl
  intro S _hS
  rw [cubeFourierCoeff_xor_left, cubeChar_cubeXor]
  ring

end DictatorshipTesting

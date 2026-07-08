import DictatorshipTesting.Paper.Aux_CubeFourierTranslate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Aux_MatchingLocalProjection`
-/

/-!
# Lemma 4.4: The definition of `P_M` is independent of representatives

The paper counter skips Lemmas 4.2 and 4.3 because those numbers are definitions.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 4.4: the definition of `P_M` is independent of representatives. -/
theorem L4_4_PMIndependentOfRepresentatives {m : ℕ}
    (g : Cube m → ℝ) (z x : Cube m) :
    cubeLowDegreeOnePart (fun y => g (cubeXor z y)) x =
      cubeLowDegreeOnePart g (cubeXor z x) := by
  unfold cubeLowDegreeOnePart
  apply Finset.sum_congr rfl
  intro S _hS
  rw [cubeFourierCoeff_xor_left, cubeChar_cubeXor]
  ring

end DictatorshipTesting

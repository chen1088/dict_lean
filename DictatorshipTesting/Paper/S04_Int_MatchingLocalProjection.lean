import DictatorshipTesting.Paper.Defs.S04_Def4_02a_MatchingLocalProjection
import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauMul
import DictatorshipTesting.Paper.S04_Lem4_02_PMIndependentOfRepresentatives

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents`
- `DictatorshipTesting.Paper.S04_Lem4_03_PMFixesLocal`
- `DictatorshipTesting.Paper.S04_Lem4_04_LocalHighDegreeErrorFormula`
- `DictatorshipTesting.Paper.S04_Lem4_05_PMPerpendicular`
- `DictatorshipTesting.Paper.S05_Lem5_21_LocalTruncationOnAMatchingCharacter`
-/


/-!
# Auxiliary facts for the matching-local projection

These lemmas connect the concrete `matchingLocalProjection` definition with the
cube-low-degree truncation used in Lemma 4.3.
-/

noncomputable section

namespace DictatorshipTesting

/-- Restricting `P_M F` to a matching cube gives the low-degree-one truncation of
the corresponding restriction of `F`. -/
theorem matchingLocalProjection_apply_mul_tau {α : Type*} [Fintype α]
    [DecidableEq α] (M : OrderedMatching α) (F : Perm α → ℝ) (π : Perm α)
    (x : Cube M.edgeCount) :
    matchingLocalProjection M F (π * M.tau x) =
      cubeLowDegreeOnePart (fun y : Cube M.edgeCount => F (π * M.tau y)) x := by
  unfold matchingLocalProjection
  have hfun :
      (fun y : Cube M.edgeCount => F ((π * M.tau x) * M.tau y)) =
        fun y : Cube M.edgeCount => F (π * M.tau (cubeXor x y)) := by
    funext y
    rw [mul_assoc, orderedMatching_tau_mul]
  rw [hfun]
  simpa [cubeXor_zero] using
    (S04_Lem4_02_PMIndependentOfRepresentatives
      (g := fun y : Cube M.edgeCount => F (π * M.tau y))
      (z := x) (x := cubeZero M.edgeCount))

end DictatorshipTesting

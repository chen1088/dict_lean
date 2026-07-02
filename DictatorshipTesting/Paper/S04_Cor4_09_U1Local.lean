import DictatorshipTesting.Paper.Aux_MatchingLocalDegreeOneLinear
import DictatorshipTesting.Paper.S04_Lem4_05_PMFixesLocal
import DictatorshipTesting.Paper.S04_Lem4_08_TijLocalDegree

/-!
# Corollary 4.9: `U_1` is contained in every local degree-one space

This is `cor:U1-local` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Corollary 4.9, `cor:U1-local`: `U_1` is contained in each local degree-one space. -/
theorem Cor4_9_U1Local {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) (hF : F ∈ U1 α) :
    IsMatchingLocalDegreeOne F M ∧ matchingLocalProjection M F = F := by
  have hlocal : IsMatchingLocalDegreeOne F M := by
    unfold U1 at hF
    refine Submodule.span_induction
      (p := fun F _ => IsMatchingLocalDegreeOne F M)
      ?mem ?zero ?add ?smul hF
    · intro G hG
      rcases hG with ⟨ij, rfl⟩
      exact L4_8_TijLocalDegree M ij.1 ij.2
    · exact IsMatchingLocalDegreeOne_zero M
    · intro G H _hGmem _hHmem hG hH
      exact IsMatchingLocalDegreeOne_add hG hH
    · intro a G _hGmem hG
      exact IsMatchingLocalDegreeOne_smul a hG
  exact ⟨hlocal, (L4_5_PMFixesLocal F M).2 F hlocal⟩

end DictatorshipTesting

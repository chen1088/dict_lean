import DictatorshipTesting.Paper.Defs.S03_Def3_05_MatchingCubeRestriction
import DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauDepends

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S03_Lem3_02_PerfectCompleteness`
- `DictatorshipTesting.Paper.S04_Lem4_08_TijLocalDegree`
-/


/-!
# Lemma 3.1: Completeness on matching cubes

This is `lem:dictator-to-junta` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Image-dictator half of Lemma 3.1. -/
theorem L3_1_ImageDictatorToJunta {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsImageDictator f)
    (M : OrderedMatching α) (π : Perm α) :
    IsCubeOneJunta (matchingCubeRestriction f M π) := by
  rcases hf with ⟨i, h, hfi⟩
  by_cases hmatch : ∃ r : Fin M.edgeCount, M.InEdge r i
  · rcases hmatch with ⟨r, hri⟩
    right
    refine ⟨r, ?_⟩
    intro x y hxy
    simp only [matchingCubeRestriction]
    rw [hfi, hfi]
    congr 1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact congrArg π
      (orderedMatching_tau_apply_eq_of_same_bit_on_edge M hxy hri)
  · left
    intro x y
    simp only [matchingCubeRestriction]
    rw [hfi, hfi]
    congr 1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hleft : ∀ r : Fin M.edgeCount, i ≠ M.left r := by
      intro r hir
      exact hmatch ⟨r, Or.inl hir⟩
    have hright : ∀ r : Fin M.edgeCount, i ≠ M.right r := by
      intro r hir
      exact hmatch ⟨r, Or.inr hir⟩
    rw [orderedMatching_tau_apply_of_unmatched M x hleft hright,
      orderedMatching_tau_apply_of_unmatched M y hleft hright]

/-- Lemma 3.1, `lem:dictator-to-junta`: completeness on matching cubes. -/
theorem L3_1_DictatorToJunta {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsDictator f)
    (M : OrderedMatching α) (π : Perm α) :
    IsCubeOneJunta (matchingCubeRestriction f M π) := by
  rcases hf with himage | hpreimage
  · exact L3_1_ImageDictatorToJunta f himage M π
  · rcases hpreimage with ⟨j, h, hfj⟩
    let a : α := π.symm j
    by_cases hmatch : ∃ r : Fin M.edgeCount, M.InEdge r a
    · rcases hmatch with ⟨r, hra⟩
      right
      refine ⟨r, ?_⟩
      intro x y hxy
      simp only [matchingCubeRestriction]
      rw [hfj, hfj]
      congr 1
      calc
        (π * M.tau x).symm j = (M.tau x).symm (π.symm j) := by
          rfl
        _ = (M.tau y).symm (π.symm j) := by
          exact orderedMatching_tau_symm_apply_eq_of_same_bit_on_edge M hxy hra
        _ = (π * M.tau y).symm j := by
          rfl
    · left
      intro x y
      simp only [matchingCubeRestriction]
      rw [hfj, hfj]
      congr 1
      have hleft : ∀ r : Fin M.edgeCount, a ≠ M.left r := by
        intro r har
        exact hmatch ⟨r, Or.inl har⟩
      have hright : ∀ r : Fin M.edgeCount, a ≠ M.right r := by
        intro r har
        exact hmatch ⟨r, Or.inr har⟩
      calc
        (π * M.tau x).symm j = (M.tau x).symm (π.symm j) := by
          rfl
        _ = a := by
          exact orderedMatching_tau_symm_apply_of_unmatched M x hleft hright
        _ = (M.tau y).symm (π.symm j) := by
          exact (orderedMatching_tau_symm_apply_of_unmatched M y hleft hright).symm
        _ = (π * M.tau y).symm j := by
          rfl

end DictatorshipTesting

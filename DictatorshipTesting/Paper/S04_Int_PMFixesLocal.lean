import DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Int_PMPerpendicular`
-/


/-!
# Internal fixed-space theorem for matching-local truncation

This proof supplies part (a) of Proposition 4.3.
-/

namespace DictatorshipTesting

/-- `P_M` maps into, and fixes, the matching-local degree-one space. -/
theorem matchingLocalProjection_fixedSpace {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    IsMatchingLocalDegreeOne (matchingLocalProjection M F) M ∧
      ∀ H : Perm α → ℝ,
        IsMatchingLocalDegreeOne H M → matchingLocalProjection M H = H := by
  constructor
  · intro π
    have hfun :
        (fun x : Cube M.edgeCount =>
          matchingLocalProjection M F (π * M.tau x)) =
            cubeLowDegreeOnePart
              (fun y : Cube M.edgeCount => F (π * M.tau y)) := by
      funext x
      exact matchingLocalProjection_apply_mul_tau M F π x
    rw [hfun]
    exact cubeHighDegreeEnergy_cubeLowDegreeOnePart_eq_zero _
  · intro H hH
    funext π
    unfold matchingLocalProjection
    have hlow :
        cubeLowDegreeOnePart
          (fun x : Cube M.edgeCount => H (π * M.tau x)) =
            (fun x : Cube M.edgeCount => H (π * M.tau x)) :=
      cubeLowDegreeOnePart_eq_self_of_cubeHighDegreeEnergy_eq_zero (hH π)
    have hzero := orderedMatching_tau_zero M
    simpa [hzero] using congrFun hlow (cubeZero M.edgeCount)

end DictatorshipTesting

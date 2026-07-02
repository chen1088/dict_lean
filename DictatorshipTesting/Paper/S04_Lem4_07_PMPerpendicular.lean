import DictatorshipTesting.Paper.Aux_CubeInnerProduct
import DictatorshipTesting.Paper.Aux_MatchingLocalProjection
import DictatorshipTesting.Paper.Aux_PermCubeAverage
import DictatorshipTesting.Paper.S04_Lem4_05_PMFixesLocal

/-!
# Lemma 4.7: High local degrees have zero inner product with local degree one

This is `lem:PM-perpendicular` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 4.7, `lem:PM-perpendicular`: high local degrees are perpendicular to local degree one. -/
theorem L4_7_PMPerpendicular {α : Type*} [Fintype α] [DecidableEq α]
    (F H : Perm α → ℝ) (M : OrderedMatching α)
    (hH : IsMatchingLocalDegreeOne H M) :
    permInner (fun π => F π - matchingLocalProjection M F π) H = 0 ∧
      permInner F (fun π => F π - matchingLocalProjection M F π) =
        matchingLocalProjectionError F M := by
  classical
  let P : Perm α → ℝ := matchingLocalProjection M F
  let R : Perm α → ℝ := fun π => F π - P π
  have horth :
      ∀ K : Perm α → ℝ, IsMatchingLocalDegreeOne K M → permInner R K = 0 := by
    intro K hK
    unfold permInner
    have hsum : (∑ σ : Perm α, R σ * K σ) = 0 := by
      rw [← sum_perm_cube_right_tau_div_card M
        (fun σ : Perm α => R σ * K σ)]
      apply Finset.sum_eq_zero
      intro π _hπ
      have hcube :
          cubeExpectation
            (fun x : Cube M.edgeCount =>
              ((fun y : Cube M.edgeCount => F (π * M.tau y)) x -
                cubeLowDegreeOnePart
                  (fun y : Cube M.edgeCount => F (π * M.tau y)) x) *
                (fun y : Cube M.edgeCount => K (π * M.tau y)) x) = 0 :=
        cubeExpectation_lowDegreeResidual_mul_of_highDegreeEnergy_eq_zero
          (g := fun y : Cube M.edgeCount => F (π * M.tau y))
          (h := fun y : Cube M.edgeCount => K (π * M.tau y))
          (hK π)
      unfold cubeExpectation at hcube
      calc
        (∑ x : Cube M.edgeCount, R (π * M.tau x) * K (π * M.tau x)) /
            (Fintype.card (Cube M.edgeCount) : ℝ)
            =
            (∑ x : Cube M.edgeCount,
                (F (π * M.tau x) -
                  cubeLowDegreeOnePart
                    (fun y : Cube M.edgeCount => F (π * M.tau y)) x) *
                  K (π * M.tau x)) /
              (Fintype.card (Cube M.edgeCount) : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro x _hx
              dsimp [R, P]
              rw [matchingLocalProjection_apply_mul_tau]
        _ = 0 := hcube
    simp [hsum]
  constructor
  · exact horth H hH
  · have hP : IsMatchingLocalDegreeOne P M := (L4_5_PMFixesLocal F M).1
    have hRP : permInner R P = 0 := horth P hP
    have hN : (Fintype.card (Perm α) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Perm α) ≠ 0)
    unfold permInner at hRP
    have hsumRP : (∑ π : Perm α, R π * P π) = 0 := by
      field_simp [hN] at hRP
      simpa using hRP
    unfold permInner matchingLocalProjectionError l2DistSq
    dsimp [R, P] at hsumRP ⊢
    congr 1
    calc
      (∑ π : Perm α,
          F π * (F π - matchingLocalProjection M F π))
          =
          ∑ π : Perm α,
            ((F π - matchingLocalProjection M F π) ^ (2 : ℕ) +
              matchingLocalProjection M F π *
                (F π - matchingLocalProjection M F π)) := by
            apply Finset.sum_congr rfl
            intro π _hπ
            ring
      _ =
          (∑ π : Perm α,
            (F π - matchingLocalProjection M F π) ^ (2 : ℕ)) +
          (∑ π : Perm α,
            matchingLocalProjection M F π *
              (F π - matchingLocalProjection M F π)) := by
            rw [Finset.sum_add_distrib]
      _ =
          ∑ π : Perm α,
            (F π - matchingLocalProjection M F π) ^ (2 : ℕ) := by
            have hsumPR :
                (∑ π : Perm α,
                  matchingLocalProjection M F π *
                    (F π - matchingLocalProjection M F π)) = 0 := by
              calc
                (∑ π : Perm α,
                  matchingLocalProjection M F π *
                    (F π - matchingLocalProjection M F π))
                    =
                    ∑ π : Perm α,
                      (F π - matchingLocalProjection M F π) *
                        matchingLocalProjection M F π := by
                      apply Finset.sum_congr rfl
                      intro π _hπ
                      ring
                _ = 0 := hsumRP
            simp [hsumPR]

end DictatorshipTesting

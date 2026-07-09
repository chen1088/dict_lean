import DictatorshipTesting.Paper.Defs.S03_Def3_18_MatchingLocalProjectionError
import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection
import DictatorshipTesting.Paper.S04_Int_PermCubeAverage
import DictatorshipTesting.Paper.S04_Lem4_03_PMFixesLocal

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
# Lemma 4.5: High local degrees have zero inner product with local degree one

This is `lem:PM-perpendicular` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Cube inner product in the Fourier basis. -/
theorem cubeExpectation_mul_eq_sum_fourierCoeff {m : ℕ}
    (g h : Cube m → ℝ) :
    cubeExpectation (fun x : Cube m => g x * h x) =
      ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeFourierCoeff h S := by
  classical
  let N : ℝ := Fintype.card (Cube m)
  calc
    cubeExpectation (fun x : Cube m => g x * h x)
        =
        cubeExpectation
          (fun x : Cube m =>
            g x * (∑ S : Finset (Fin m),
              cubeFourierCoeff h S * cubeChar S x)) := by
          congr
          ext x
          rw [← L2_3_cubeFourier_expansion m h x]
    _ = ∑ S : Finset (Fin m), cubeFourierCoeff h S *
          cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
          calc
            cubeExpectation
                (fun x : Cube m =>
                  g x * (∑ S : Finset (Fin m),
                    cubeFourierCoeff h S * cubeChar S x))
                =
                (∑ x : Cube m,
                  g x * (∑ S : Finset (Fin m),
                    cubeFourierCoeff h S * cubeChar S x)) / N := by
                    simp [cubeExpectation, N]
            _ = (∑ x : Cube m,
                  ∑ S : Finset (Fin m),
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x _hx
                    rw [Finset.mul_sum]
            _ = (∑ S : Finset (Fin m),
                  ∑ x : Cube m,
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    rw [Finset.sum_comm]
            _ = ∑ S : Finset (Fin m),
                  (∑ x : Cube m,
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    rw [Finset.sum_div]
            _ = ∑ S : Finset (Fin m), cubeFourierCoeff h S *
                  cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
                    apply Finset.sum_congr rfl
                    intro S _hS
                    unfold cubeExpectation
                    calc
                      (∑ x : Cube m,
                          g x * (cubeFourierCoeff h S * cubeChar S x)) / N
                          =
                          (cubeFourierCoeff h S *
                            (∑ x : Cube m, g x * cubeChar S x)) / N := by
                            congr 1
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro x _hx
                            ring
                      _ = cubeFourierCoeff h S *
                            ((∑ x : Cube m, g x * cubeChar S x) / N) := by
                            ring
                      _ = cubeFourierCoeff h S *
                            ((∑ x : Cube m, g x * cubeChar S x) /
                              (Fintype.card (Cube m) : ℝ)) := by
                            simp [N]
    _ = ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeFourierCoeff h S := by
          apply Finset.sum_congr rfl
          intro S _hS
          unfold cubeFourierCoeff
          ring

/-- The high-degree residual is orthogonal to every degree-at-most-one cube
function. -/
theorem cubeExpectation_lowDegreeResidual_mul_of_highDegreeEnergy_eq_zero
    {m : ℕ} (g h : Cube m → ℝ) (hh : cubeHighDegreeEnergy h = 0) :
    cubeExpectation
        (fun x : Cube m => (g x - cubeLowDegreeOnePart g x) * h x) = 0 := by
  rw [cubeExpectation_mul_eq_sum_fourierCoeff]
  apply Finset.sum_eq_zero
  intro S _hS
  by_cases hhigh : 2 ≤ S.card
  · have hcoeff :
        cubeFourierCoeff h S = 0 :=
      cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hh hhigh
    simp [cubeFourierCoeff_lowDegreeResidual, hhigh, hcoeff]
  · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]

/-- Lemma 4.5, `lem:PM-perpendicular`: high local degrees are perpendicular to local degree one. -/
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

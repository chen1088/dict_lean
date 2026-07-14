import DictatorshipTesting.Paper.Defs.S02_Def2_02a_CubeLowDegreeOnePart
import DictatorshipTesting.Paper.S02_Int_CubeFourierTranslate
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval
import DictatorshipTesting.Paper.Defs.S04_Def4_01_MatchingLocalDegreeOneAndProjection
import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import DictatorshipTesting.Paper.S04_Int_PermCubeAverage

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents`
- `DictatorshipTesting.Paper.S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne`
- `DictatorshipTesting.Paper.S04_Prop4_05_SquareEnergyControlsGlobalDegree`
- `DictatorshipTesting.Paper.S05_Lem5_14_MatchingFourierProjections`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/

/-!
# Proposition 4.2: Cosetwise description of `P_M`

The construction is independent of coset representatives and is the
orthogonal projection onto the matching-local degree-one space.
-/

noncomputable section

namespace DictatorshipTesting

/-- Proposition 4.2: the definition of `P_M` is independent of representatives. -/
theorem S04_Prop4_02_PMIndependentOfRepresentatives {m : ℕ}
    (g : Cube m → ℝ) (z x : Cube m) :
    cubeLowDegreeOnePart (fun y => g (cubeXor z y)) x =
      cubeLowDegreeOnePart g (cubeXor z x) := by
  unfold cubeLowDegreeOnePart
  apply Finset.sum_congr rfl
  intro S _hS
  rw [cubeFourierCoeff_xor_left, cubeChar_cubeXor]
  ring

/-- Restricting `P_M F` to a matching cube gives the low-degree-one truncation
of the corresponding restriction of `F`. -/
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
    (S04_Prop4_02_PMIndependentOfRepresentatives
      (g := fun y : Cube M.edgeCount => F (π * M.tau y))
      (z := x) (x := cubeZero M.edgeCount))

/-- Proposition 4.2(a): `P_M` maps into, and fixes, the local degree-one space. -/
theorem S04_Prop4_02_fixedSpace {α : Type*} [Fintype α] [DecidableEq α]
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

/-- Proposition 4.2(b): the projection error is the local high-degree energy. -/
theorem S04_Prop4_02_errorFormula {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M = matchingLocalHighDegreeEnergy F M := by
  classical
  unfold matchingLocalProjectionError matchingLocalHighDegreeEnergy l2DistSq
  congr 1
  symm
  calc
    (∑ π : Perm α,
        cubeHighDegreeEnergy (fun x : Cube M.edgeCount => F (π * M.tau x)))
        =
        ∑ π : Perm α,
          cubeExpectation
            (fun x : Cube M.edgeCount =>
              (F (π * M.tau x) -
                cubeLowDegreeOnePart
                  (fun y : Cube M.edgeCount => F (π * M.tau y)) x) ^
                (2 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro π _hπ
          rw [← cubeExpectation_sq_sub_cubeLowDegreeOnePart_eq_highDegreeEnergy]
    _ =
        ∑ π : Perm α,
          (∑ x : Cube M.edgeCount,
              (F (π * M.tau x) -
                cubeLowDegreeOnePart
                  (fun y : Cube M.edgeCount => F (π * M.tau y)) x) ^
                (2 : ℕ)) /
            (Fintype.card (Cube M.edgeCount) : ℝ) := by
          rfl
    _ =
        ∑ π : Perm α,
          (∑ x : Cube M.edgeCount,
              (F (π * M.tau x) -
                matchingLocalProjection M F (π * M.tau x)) ^ (2 : ℕ)) /
            (Fintype.card (Cube M.edgeCount) : ℝ) := by
          apply Finset.sum_congr rfl
          intro π _hπ
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          rw [matchingLocalProjection_apply_mul_tau]
    _ =
        ∑ π : Perm α,
          (F π - matchingLocalProjection M F π) ^ (2 : ℕ) := by
          exact
            sum_perm_cube_right_tau_div_card M
              (fun σ : Perm α =>
                (F σ - matchingLocalProjection M F σ) ^ (2 : ℕ))

private theorem cubeExpectation_mul_eq_sum_fourierCoeff {m : ℕ}
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
          rw [← S02_Lem2_03_cubeFourier_expansion m h x]
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

private theorem cubeExpectation_lowDegreeResidual_mul_of_highDegreeEnergy_eq_zero
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

/-- Proposition 4.2(c): the residual is perpendicular to the fixed space. -/
theorem S04_Prop4_02_perpendicular {α : Type*} [Fintype α] [DecidableEq α]
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
  · have hP : IsMatchingLocalDegreeOne P M := (S04_Prop4_02_fixedSpace F M).1
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

/-- Proposition 4.2, `prop:PM-orthogonal-projection`, in its combined form. -/
theorem S04_Prop4_02_CosetwiseDescriptionOfPM
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    (IsMatchingLocalDegreeOne (matchingLocalProjection M F) M ∧
      ∀ H : Perm α → ℝ,
        IsMatchingLocalDegreeOne H M → matchingLocalProjection M H = H) ∧
    matchingLocalProjectionError F M = matchingLocalHighDegreeEnergy F M ∧
    (∀ H : Perm α → ℝ,
      IsMatchingLocalDegreeOne H M →
        permInner (fun π => F π - matchingLocalProjection M F π) H = 0) ∧
    permInner F (fun π => F π - matchingLocalProjection M F π) =
      matchingLocalProjectionError F M := by
  have hfixed := S04_Prop4_02_fixedSpace F M
  refine ⟨hfixed, S04_Prop4_02_errorFormula F M, ?_, ?_⟩
  · intro H hH
    exact (S04_Prop4_02_perpendicular F H M hH).1
  · exact
      (S04_Prop4_02_perpendicular F (matchingLocalProjection M F) M hfixed.1).2

end DictatorshipTesting

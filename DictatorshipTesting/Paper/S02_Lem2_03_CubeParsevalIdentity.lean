import DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper`
- `DictatorshipTesting.Paper.Aux_CubeLowDegreeError`
- `DictatorshipTesting.Paper.Aux_CubeSquareSpectralFormula`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval`
-/

/-!
# Lemma 2.3: cube Parseval identity

This proves the third displayed identity in `lem:cube-parseval`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The Parseval part of Lemma 2.3, `lem:cube-parseval`. -/
theorem L2_3_cubeParseval_identity (m : ℕ) :
    ∀ g : Cube m → ℝ,
      cubeExpectation (fun x : Cube m => g x ^ (2 : ℕ)) =
        ∑ S : Finset (Fin m), (cubeFourierCoeff g S) ^ (2 : ℕ) := by
  intro g
  classical
  let N : ℝ := Fintype.card (Cube m)
  calc
    cubeExpectation (fun x : Cube m => g x ^ (2 : ℕ))
        =
        cubeExpectation
          (fun x : Cube m =>
            g x * (∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x)) := by
          congr
          ext x
          rw [← L2_3_cubeFourier_expansion m g x]
          ring
    _ = ∑ S : Finset (Fin m), cubeFourierCoeff g S *
          cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
          calc
            cubeExpectation
                (fun x : Cube m =>
                  g x * (∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x))
                =
                (∑ x : Cube m,
                  g x * (∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x)) / N := by
                    simp [cubeExpectation, N]
            _ = (∑ x : Cube m,
                  ∑ S : Finset (Fin m),
                    g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x _
                    rw [Finset.mul_sum]
            _ = (∑ S : Finset (Fin m),
                  ∑ x : Cube m,
                    g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                    rw [Finset.sum_comm]
            _ = ∑ S : Finset (Fin m),
                  (∑ x : Cube m,
                    g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                    rw [Finset.sum_div]
            _ = ∑ S : Finset (Fin m), cubeFourierCoeff g S *
                  cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
                    apply Finset.sum_congr rfl
                    intro S _
                    unfold cubeExpectation
                    calc
                      (∑ x : Cube m,
                          g x * (cubeFourierCoeff g S * cubeChar S x)) / N
                          =
                          (cubeFourierCoeff g S *
                            (∑ x : Cube m, g x * cubeChar S x)) / N := by
                            congr 1
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro x _
                            ring
                      _ = cubeFourierCoeff g S *
                            ((∑ x : Cube m, g x * cubeChar S x) / N) := by
                            ring
                      _ = cubeFourierCoeff g S *
                            ((∑ x : Cube m, g x * cubeChar S x) /
                              (Fintype.card (Cube m) : ℝ)) := by
                            simp [N]
    _ = ∑ S : Finset (Fin m), (cubeFourierCoeff g S) ^ (2 : ℕ) := by
          simp [cubeFourierCoeff, pow_two]

end DictatorshipTesting

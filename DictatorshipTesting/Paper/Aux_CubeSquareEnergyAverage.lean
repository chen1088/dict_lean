import DictatorshipTesting.Paper.Defs

/-!
# Rearranging the square-test energy average
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The square-test energy can be viewed as first averaging over the cube for
each color choice, and then averaging over colors. -/
theorem cubeSquareEnergy_eq_color_average {m : ℕ} (g : Cube m → ℝ) :
    cubeSquareEnergy g =
      (∑ c : CubeDirectionColor m,
        cubeExpectation
          (fun x : Cube m =>
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ))) /
        (Fintype.card (CubeDirectionColor m) : ℝ) := by
  unfold cubeSquareEnergy cubeExpectation
  calc
    (∑ x : Cube m,
        (∑ c : CubeDirectionColor m,
          (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
      (Fintype.card (Cube m) : ℝ)
        =
        ((∑ x : Cube m,
          ∑ c : CubeDirectionColor m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [← Finset.sum_div]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [Finset.sum_comm]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (Cube m) : ℝ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          ring_nf
    _ =
        (∑ c : CubeDirectionColor m,
          (∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
              (Fintype.card (Cube m) : ℝ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ) := by
          rw [Finset.sum_div]

end DictatorshipTesting

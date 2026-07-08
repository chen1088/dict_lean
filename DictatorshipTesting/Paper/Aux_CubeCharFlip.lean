import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality`
- `DictatorshipTesting.Paper.S04_Lem4_08_TijLocalDegree`
-/

namespace DictatorshipTesting

/-- Flipping a coordinate in the character support negates that character. -/
theorem cubeChar_cubeFlip {m : ℕ} (S : Finset (Fin m)) (r : Fin m)
    (hr : r ∈ S) (x : Cube m) :
    cubeChar S (cubeFlip r x) = -cubeChar S x := by
  unfold cubeChar
  rw [← Finset.mul_prod_erase S
    (fun q => if cubeFlip r x q then (-1 : ℝ) else 1) (a := r) hr]
  rw [← Finset.mul_prod_erase S
    (fun q => if x q then (-1 : ℝ) else 1) (a := r) hr]
  have hprod :
      (∏ q ∈ S.erase r, if cubeFlip r x q then (-1 : ℝ) else 1) =
        ∏ q ∈ S.erase r, if x q then (-1 : ℝ) else 1 := by
    apply Finset.prod_congr rfl
    intro q hq
    have hqr : q ≠ r := (Finset.mem_erase.mp hq).1
    simp [cubeFlip, hqr]
  rw [hprod]
  by_cases hx : x r <;> simp [cubeFlip, hx]

end DictatorshipTesting

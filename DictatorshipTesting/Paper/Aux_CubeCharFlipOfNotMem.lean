import DictatorshipTesting.Paper.Defs

namespace DictatorshipTesting

/-- Flipping a coordinate outside the character support leaves that character unchanged. -/
theorem cubeChar_cubeFlip_of_not_mem {m : ℕ} (S : Finset (Fin m)) (r : Fin m)
    (hr : r ∉ S) (x : Cube m) :
    cubeChar S (cubeFlip r x) = cubeChar S x := by
  unfold cubeChar
  apply Finset.prod_congr rfl
  intro q hq
  have hqr : q ≠ r := by
    intro h
    exact hr (h ▸ hq)
  simp [cubeFlip, hqr]

end DictatorshipTesting

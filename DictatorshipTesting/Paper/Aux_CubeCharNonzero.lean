import DictatorshipTesting.Paper.Defs

namespace DictatorshipTesting

/-- Boolean-cube characters take values in `{1,-1}`, hence are nonzero. -/
theorem cubeChar_ne_zero {m : ℕ} (S : Finset (Fin m)) (x : Cube m) :
    cubeChar S x ≠ 0 := by
  unfold cubeChar
  exact Finset.prod_ne_zero_iff.mpr (by
    intro r _hr
    by_cases h : x r <;> simp [h])

end DictatorshipTesting

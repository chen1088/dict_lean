import DictatorshipTesting.Paper.S03_Def3_27_MatchingHighConvolution

/-!
Definition file for `YoungDiagram`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Young diagram with `n` boxes, represented by its row lengths.  The row
vector has length `n`, which is enough because a partition of `n` has at most
`n` nonzero rows; each row length is bounded by `n`. -/
structure YoungDiagram (n : ℕ) where
  row : Fin n → Fin (n + 1)
  nonincreasing :
    ∀ {i j : Fin n}, (i : ℕ) ≤ (j : ℕ) → (row j : ℕ) ≤ (row i : ℕ)
  sum_rows : (∑ i : Fin n, (row i : ℕ)) = n
deriving DecidableEq

end DictatorshipTesting

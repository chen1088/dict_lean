import DictatorshipTesting.Basic

/-
Direct reverse imports:
- `DictatorshipTesting.BasicFacts`
-/


namespace DictatorshipTesting

variable {α : Type*} [DecidableEq α]

/-- `rowDict` is the same function as the sum of the one-coset indicators.

This is the first small counting lemma we should discharge.  The proof is a
one-line finite-set counting argument once the preferred Mathlib lemma for
`∑ j in J, if π i = j then 1 else 0` is chosen.
-/
lemma rowDictAsCosetSum_eq_rowDict
    (i : α) (J : Finset α) (π : Perm α) :
    rowDictAsCosetSum i J π = rowDict i J π := by
  classical
  simp [rowDictAsCosetSum, rowDict, oneCoset]

end DictatorshipTesting

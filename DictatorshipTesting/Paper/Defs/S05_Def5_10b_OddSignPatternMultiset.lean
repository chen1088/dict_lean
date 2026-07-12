import DictatorshipTesting.Paper.Defs.S05_Def5_10a_EvenSignPatternMultiset
import DictatorshipTesting.Paper.Defs.S05_IntDef_HOdd

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_SignPatternCardinalities`
-/


/-!
Paper statement: Definition 5.10 part (b) `def:matching-sign-patterns`
Title in paper: Matching sign-pattern multisets and heights.

Status: definition/interface. The odd multiset is the multiplicity-preserving
union of the even multisets over one-box children. The older scalar shadow
`hOdd` remains available for the alternate `youngDim` certificate route.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Definition 5.10: the recursive multiset of matching-character labels for
an odd Young diagram, obtained by taking the multiset union over all one-box
children. -/
noncomputable def S05_oddSignPatternMultiset
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Multiset (Finset (Fin m)) :=
  (oneBoxChildrenOdd m lam).sum
    (fun mu => S05_evenSignPatternMultiset m mu)

/-- High-weight count from the odd sign-pattern multiset. -/
abbrev S05_oddHighSignPatternCount
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  hOdd m lam

/-- Definition 5.10 scalar shadow: odd high-weight entries are summed over
one-box removals to even shapes. -/
theorem S05_oddHighSignPatternCount_eq_evenHigh_sum
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_oddHighSignPatternCount m lam =
      (oneBoxChildrenOdd m lam).sum
        (fun mu => S05_evenHighSignPatternCount m mu) := by
  simp [S05_oddHighSignPatternCount, S05_evenHighSignPatternCount, hOdd]

end DictatorshipTesting

import DictatorshipTesting.Paper.S05_Def5_17_EvenSignPatternMultiset

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_21_SizesOfTheSignPatternMultisets`
-/


/-!
Paper statement: Definition 5.18 (`def:odd-sign-patterns`)
Title in paper: Odd sign-pattern multiset.

Status: definition/interface. The current finite scaffold records the high-weight count extracted
from the odd sign-pattern multiset as `hOdd`.
-/

noncomputable section

namespace DictatorshipTesting

/-- High-weight count from the odd sign-pattern multiset. -/
abbrev S05_oddHighSignPatternCount
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  hOdd m lam

/-- Definition 5.18 scalar shadow: odd high-weight entries are summed over
one-box removals to even shapes. -/
theorem S05_oddHighSignPatternCount_eq_evenHigh_sum
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_oddHighSignPatternCount m lam =
      (oneBoxChildrenOdd m lam).sum
        (fun mu => S05_evenHighSignPatternCount m mu) := by
  simp [S05_oddHighSignPatternCount, S05_evenHighSignPatternCount, hOdd]

end DictatorshipTesting

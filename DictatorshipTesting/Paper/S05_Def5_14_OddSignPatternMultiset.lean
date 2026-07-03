import DictatorshipTesting.Paper.S05_Def5_13_EvenSignPatternMultiset

/-!
Paper statement: Definition 5.14
Title in paper: Odd sign-pattern multiset.

Status: the current finite scaffold records the high-weight count extracted
from the odd sign-pattern multiset as `hOdd`.
-/

noncomputable section

namespace DictatorshipTesting

/-- High-weight count from the odd sign-pattern multiset. -/
abbrev S05_oddHighSignPatternCount
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  hOdd m lam

end DictatorshipTesting

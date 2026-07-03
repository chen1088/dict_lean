import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Definition 5.13
Title in paper: Even sign-pattern multiset.

Status: the current finite scaffold records the two counts extracted from the
even sign-pattern multiset: zero-weight entries `zEven` and high-weight entries
`hEven`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Zero-weight count from the even sign-pattern multiset. -/
abbrev S05_evenZeroSignPatternCount :
    (m : Nat) -> YoungDiagram (2 * m) -> ℝ :=
  zEven

/-- High-weight count from the even sign-pattern multiset. -/
abbrev S05_evenHighSignPatternCount :
    (m : Nat) -> YoungDiagram (2 * m) -> ℝ :=
  hEven

end DictatorshipTesting

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

/-- Definition 5.13 scalar shadow: the empty even diagram has one zero-weight
entry. -/
theorem S05_evenZeroSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenZeroSignPatternCount 0 lam = 1 := by
  simp [S05_evenZeroSignPatternCount, zEven]

/-- Definition 5.13 scalar shadow: zero-weight entries recurse through
horizontal two-strip removals. -/
theorem S05_evenZeroSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenZeroSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => S05_evenZeroSignPatternCount m mu) := by
  simp [S05_evenZeroSignPatternCount, zEven]

/-- Definition 5.13 scalar shadow: the empty even diagram has no high-weight
entries. -/
theorem S05_evenHighSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenHighSignPatternCount 0 lam = 0 := by
  simp [S05_evenHighSignPatternCount, hEven]

/-- Definition 5.13 scalar shadow: high-weight entries recurse through the
horizontal branch and the vertical nonzero contribution. -/
theorem S05_evenHighSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenHighSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => S05_evenHighSignPatternCount m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => youngDim mu - S05_evenZeroSignPatternCount m mu) := by
  simp [S05_evenHighSignPatternCount, S05_evenZeroSignPatternCount, hEven]

end DictatorshipTesting

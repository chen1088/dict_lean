import DictatorshipTesting.Paper.Defs.S05_IntDef_HEven
import DictatorshipTesting.Paper.Defs.S05_Def5_07a_TwoBoxRemovals

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_10b_OddSignPatternMultiset`
- `DictatorshipTesting.Paper.Defs.S05_Def5_11a_MatchingCharacters`
- `DictatorshipTesting.Paper.S05_Lem5_12_BranchingDimensionsAndSignPatternCardinalities`
- `DictatorshipTesting.Paper.S05_Lem5_13_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_17_CountingOneMoreMatchingEdge`
- `DictatorshipTesting.Paper.S05_Lem5_18_WeightZeroEntriesAreNeverAMajority`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenCertificate`
- `DictatorshipTesting.Paper.S05_Lem5_20_OddCertificate`
-/
/-!
Paper statement: Definition 5.10 part (a) `def:matching-sign-patterns`
Title in paper: Matching sign-pattern multisets and heights.

Status: definition/interface. The multiset itself is represented as a
`Multiset (Finset (Fin m))`, so repeated character labels retain their
multiplicity. The older scalar shadows `zEven` and `hEven` remain available
for the alternate `youngDim` certificate route.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Embed a matching-character label on `m` edges into the first `m` edges of
an `(m+1)`-edge matching. -/
def S05_liftEvenSignPattern {m : Nat}
    (R : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  R.map Fin.castSuccEmb

/-- Extend a matching-character label by assigning negative sign to the new
last matching edge. -/
def S05_liftEvenSignPatternWithLast {m : Nat}
    (R : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  insert (Fin.last m) (S05_liftEvenSignPattern R)

/-- Definition 5.10: the recursive multiset of matching-character labels for
an even Young diagram. Horizontal two-strip children keep the old label, while
vertical two-strip children add the new last matching edge. -/
noncomputable def S05_evenSignPatternMultiset :
    (m : Nat) -> YoungDiagram (2 * m) -> Multiset (Finset (Fin m))
  | 0, _ => ({Finset.empty} : Multiset (Finset (Fin 0)))
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu =>
            (S05_evenSignPatternMultiset m mu).map S05_liftEvenSignPattern) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu =>
            (S05_evenSignPatternMultiset m mu).map
              S05_liftEvenSignPatternWithLast)

/-- Multiplicity of weight-zero labels in a sign-pattern multiset. -/
def S05_zeroSignPatternMultiplicity {m : Nat}
    (X : Multiset (Finset (Fin m))) : Nat :=
  X.countP (fun R => R.card = 0)

/-- Multiplicity of labels of weight at least two in a sign-pattern multiset. -/
def S05_highSignPatternMultiplicity {m : Nat}
    (X : Multiset (Finset (Fin m))) : Nat :=
  X.countP (fun R => 2 <= R.card)

/-- Zero-weight count from the even sign-pattern multiset. -/
abbrev S05_evenZeroSignPatternCount :
    (m : Nat) -> YoungDiagram (2 * m) -> ℝ :=
  zEven

/-- High-weight count from the even sign-pattern multiset. -/
abbrev S05_evenHighSignPatternCount :
    (m : Nat) -> YoungDiagram (2 * m) -> ℝ :=
  hEven

/-- Definition 5.10 scalar shadow: the empty even diagram has one zero-weight
entry. -/
theorem S05_evenZeroSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenZeroSignPatternCount 0 lam = 1 := by
  simp [S05_evenZeroSignPatternCount, zEven]

/-- Definition 5.10 scalar shadow: zero-weight entries recurse through
horizontal two-strip removals. -/
theorem S05_evenZeroSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenZeroSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => S05_evenZeroSignPatternCount m mu) := by
  simp [S05_evenZeroSignPatternCount, zEven]

/-- Definition 5.10 scalar shadow: the empty even diagram has no high-weight
entries. -/
theorem S05_evenHighSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenHighSignPatternCount 0 lam = 0 := by
  simp [S05_evenHighSignPatternCount, hEven]

/-- Definition 5.10 scalar shadow: high-weight entries recurse through the
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

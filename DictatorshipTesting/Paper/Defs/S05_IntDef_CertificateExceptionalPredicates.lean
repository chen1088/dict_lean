import DictatorshipTesting.Paper.Defs.S05_IntDef_IsStandard
import DictatorshipTesting.Paper.Defs.S05_IntDef_OneBoxChildrenOdd

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_24_WeightZeroEntriesAreNeverAMajority`
- `DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate`
- `DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate`
-/

/-!
Internal predicates naming the finite-certificate child obstructions and
exceptional shapes used in Lemmas 5.23--5.26.
-/

noncomputable section

namespace DictatorshipTesting

/-- A diagram has a horizontal two-strip child that is the one-row diagram.  This
is the exact obstruction to applying the induction hypothesis uniformly to all
horizontal children in the proof of the `zEven` bound. -/
def HasOneRowHorizontalChild (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  ∃ mu ∈ horizontalTwoStripChildrenEven m lam, IsOneRow mu

/-- Row predicate for the exceptional two-row shape `(2m-2, 2)`. -/
def IsTwoRowTwoException (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  youngRow lam 0 = 2 * m - 2 ∧ youngRow lam 1 = 2

/-- A diagram has a vertical two-strip child that is one-row. -/
def HasOneRowVerticalChild (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  ∃ mu ∈ verticalTwoStripChildrenEven m lam, IsOneRow mu

/-- A diagram has a horizontal two-strip child that is standard. -/
def HasStandardHorizontalChild (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  ∃ mu ∈ horizontalTwoStripChildrenEven m lam, IsStandard mu

/-- Row predicate for the exceptional shape `(2m-2, 1, 1)`. -/
def IsTwoRowOneOneException (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  youngRow lam 0 = 2 * m - 2 ∧ youngRow lam 1 = 1 ∧ youngRow lam 2 = 1

/-- Row predicate for the exceptional shape `(2m-3, 3)`. -/
def IsTwoRowThreeException (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  youngRow lam 0 = 2 * m - 3 ∧ youngRow lam 1 = 3

/-- Row predicate for the exceptional shape `(2m-3, 2, 1)`. -/
def IsThreeRowTwoOneException (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  youngRow lam 0 = 2 * m - 3 ∧ youngRow lam 1 = 2 ∧ youngRow lam 2 = 1

/-- The four exceptional even shapes from the paper:
`(2m-2,2)`, `(2m-2,1,1)`, `(2m-3,3)`, and `(2m-3,2,1)`. -/
def IsEvenHExceptional (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  IsTwoRowTwoException m lam ∨
    IsTwoRowOneOneException m lam ∨
      IsTwoRowThreeException m lam ∨
        IsThreeRowTwoOneException m lam

/-- A diagram has a one-box child that is one-row. -/
def HasOneRowOneBoxChild (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  ∃ mu ∈ oneBoxChildrenOdd m lam, IsOneRow mu

/-- A diagram has a one-box child that is standard. -/
def HasStandardOneBoxChild (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  ∃ mu ∈ oneBoxChildrenOdd m lam, IsStandard mu

/-- Row predicate for the odd exceptional shape `(2m-1,2)`. -/
def IsOddTwoRowTwoException (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  youngRow lam 0 = 2 * m - 1 ∧ youngRow lam 1 = 2

/-- Row predicate for the odd exceptional shape `(2m-1,1,1)`. -/
def IsOddTwoRowOneOneException (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  youngRow lam 0 = 2 * m - 1 ∧ youngRow lam 1 = 1 ∧ youngRow lam 2 = 1

/-- The two exceptional odd shapes from the paper: `(2m-1,2)` and
`(2m-1,1,1)`. -/
def IsOddHExceptional (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  IsOddTwoRowTwoException m lam ∨ IsOddTwoRowOneOneException m lam

end DictatorshipTesting

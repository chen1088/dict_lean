import DictatorshipTesting.Paper.S05_Lem5_13_MatchingSubgroupEigenbasis
import DictatorshipTesting.Paper.Defs.S05_IntDef_TraceLocalTruncationEvenInput
import DictatorshipTesting.Paper.Defs.S05_IntDef_TraceLocalTruncationOddInput
import DictatorshipTesting.Paper.Defs.S05_Def5_12d_TableauOperatorTrace
import DictatorshipTesting.Paper.S05_Lem5_14_MatchingFourierProjections
import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
/-!
Paper statement: Lemma 5.15 (`lem:PM-trace-young-block`)
Title in paper: Trace of one local truncation on one Young block.

Status: proven. The positive-size even and all odd applications are instantiated
unconditionally from Lemma 5.13's arbitrary-matching bases.
-/

/-!
# Trace of one local truncation

Assuming the matching-restriction data, the trace of `I - P_M` on a Young block
is obtained by counting high-weight matching characters.  The paper's factor is

`tr((I - P_M)|_{H_lambda}) = d_lambda * h_m(lambda)`.

The extra factor `d_lambda` comes from the block
`H_lambda ≃ S^lambda ⊗ (S^lambda)^*`: the restricted Specht multiplicities occur
in `d_lambda` matrix-coefficient copies.  The current Lean vocabulary does not
yet contain these Young blocks as vector spaces, so this file records the
scalar trace formula used by the later bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Concrete operator reduction for Lemma 5.15: the fixed high-matching trace
is the sum of the traces of its high-character Fourier idempotents. -/
theorem S05_Lem5_15_fixedMatching_trace_eq_sum_characterTraces
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
        tableauOperatorTrace
          (S05_fixedMatchingCharacterYoungOperator action M R) := by
  exact S05_fixedMatchingRejectionYoungOperator_trace_eq_sum_characters
    action M

/-- Concrete multiplicity reduction for Lemma 5.15: right action on the full
matrix-coordinate Young block contributes one identical trace for each left
tableau index. -/
theorem S05_Lem5_15_youngBlockTrace_eq_tableauDim_mul_repTrace
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam *
        tableauOperatorTrace
          (S05_fixedMatchingRejectionYoungOperator action M) := by
  exact fixedMatchingYoungBlockTrace_eq_tableauDim_mul_repTrace action M

/-- Even tableau-space trace formula for the actual fixed-matching operator,
from exactly the matching eigenbasis and high-label count asserted in Lemma
5.10. -/
theorem S05_Lem5_15_fixedMatching_tableauTrace_even_of_eigenbasis
    {n m : Nat} (hsize : n + 1 = 2 * m)
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Real (TableauSpace lam))
    (label : ι -> Finset (Fin M.toOrdered.edgeCount))
    (heigen : forall i x,
      action.rep.rho (M.toOrdered.tau x) (b i) =
        cubeChar (label i) x • b i)
    (hcount :
      (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
          hEvenTableau m (hsize ▸ lam)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      hEvenTableau m (hsize ▸ lam) := by
  rw [fixedMatchingRejectionYoungOperator_trace_eq_highLabelCount_of_eigenbasis
    action M b label heigen]
  exact hcount

/-- Odd tableau-space trace formula for the actual fixed-matching operator,
from exactly the matching eigenbasis and high-label count asserted in Lemma
5.10. -/
theorem S05_Lem5_15_fixedMatching_tableauTrace_odd_of_eigenbasis
    {n m : Nat} (hsize : n + 1 = 2 * m + 1)
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Real (TableauSpace lam))
    (label : ι -> Finset (Fin M.toOrdered.edgeCount))
    (heigen : forall i x,
      action.rep.rho (M.toOrdered.tau x) (b i) =
        cubeChar (label i) x • b i)
    (hcount :
      (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
          hOddTableau m (hsize ▸ lam)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      hOddTableau m (hsize ▸ lam) := by
  rw [fixedMatchingRejectionYoungOperator_trace_eq_highLabelCount_of_eigenbasis
    action M b label heigen]
  exact hcount

/-- Even full Young-block trace formula.  The free left tableau index supplies
the factor `tableauDim`. -/
theorem S05_Lem5_15_fixedMatching_youngBlockTrace_even_of_eigenbasis
    {n m : Nat} (hsize : n + 1 = 2 * m)
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Real (TableauSpace lam))
    (label : ι -> Finset (Fin M.toOrdered.edgeCount))
    (heigen : forall i x,
      action.rep.rho (M.toOrdered.tau x) (b i) =
        cubeChar (label i) x • b i)
    (hcount :
      (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
          hEvenTableau m (hsize ▸ lam)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam * hEvenTableau m (hsize ▸ lam) := by
  rw [S05_Lem5_15_youngBlockTrace_eq_tableauDim_mul_repTrace action M]
  rw [S05_Lem5_15_fixedMatching_tableauTrace_even_of_eigenbasis
    hsize action M b label heigen hcount]

/-- Odd full Young-block trace formula.  The free left tableau index supplies
the factor `tableauDim`. -/
theorem S05_Lem5_15_fixedMatching_youngBlockTrace_odd_of_eigenbasis
    {n m : Nat} (hsize : n + 1 = 2 * m + 1)
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Real (TableauSpace lam))
    (label : ι -> Finset (Fin M.toOrdered.edgeCount))
    (heigen : forall i x,
      action.rep.rho (M.toOrdered.tau x) (b i) =
        cubeChar (label i) x • b i)
    (hcount :
      (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
          hOddTableau m (hsize ▸ lam)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam * hOddTableau m (hsize ▸ lam) := by
  rw [S05_Lem5_15_youngBlockTrace_eq_tableauDim_mul_repTrace action M]
  rw [S05_Lem5_15_fixedMatching_tableauTrace_odd_of_eigenbasis
    hsize action M b label heigen hcount]

/-- Unconditional positive-size even tableau trace, using the transported
arbitrary-perfect-matching basis from Lemma 5.13. -/
theorem S05_Lem5_15_fixedMatching_tableauTrace_even
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      hEvenTableau (m + 1) lam := by
  exact S05_Lem5_15_fixedMatching_tableauTrace_even_of_eigenbasis
    (n := 2 * m + 1) (m := m + 1) rfl action M
    (S05_arbitraryEvenMatchingBasis m lam action M)
    (fun i => S05_arbitraryEvenMatchingLabel (m + 1) M
      (S05_canonicalEvenEigenbasisLabel (m + 1) lam i))
    (S05_arbitraryEvenMatchingBasis_toOrdered_character_action
      m lam action M)
    (S05_arbitraryEvenMatchingBasis_highLabelCount (m + 1) lam M)

/-- Unconditional positive-size even full Young-block trace. -/
theorem S05_Lem5_15_fixedMatching_youngBlockTrace_even
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam * hEvenTableau (m + 1) lam := by
  rw [S05_Lem5_15_youngBlockTrace_eq_tableauDim_mul_repTrace action M]
  rw [S05_Lem5_15_fixedMatching_tableauTrace_even m lam action M]

/-- Unconditional odd tableau trace, using the arbitrary near-perfect-matching
basis from Lemma 5.13. -/
theorem S05_Lem5_15_fixedMatching_tableauTrace_odd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      hOddTableau m lam := by
  exact S05_Lem5_15_fixedMatching_tableauTrace_odd_of_eigenbasis
    (n := 2 * m) (m := m) rfl action M
    (S05_arbitraryOddMatchingBasis m lam action M)
    (fun i => S05_arbitraryOddMatchingLabel m M
      (S05_canonicalOddEigenbasisLabel m lam i))
    (S05_arbitraryOddMatchingBasis_toOrdered_character_action
      m lam action M)
    (S05_arbitraryOddMatchingBasis_highLabelCount m lam M)

/-- Unconditional odd full Young-block trace. -/
theorem S05_Lem5_15_fixedMatching_youngBlockTrace_odd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam * hOddTableau m lam := by
  rw [S05_Lem5_15_youngBlockTrace_eq_tableauDim_mul_repTrace action M]
  rw [S05_Lem5_15_fixedMatching_tableauTrace_odd m lam action M]

/-- Scalar trace formula as the current Lean consequence of the even
matching-restriction input. -/
theorem traceLocalTruncation_even_from_restriction
    (m : ℕ) (_hrestrict : MatchingRestrictionEvenInput m) :
    TraceLocalTruncationEvenInput m := by
  intro lam
  exact ⟨youngDim lam * hEven m lam, rfl⟩

/-- Scalar trace formula as the current Lean consequence of the odd
matching-restriction input. -/
theorem traceLocalTruncation_odd_from_restriction
    (m : ℕ) (_hrestrict : MatchingRestrictionOddInput m) :
    TraceLocalTruncationOddInput m := by
  intro lam
  exact ⟨youngDim lam * hOdd m lam, rfl⟩

end DictatorshipTesting

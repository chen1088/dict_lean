import DictatorshipTesting.Paper.S05_Int_YoungMatchingOperators
import DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction
import DictatorshipTesting.Paper.Defs.S05_Def5_08_SignedTwoBoxExtensionSpaces
import DictatorshipTesting.Paper.Defs.S05_Def5_11a_MatchingCharacters
import DictatorshipTesting.Paper.Defs.S05_Def5_11b_IsMatchingEigenvectorEven
import DictatorshipTesting.Paper.Defs.S05_Def5_11c_IsMatchingEigenvectorOdd
import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionEvenInput
import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionOddInput
import DictatorshipTesting.Paper.S05_Lem5_13_SignedTwoBoxOrthogonalBranching
import DictatorshipTesting.Paper.S05_Lem5_14_OneBoxDecompositionAndDeletion
import DictatorshipTesting.Paper.S05_Lem5_15_BranchingDimensionsAndSignPatternCardinalities
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauOddHeight
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData
import DictatorshipTesting.Paper.Defs.S05_Def5_12c_AveragedHighMatchingElement
import DictatorshipTesting.Paper.Defs.S05_Def5_10a_EvenSignPatternMultiset

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_18_TraceOfOneLocalTruncationOnOneYoungBlock`
-/


/-!
Paper statement: Lemma 5.16 (`lem:matching-restriction-X`)
Title in paper: Matching subgroup eigenbasis.

The concrete matching-operator and sign-projection interfaces are proved below.
The signed two-box child embeddings are explicit, isometric, pairwise
orthogonal, and jointly spanning. Lemma 5.15 supplies the recursive label
multisets and cardinality identities. The canonical even labeled matching
eigenbasis is recursively constructed below, with literal multiset equality of
its labels. The explicit endpoint permutation and
represented isometry now transport it to every arbitrary perfect matching.
The canonical odd basis is also constructed explicitly from the one-box
fibers, with orthonormality, spanning, matching eigenvalues, and literal odd
label multiplicities, and an explicit unmatched-point permutation transports
it to every arbitrary near-perfect matching.
-/

/-!
# Matching-restriction scalar shadow

The paper's full statement says that, after restricting the Specht module
indexed by `lambda` to the matching subgroup `A_M ≃ (Z / 2Z)^m`, the local
character-weight multiset is the recursively defined multiset counted by
`zEven`, `hEven`, and `hOdd`.

The signed two-box child spaces, one-box fibers, and their orthogonal
decompositions are constructed internally below. The recursive labeled bases
are packaged as Mathlib bases and transported by explicit conjugating
permutations in both parity cases. Their labels are identified with the exact
recursive multisets, not only with their cardinalities.
-/

noncomputable section

namespace DictatorshipTesting

local instance S05_standardYoungTableauDecidableEq
    {n : Nat} {lam : YoungDiagram n} :
    DecidableEq (StandardYoungTableau lam) :=
  Classical.decEq _

local instance S05_adjacentSameRowDecidable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameRow T a) :=
  Classical.propDecidable _

local instance S05_adjacentSameColDecidable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameCol T a) :=
  Classical.propDecidable _

/-- The ordered two-box extension sends a child basis vector to its explicit
parent extension basis vector. -/
theorem S05_twoStepExtensionEmbedding_basis
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    S05_twoStepExtensionEmbedding lam p (tableauBasisVec U) =
      tableauBasisVec (S05_Lem5_13_twoBoxExtensionTableau lam p U) := by
  classical
  funext T
  rw [S05_twoStepExtensionEmbedding]
  rw [Fintype.sum_eq_single U]
  · simp [tableauBasisVec]
  · intro V hVU
    simp [tableauBasisVec, hVU]

/-- The ordered two-box extension is additive. -/
theorem S05_twoStepExtensionEmbedding_add
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f g : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    S05_twoStepExtensionEmbedding lam p (f + g) =
      S05_twoStepExtensionEmbedding lam p f +
        S05_twoStepExtensionEmbedding lam p g := by
  classical
  funext T
  simp only [S05_twoStepExtensionEmbedding, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- The ordered two-box extension commutes with real scalar multiplication. -/
theorem S05_twoStepExtensionEmbedding_smul
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) (c : Real)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    S05_twoStepExtensionEmbedding lam p (c • f) =
      c • S05_twoStepExtensionEmbedding lam p f := by
  classical
  funext T
  simp only [S05_twoStepExtensionEmbedding, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _hU
  ring

/-- Reading an extended coordinate at the extension of `U` recovers the child
coordinate at `U`. -/
theorem S05_twoStepExtensionEmbedding_apply_extension
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    S05_twoStepExtensionEmbedding lam p f
        (S05_Lem5_13_twoBoxExtensionTableau lam p U) =
      f U := by
  classical
  rw [S05_twoStepExtensionEmbedding]
  rw [Fintype.sum_eq_single U]
  · simp [tableauBasisVec]
  · intro V hVU
    have hExt :
        S05_Lem5_13_twoBoxExtensionTableau lam p V ≠
          S05_Lem5_13_twoBoxExtensionTableau lam p U := by
      intro h
      exact hVU (S05_Lem5_13_twoBoxExtensionTableau_injective lam p h)
    rw [tableauBasisVec_ne (Ne.symm hExt)]
    ring

/-- Child basis vectors remain orthonormal after ordered two-box extension. -/
theorem S05_twoStepExtensionEmbedding_basis_inner
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    tableauInner
        (S05_twoStepExtensionEmbedding lam p (tableauBasisVec U))
        (S05_twoStepExtensionEmbedding lam p (tableauBasisVec V)) =
      if U = V then 1 else 0 := by
  classical
  rw [S05_twoStepExtensionEmbedding_basis,
    S05_twoStepExtensionEmbedding_basis]
  by_cases hUV : U = V
  · subst V
    simp
  · have hExt :
        S05_Lem5_13_twoBoxExtensionTableau lam p U ≠
          S05_Lem5_13_twoBoxExtensionTableau lam p V := by
      intro h
      exact hUV (S05_Lem5_13_twoBoxExtensionTableau_injective lam p h)
    rw [tableauInner_basis_basis_ne hExt, if_neg hUV]

/-- Ordered two-box extension preserves the full coordinate inner product. -/
theorem S05_twoStepExtensionEmbedding_isometry
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f g : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    tableauInner
        (S05_twoStepExtensionEmbedding lam p f)
        (S05_twoStepExtensionEmbedding lam p g) =
      tableauInner f g := by
  classical
  rw [tableauInner, tableauInner]
  change
    (∑ T : StandardYoungTableau lam,
      S05_twoStepExtensionEmbedding lam p f T *
        (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          g U * tableauBasisVec
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) T)) =
      ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U * g U
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _hU
  have hright :
      (∑ T : StandardYoungTableau lam,
        S05_twoStepExtensionEmbedding lam p f T *
          tableauBasisVec (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) =
        S05_twoStepExtensionEmbedding lam p f
          (S05_Lem5_13_twoBoxExtensionTableau lam p U) := by
    simpa [tableauInner] using
      tableauInner_right_basis
        (S05_twoStepExtensionEmbedding lam p f)
        (S05_Lem5_13_twoBoxExtensionTableau lam p U)
  calc
    (∑ T : StandardYoungTableau lam,
        S05_twoStepExtensionEmbedding lam p f T *
          (g U * tableauBasisVec
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) T)) =
        g U *
          ∑ T : StandardYoungTableau lam,
            S05_twoStepExtensionEmbedding lam p f T *
              tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U) T := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _hT
          ring
    _ = g U * S05_twoStepExtensionEmbedding lam p f
          (S05_Lem5_13_twoBoxExtensionTableau lam p U) := by rw [hright]
    _ = f U * g U := by
      rw [S05_twoStepExtensionEmbedding_apply_extension]
      ring

/-- Ordered two-box extension is injective. -/
theorem S05_twoStepExtensionEmbedding_injective
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    Function.Injective (S05_twoStepExtensionEmbedding lam p) := by
  intro f g hfg
  funext U
  have hcoord := congrFun hfg
    (S05_Lem5_13_twoBoxExtensionTableau lam p U)
  simpa [S05_twoStepExtensionEmbedding_apply_extension] using hcoord

/-- Ordered two-box extension commutes with finite coordinate sums. -/
theorem S05_twoStepExtensionEmbedding_sum
    {n : Nat} {ι : Type} [Fintype ι]
    (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : ι -> TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    S05_twoStepExtensionEmbedding lam p (fun U => ∑ i : ι, f i U) =
      fun T => ∑ i : ι, S05_twoStepExtensionEmbedding lam p (f i) T := by
  classical
  funext T
  simp only [S05_twoStepExtensionEmbedding]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Basis-level intertwining for every adjacent pair that belongs to the child
tableau. -/
theorem S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent_basis
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (S05_twoStepExtensionEmbedding lam p (tableauBasisVec U)) =
      S05_twoStepExtensionEmbedding lam p
        (youngAdjacentOperator a (tableauBasisVec U)) := by
  let TU := S05_Lem5_13_twoBoxExtensionTableau lam p U
  rw [S05_twoStepExtensionEmbedding_basis]
  by_cases hrow : adjacentSameRow U a
  · have hrowP : adjacentSameRow TU (Fin.castSucc (Fin.castSucc a)) :=
      (S05_Lem5_13_twoBoxExtensionTableau_earlier_sameRow_iff
        lam p U a).2 hrow
    rw [youngAdjacentOperator_basis_sameRow TU _ hrowP,
      youngAdjacentOperator_basis_sameRow U a hrow,
      S05_twoStepExtensionEmbedding_basis]
  · by_cases hcol : adjacentSameCol U a
    · have hcolP : adjacentSameCol TU (Fin.castSucc (Fin.castSucc a)) :=
        (S05_Lem5_13_twoBoxExtensionTableau_earlier_sameCol_iff
          lam p U a).2 hcol
      rw [youngAdjacentOperator_basis_sameCol TU _ hcolP,
        youngAdjacentOperator_basis_sameCol U a hcol]
      have hnegP : (fun S => -tableauBasisVec TU S) =
          (-1 : Real) • tableauBasisVec TU := by
        funext S
        simp
      have hnegC : (fun S => -tableauBasisVec U S) =
          (-1 : Real) • tableauBasisVec U := by
        funext S
        simp
      rw [hnegP, hnegC]
      rw [S05_twoStepExtensionEmbedding_smul,
        S05_twoStepExtensionEmbedding_basis]
    · have hrowP : ¬ adjacentSameRow TU (Fin.castSucc (Fin.castSucc a)) := by
        intro hp
        exact hrow
          ((S05_Lem5_13_twoBoxExtensionTableau_earlier_sameRow_iff
            lam p U a).1 hp)
      have hcolP : ¬ adjacentSameCol TU (Fin.castSucc (Fin.castSucc a)) := by
        intro hp
        exact hcol
          ((S05_Lem5_13_twoBoxExtensionTableau_earlier_sameCol_iff
            lam p U a).1 hp)
      let U' := adjacentSwapTableau U a hrow hcol
      have hswap :
          S05_Lem5_13_twoBoxExtensionTableau lam p U' =
            adjacentSwapTableau TU (Fin.castSucc (Fin.castSucc a))
              hrowP hcolP := by
        simpa [TU, U'] using
          S05_Lem5_13_twoBoxExtensionTableau_earlier_swap
            lam p U a hrow hcol
      rw [youngAdjacentOperator_basis_swappable_eq TU _ hrowP hcolP,
        youngAdjacentOperator_basis_swappable_eq U a hrow hcol]
      have hchild :
          (fun S => youngAdjacentDiagCoeff U a * tableauBasisVec U S +
            youngAdjacentOffCoeff U a * tableauBasisVec U' S) =
          youngAdjacentDiagCoeff U a • tableauBasisVec U +
            youngAdjacentOffCoeff U a • tableauBasisVec U' := by
        rfl
      rw [hchild, S05_twoStepExtensionEmbedding_add,
        S05_twoStepExtensionEmbedding_smul,
        S05_twoStepExtensionEmbedding_smul,
        S05_twoStepExtensionEmbedding_basis,
        S05_twoStepExtensionEmbedding_basis]
      funext S
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [S05_Lem5_13_twoBoxExtensionTableau_earlier_diagCoeff,
        S05_Lem5_13_twoBoxExtensionTableau_earlier_offCoeff,
        ← hswap]

/-- Ordered two-box extension intertwines every child adjacent operator with
the corresponding parent earlier-adjacent operator. -/
theorem S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam) (a : Fin n)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (S05_twoStepExtensionEmbedding lam p f) =
      S05_twoStepExtensionEmbedding lam p (youngAdjacentOperator a f) := by
  classical
  have hf := tableauBasis_expansion f
  calc
    youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (S05_twoStepExtensionEmbedding lam p f) =
      youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (S05_twoStepExtensionEmbedding lam p
          (fun S =>
            ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
              f U * tableauBasisVec U S)) := by
        exact congrArg
          (fun g => youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
            (S05_twoStepExtensionEmbedding lam p g)) hf
    _ = youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (fun T =>
          ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            S05_twoStepExtensionEmbedding lam p
              (fun S => f U * tableauBasisVec U S) T) := by
        rw [S05_twoStepExtensionEmbedding_sum]
    _ = fun T =>
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
            (S05_twoStepExtensionEmbedding lam p
              (fun S => f U * tableauBasisVec U S)) T := by
        rw [youngAdjacentOperator_sum]
    _ = fun T =>
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          S05_twoStepExtensionEmbedding lam p
            (youngAdjacentOperator a
              (fun S => f U * tableauBasisVec U S)) T := by
        funext T
        apply Finset.sum_congr rfl
        intro U _hU
        have hscaled :
            youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
                (S05_twoStepExtensionEmbedding lam p
                  (fun S => f U * tableauBasisVec U S)) =
              S05_twoStepExtensionEmbedding lam p
                (youngAdjacentOperator a
                  (fun S => f U * tableauBasisVec U S)) := by
          have hembed :
              S05_twoStepExtensionEmbedding lam p
                  (fun S => f U * tableauBasisVec U S) =
                fun T => f U *
                  S05_twoStepExtensionEmbedding lam p (tableauBasisVec U) T := by
            funext T
            simp only [S05_twoStepExtensionEmbedding]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro V _hV
            ring
          have hembedOp :
              S05_twoStepExtensionEmbedding lam p
                  (fun S => f U *
                    youngAdjacentOperator a (tableauBasisVec U) S) =
                fun T => f U * S05_twoStepExtensionEmbedding lam p
                  (youngAdjacentOperator a (tableauBasisVec U)) T := by
            funext T
            simp only [S05_twoStepExtensionEmbedding]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro V _hV
            ring
          have hparentSmul := youngAdjacentOperator_smul
            (Fin.castSucc (Fin.castSucc a)) (f U)
            (S05_twoStepExtensionEmbedding lam p (tableauBasisVec U))
          have hchildSmul := youngAdjacentOperator_smul a (f U)
            (tableauBasisVec U)
          calc
            youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
                (S05_twoStepExtensionEmbedding lam p
                  (fun S => f U * tableauBasisVec U S)) =
              youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
                (fun T => f U * S05_twoStepExtensionEmbedding lam p
                  (tableauBasisVec U) T) := congrArg _ hembed
            _ = fun T => f U *
                youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
                  (S05_twoStepExtensionEmbedding lam p (tableauBasisVec U)) T :=
              hparentSmul
            _ = fun T => f U * S05_twoStepExtensionEmbedding lam p
                (youngAdjacentOperator a (tableauBasisVec U)) T := by
              rw [S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent_basis]
            _ = S05_twoStepExtensionEmbedding lam p
                (fun S => f U *
                  youngAdjacentOperator a (tableauBasisVec U) S) := hembedOp.symm
            _ = S05_twoStepExtensionEmbedding lam p
                (youngAdjacentOperator a
                  (fun S => f U * tableauBasisVec U S)) := by
              exact congrArg (S05_twoStepExtensionEmbedding lam p)
                hchildSmul.symm
        exact congrFun hscaled T
    _ = S05_twoStepExtensionEmbedding lam p
        (fun S =>
          ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            youngAdjacentOperator a
              (fun R => f U * tableauBasisVec U R) S) := by
        rw [S05_twoStepExtensionEmbedding_sum]
    _ = S05_twoStepExtensionEmbedding lam p
        (youngAdjacentOperator a
          (fun S =>
            ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
              f U * tableauBasisVec U S)) := by
        rw [youngAdjacentOperator_sum]
    _ = S05_twoStepExtensionEmbedding lam p
        (youngAdjacentOperator a f) := by
      exact congrArg (S05_twoStepExtensionEmbedding lam p)
        (congrArg (youngAdjacentOperator a) hf).symm

/-- Applying any parent adjacent operator to the raw extension embedding can be
expanded term-by-term over the child tableau basis. -/
theorem S05_twoStepExtensionEmbedding_operator_expansion
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) (a : Fin (n + 1))
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOperator a (S05_twoStepExtensionEmbedding lam p f) =
      fun T =>
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * youngAdjacentOperator a
            (tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T := by
  classical
  change youngAdjacentOperator a
      (fun T =>
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * tableauBasisVec
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) = _
  rw [youngAdjacentOperator_sum]
  funext T
  apply Finset.sum_congr rfl
  intro U _hU
  rw [youngAdjacentOperator_smul]

/-- The final diagonal coefficient of every extension in a fixed two-box fiber
is the corner-defined coefficient above. -/
theorem S05_twoBoxExtension_final_diagCoeff
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentDiagCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n) =
      S05_twoBoxFinalDiagCoeff lam p := by
  unfold youngAdjacentDiagCoeff adjacentAxialDistance entryContent
  change
    (((YoungCell.content
        (adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) -
      YoungCell.content
        (adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) : Int) : Real)⁻¹ =
      S05_twoBoxFinalDiagCoeff lam p)
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_hiCell,
    S05_Lem5_13_twoBoxExtensionTableau_final_loCell]
  rfl

/-- The normalized positive vector has final-edge eigenvalue `+1`. -/
theorem S05_normalizedAdjacentPlusVector_eigen
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (S05_normalizedAdjacentPlusVector T a hrow hcol) =
      S05_normalizedAdjacentPlusVector T a hrow hcol := by
  dsimp [S05_normalizedAdjacentPlusVector]
  rw [youngAdjacentOperator_smul, youngAdjacentOperator_add,
    youngAdjacentOperator_sq_basis]
  funext S
  ring

/-- The normalized negative vector has final-edge eigenvalue `-1`. -/
theorem S05_normalizedAdjacentMinusVector_eigen
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (S05_normalizedAdjacentMinusVector T a hrow hcol) =
      (-1 : Real) • S05_normalizedAdjacentMinusVector T a hrow hcol := by
  dsimp [S05_normalizedAdjacentMinusVector]
  have hsub :
      youngAdjacentOperator a
          (fun S => tableauBasisVec T S -
            youngAdjacentOperator a (tableauBasisVec T) S) =
        fun S => youngAdjacentOperator a (tableauBasisVec T) S -
          tableauBasisVec T S := by
    change youngAdjacentOperator a
        (fun S => tableauBasisVec T S +
          -(youngAdjacentOperator a (tableauBasisVec T) S)) = _
    rw [youngAdjacentOperator_add, youngAdjacentOperator_neg,
      youngAdjacentOperator_sq_basis]
    funext S
    ring
  rw [youngAdjacentOperator_smul, hsub]
  funext S
  simp [Pi.smul_apply]
  ring

/-- In the disconnected positive case, the signed extension vector is the
normalized `+1` spectral projection of the raw extension basis vector. -/
theorem S05_signedTwoBoxExtensionBasisVector_eq_plusProjection
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (hpos : p.first.1 <= p.second.1)
    (hrow : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)) :
    S05_signedTwoBoxExtensionBasisVector lam p U =
      fun T =>
        (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T +
            youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T) := by
  rw [S05_signedTwoBoxExtensionBasisVector]
  dsimp only
  rw [dif_pos hpos, dif_neg hrow]
  rw [S05_normalizedAdjacentPlusVector]
  rw [S05_twoBoxExtension_final_diagCoeff]

/-- In the disconnected negative case, the signed extension vector is the
normalized `-1` spectral projection of the raw extension basis vector. -/
theorem S05_signedTwoBoxExtensionBasisVector_eq_minusProjection
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (hneg : ¬ p.first.1 <= p.second.1)
    (hcol : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)) :
    S05_signedTwoBoxExtensionBasisVector lam p U =
      fun T =>
        (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T -
            youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T) := by
  have hrow := S05_twoBoxExtension_not_sameRow_of_negative lam p hneg U
  rw [S05_signedTwoBoxExtensionBasisVector]
  dsimp only
  rw [dif_neg hneg, dif_neg hcol]
  rw [S05_normalizedAdjacentMinusVector]
  rw [S05_twoBoxExtension_final_diagCoeff]

/-- Every signed child basis vector has the required eigenvalue under the final
adjacent operator. -/
theorem S05_signedTwoBoxExtensionBasisVector_finalOperator
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOperator (Fin.last n)
        (S05_signedTwoBoxExtensionBasisVector lam p U) =
      S05_signedTwoBoxRemovalSign p •
        S05_signedTwoBoxExtensionBasisVector lam p U := by
  by_cases hpos : p.first.1 <= p.second.1
  · by_cases hrow : adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_pos hpos, dif_pos hrow]
      rw [youngAdjacentOperator_basis_sameRow
        (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) hrow]
      simp [S05_signedTwoBoxRemovalSign, hpos]
    · have hcol := S05_twoBoxExtension_not_sameCol_of_positive lam p hpos U
      rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_pos hpos, dif_neg hrow]
      rw [S05_normalizedAdjacentPlusVector_eigen
        (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) hrow hcol]
      simp [S05_signedTwoBoxRemovalSign, hpos]
  · have hrow := S05_twoBoxExtension_not_sameRow_of_negative lam p hpos U
    by_cases hcol : adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_neg hpos, dif_pos hcol]
      rw [youngAdjacentOperator_basis_sameCol
        (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) hcol]
      simp [S05_signedTwoBoxRemovalSign, hpos]
      funext S
      rfl
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_neg hpos, dif_neg hcol]
      rw [S05_normalizedAdjacentMinusVector_eigen
        (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) hrow hcol]
      simp [S05_signedTwoBoxRemovalSign, hpos]
/-- The squared norm of a two-basis-vector combination with disjoint support. -/
theorem S05_tableauInner_twoBasis_self {n : Nat} {lam : YoungDiagram n}
    {T U : StandardYoungTableau lam} (hTU : T ≠ U) (x y : Real) :
    tableauInner
        (fun S => x * tableauBasisVec T S + y * tableauBasisVec U S)
        (fun S => x * tableauBasisVec T S + y * tableauBasisVec U S) =
      x ^ 2 + y ^ 2 := by
  rw [S05_tableauInner_add_left, S05_tableauInner_add_right,
    S05_tableauInner_add_right]
  simp only [S05_tableauInner_mul_left, S05_tableauInner_mul_right,
    tableauInner_basis_basis_self,
    tableauInner_basis_basis_ne hTU,
    tableauInner_basis_basis_ne (Ne.symm hTU)]
  ring

/-- Linear combinations supported on two disjoint pairs of tableau basis
vectors are orthogonal. -/
theorem S05_tableauInner_twoBasis_twoBasis_of_disjoint
    {n : Nat} {lam : YoungDiagram n}
    {T T' U U' : StandardYoungTableau lam}
    (hTU : T ≠ U) (hTU' : T ≠ U')
    (hT'U : T' ≠ U) (hT'U' : T' ≠ U')
    (x y z w : Real) :
    tableauInner
        (fun S => x * tableauBasisVec T S + y * tableauBasisVec T' S)
        (fun S => z * tableauBasisVec U S + w * tableauBasisVec U' S) =
      0 := by
  rw [S05_tableauInner_add_left, S05_tableauInner_add_right,
    S05_tableauInner_add_right]
  simp only [S05_tableauInner_mul_left, S05_tableauInner_mul_right,
    tableauInner_basis_basis_ne hTU,
    tableauInner_basis_basis_ne hTU',
    tableauInner_basis_basis_ne hT'U,
    tableauInner_basis_basis_ne hT'U']
  ring

/-- The explicit positive eigenvector is normalized. -/
theorem S05_normalizedAdjacentPlusVector_inner_self
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    tableauInner (S05_normalizedAdjacentPlusVector T a hrow hcol)
      (S05_normalizedAdjacentPlusVector T a hrow hcol) = 1 := by
  let d := youngAdjacentDiagCoeff T a
  let b := youngAdjacentOffCoeff T a
  let T' := adjacentSwapTableau T a
    (by simpa [adjacentSameRow] using hrow)
    (by simpa [adjacentSameCol] using hcol)
  let q := 2 * (1 + d)
  let c := (Real.sqrt q)⁻¹
  have hT' : T ≠ T' := by
    exact Ne.symm (by
      simpa [T'] using adjacentSwapTableau_ne_self T a hrow hcol)
  have hcoeff : d ^ 2 + b ^ 2 = 1 := by
    simpa [d, b] using youngAdjacentCoeff_sq_sum_of_swappable T a hrow hcol
  have hdabs : |d| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]
    simpa [d] using youngAdjacentDiagCoeff_sq_lt_one_of_swappable T a hrow hcol
  have hqpos : 0 < q := by
    have hdgt : -1 < d := (abs_lt.mp hdabs).1
    simp [q]
    linarith
  have hsqrt : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hqpos)
  have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hqpos)
  have hvec :
      S05_normalizedAdjacentPlusVector T a hrow hcol =
        fun S => (c * (1 + d)) * tableauBasisVec T S +
          (c * b) * tableauBasisVec T' S := by
    funext S
    rw [S05_normalizedAdjacentPlusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
    simp [c, q, d, b, T']
    ring
  rw [hvec, S05_tableauInner_twoBasis_self hT']
  have hnorm : (1 + d) ^ 2 + b ^ 2 = q := by
    simp [q]
    nlinarith
  dsimp [c]
  field_simp [hsqrt_ne]
  nlinarith

/-- The explicit negative eigenvector is normalized. -/
theorem S05_normalizedAdjacentMinusVector_inner_self
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    tableauInner (S05_normalizedAdjacentMinusVector T a hrow hcol)
      (S05_normalizedAdjacentMinusVector T a hrow hcol) = 1 := by
  let d := youngAdjacentDiagCoeff T a
  let b := youngAdjacentOffCoeff T a
  let T' := adjacentSwapTableau T a
    (by simpa [adjacentSameRow] using hrow)
    (by simpa [adjacentSameCol] using hcol)
  let q := 2 * (1 - d)
  let c := (Real.sqrt q)⁻¹
  have hT' : T ≠ T' := by
    exact Ne.symm (by
      simpa [T'] using adjacentSwapTableau_ne_self T a hrow hcol)
  have hcoeff : d ^ 2 + b ^ 2 = 1 := by
    simpa [d, b] using youngAdjacentCoeff_sq_sum_of_swappable T a hrow hcol
  have hdabs : |d| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]
    simpa [d] using youngAdjacentDiagCoeff_sq_lt_one_of_swappable T a hrow hcol
  have hqpos : 0 < q := by
    have hdlt : d < 1 := (abs_lt.mp hdabs).2
    simp [q]
    linarith
  have hsqrt : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hqpos)
  have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hqpos)
  have hvec :
      S05_normalizedAdjacentMinusVector T a hrow hcol =
        fun S => (c * (1 - d)) * tableauBasisVec T S +
          (-(c * b)) * tableauBasisVec T' S := by
    funext S
    rw [S05_normalizedAdjacentMinusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
    simp [c, q, d, b, T']
    ring
  rw [hvec, S05_tableauInner_twoBasis_self hT']
  have hnorm : (1 - d) ^ 2 + b ^ 2 = q := by
    simp [q]
    nlinarith
  dsimp [c]
  field_simp [hsqrt_ne]
  nlinarith

/-- Every signed child basis image has norm one. -/
theorem S05_signedTwoBoxExtensionBasisVector_inner_self
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
      (S05_signedTwoBoxExtensionBasisVector lam p U) = 1 := by
  by_cases hpos : p.first.1 <= p.second.1
  · by_cases hrow : adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_pos hpos, dif_pos hrow]
      exact tableauInner_basis_basis_self _
    · have hcol := S05_twoBoxExtension_not_sameCol_of_positive lam p hpos U
      rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_pos hpos, dif_neg hrow]
      exact S05_normalizedAdjacentPlusVector_inner_self _ _ hrow hcol
  · have hrow := S05_twoBoxExtension_not_sameRow_of_negative lam p hpos U
    by_cases hcol : adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_neg hpos, dif_pos hcol]
      exact tableauInner_basis_basis_self _
    · rw [S05_signedTwoBoxExtensionBasisVector]
      dsimp only
      rw [dif_neg hpos, dif_neg hcol]
      exact S05_normalizedAdjacentMinusVector_inner_self _ _ hrow hcol

/-- A standard tableau is determined by the cell containing each entry. -/
theorem S05_standardYoungTableau_ext_cellOfEntry
    {n : Nat} {lam : YoungDiagram n}
    {T U : StandardYoungTableau lam}
    (hcell : ∀ a : Fin n, cellOfEntry T a = cellOfEntry U a) :
    T = U := by
  apply standardYoungTableau_ext_entry
  intro u
  let a := T.entry u
  have hTu : cellOfEntry T a = u := cellOfEntry_eq_of_entry T rfl
  have hUu : cellOfEntry U a = u := by
    rw [← hTu]
    exact (hcell a).symm
  have hentry := entry_cellOfEntry U a
  rw [hUu] at hentry
  exact hentry.symm

theorem S05_castCastSucc_ne_final_lo {n : Nat} (a : Fin n) :
    Fin.castSucc (Fin.castSucc a) ≠ adjacentEntryLo (Fin.last n) := by
  intro h
  have hv := congrArg Fin.val h
  simp [adjacentEntryLo] at hv
  omega

theorem S05_castCastSucc_ne_final_hi {n : Nat} (a : Fin n) :
    Fin.castSucc (Fin.castSucc a) ≠ adjacentEntryHi (Fin.last n) := by
  intro h
  have hv := congrArg Fin.val h
  simp [adjacentEntryHi] at hv
  omega

/-- Swapping the final labels in the extension of `U` cannot produce the raw
extension of a distinct child tableau `V`. -/
theorem S05_twoBoxExtension_finalSwap_ne_extension_of_ne
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    {U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)}
    (hUV : U ≠ V)
    (hrow : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcol : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)) :
    adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrow)
        (by simpa [adjacentSameCol] using hcol) ≠
      S05_Lem5_13_twoBoxExtensionTableau lam p V := by
  intro hswapEq
  apply hUV
  apply S05_standardYoungTableau_ext_cellOfEntry
  intro a
  apply YoungCell.ext_row_col
  · rw [S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_row,
      S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_row]
    have hfix := S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
      (by simpa [adjacentSameRow] using hrow)
      (by simpa [adjacentSameCol] using hcol)
      (S05_castCastSucc_ne_final_lo a)
      (S05_castCastSucc_ne_final_hi a)
    rw [hswapEq] at hfix
    exact congrArg YoungCell.row hfix.symm
  · rw [S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_col,
      S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_col]
    have hfix := S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
      (by simpa [adjacentSameRow] using hrow)
      (by simpa [adjacentSameCol] using hcol)
      (S05_castCastSucc_ne_final_lo a)
      (S05_castCastSucc_ne_final_hi a)
    rw [hswapEq] at hfix
    exact congrArg YoungCell.col hfix.symm

/-- Final swaps of extensions of distinct child tableaux remain distinct. -/
theorem S05_twoBoxExtension_finalSwap_ne_finalSwap_of_ne
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    {U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)}
    (hUV : U ≠ V)
    (hrowU : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcolU : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hrowV : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p V) (Fin.last n))
    (hcolV : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p V) (Fin.last n)) :
    adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowU)
        (by simpa [adjacentSameCol] using hcolU) ≠
      adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p V)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowV)
        (by simpa [adjacentSameCol] using hcolV) := by
  intro hswapEq
  apply hUV
  apply S05_standardYoungTableau_ext_cellOfEntry
  intro a
  have hfixU := S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi
    (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)
    (by simpa [adjacentSameRow] using hrowU)
    (by simpa [adjacentSameCol] using hcolU)
    (S05_castCastSucc_ne_final_lo a)
    (S05_castCastSucc_ne_final_hi a)
  have hfixV := S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi
    (S05_Lem5_13_twoBoxExtensionTableau lam p V) (Fin.last n)
    (by simpa [adjacentSameRow] using hrowV)
    (by simpa [adjacentSameCol] using hcolV)
    (S05_castCastSucc_ne_final_lo a)
    (S05_castCastSucc_ne_final_hi a)
  have hparent :
      cellOfEntry (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.castSucc (Fin.castSucc a)) =
        cellOfEntry (S05_Lem5_13_twoBoxExtensionTableau lam p V)
          (Fin.castSucc (Fin.castSucc a)) := by
    calc
      _ = cellOfEntry
          (adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
            (Fin.last n) _ _)
          (Fin.castSucc (Fin.castSucc a)) := hfixU.symm
      _ = cellOfEntry
          (adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p V)
            (Fin.last n) _ _)
          (Fin.castSucc (Fin.castSucc a)) := by rw [hswapEq]
      _ = _ := hfixV
  apply YoungCell.ext_row_col
  · rw [S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_row,
      S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_row]
    exact congrArg YoungCell.row hparent
  · rw [S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_col,
      S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_col]
    exact congrArg YoungCell.col hparent

/-- Raw extensions associated to distinct ordered two-step removals are
distinct parent tableaux. -/
theorem S05_twoBoxExtension_ne_of_removal_ne
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam} (hpq : p ≠ q)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q)) :
    S05_Lem5_13_twoBoxExtensionTableau lam p U ≠
      S05_Lem5_13_twoBoxExtensionTableau lam q V := by
  intro hExt
  apply hpq
  apply twoStepRemovableRows_ext
  · have hhi := congrArg
      (fun T => YoungCell.row (adjacentHiCell T (Fin.last n))) hExt
    rw [S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row] at hhi
    exact hhi
  · have hlo := congrArg
      (fun T => YoungCell.row (adjacentLoCell T (Fin.last n))) hExt
    rw [S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row] at hlo
    exact hlo

/-- If a final-swapped extension from `p` equals a raw extension from `q`, the
two ordered deletion-row pairs are reverses of one another. -/
theorem S05_twoBoxExtension_finalSwap_rows_of_eq_extension
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam}
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q))
    (hrowP : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcolP : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hEq :
      adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) =
        S05_Lem5_13_twoBoxExtensionTableau lam q V) :
    p.second.1 = q.first.1 ∧ p.first.1 = q.second.1 := by
  constructor
  · have hhi := congrArg
      (fun T => YoungCell.row (adjacentHiCell T (Fin.last n))) hEq
    change YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) _ _)
          (adjacentEntryHi (Fin.last n))) = _ at hhi
    rw [S05_Lem5_01_adjacentSwapTableau_cell_hi,
      S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row] at hhi
    exact hhi
  · have hlo := congrArg
      (fun T => YoungCell.row (adjacentLoCell T (Fin.last n))) hEq
    change YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) _ _)
          (adjacentEntryLo (Fin.last n))) = _ at hlo
    rw [S05_Lem5_01_adjacentSwapTableau_cell_lo,
      S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row] at hlo
    exact hlo

/-- A final-swapped positive extension cannot equal a raw extension from a
positive removal. -/
theorem S05_twoBoxExtension_finalSwap_ne_extension_of_positive
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam}
    (hposP : p.first.1 <= p.second.1)
    (hposQ : q.first.1 <= q.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q))
    (hrowP : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcolP : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)) :
    adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowP)
        (by simpa [adjacentSameCol] using hcolP) ≠
      S05_Lem5_13_twoBoxExtensionTableau lam q V := by
  intro hEq
  rcases S05_twoBoxExtension_finalSwap_rows_of_eq_extension
    lam U V hrowP hcolP hEq with ⟨hfirst, hsecond⟩
  have hne : p.second.1 ≠ p.first.1 := by
    intro h
    exact hrowP
      ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
        lam p U).2 h)
  omega

/-- A final-swapped negative extension cannot equal a raw extension from a
negative removal. -/
theorem S05_twoBoxExtension_finalSwap_ne_extension_of_negative
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam}
    (hnegP : ¬ p.first.1 <= p.second.1)
    (hnegQ : ¬ q.first.1 <= q.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q))
    (hrowP : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcolP : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n)) :
    adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowP)
        (by simpa [adjacentSameCol] using hcolP) ≠
      S05_Lem5_13_twoBoxExtensionTableau lam q V := by
  intro hEq
  rcases S05_twoBoxExtension_finalSwap_rows_of_eq_extension
    lam U V hrowP hcolP hEq with ⟨hfirst, hsecond⟩
  omega

/-- Final swaps belonging to distinct ordered removals remain distinct. -/
theorem S05_twoBoxExtension_finalSwap_ne_finalSwap_of_removal_ne
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam} (hpq : p ≠ q)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q))
    (hrowP : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hcolP : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n))
    (hrowQ : ¬ adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam q V) (Fin.last n))
    (hcolQ : ¬ adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam q V) (Fin.last n)) :
    adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowP)
        (by simpa [adjacentSameCol] using hcolP) ≠
      adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam q V)
        (Fin.last n)
        (by simpa [adjacentSameRow] using hrowQ)
        (by simpa [adjacentSameCol] using hcolQ) := by
  intro hEq
  apply hpq
  apply twoStepRemovableRows_ext
  · have hlo := congrArg
      (fun T => YoungCell.row (adjacentLoCell T (Fin.last n))) hEq
    change YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) _ _)
          (adjacentEntryLo (Fin.last n))) =
      YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam q V) (Fin.last n) _ _)
          (adjacentEntryLo (Fin.last n))) at hlo
    rw [S05_Lem5_01_adjacentSwapTableau_cell_lo,
      S05_Lem5_01_adjacentSwapTableau_cell_lo,
      S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row] at hlo
    exact hlo
  · have hhi := congrArg
      (fun T => YoungCell.row (adjacentHiCell T (Fin.last n))) hEq
    change YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) _ _)
          (adjacentEntryHi (Fin.last n))) =
      YoungCell.row
        (cellOfEntry
          (adjacentSwapTableau
            (S05_Lem5_13_twoBoxExtensionTableau lam q V) (Fin.last n) _ _)
          (adjacentEntryHi (Fin.last n))) at hhi
    rw [S05_Lem5_01_adjacentSwapTableau_cell_hi,
      S05_Lem5_01_adjacentSwapTableau_cell_hi,
      S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row,
      S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row] at hhi
    exact hhi

/-- Positive final-edge eigenvectors over disjoint extension fibers are
orthogonal. -/
theorem S05_normalizedAdjacentPlusVector_inner_of_disjoint
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T U : StandardYoungTableau lam) (a : Fin n)
    (hrowT : ¬ adjacentSameRow T a) (hcolT : ¬ adjacentSameCol T a)
    (hrowU : ¬ adjacentSameRow U a) (hcolU : ¬ adjacentSameCol U a)
    (hTU : T ≠ U)
    (hTU' : T ≠ adjacentSwapTableau U a
      (by simpa [adjacentSameRow] using hrowU)
      (by simpa [adjacentSameCol] using hcolU))
    (hT'U : adjacentSwapTableau T a
      (by simpa [adjacentSameRow] using hrowT)
      (by simpa [adjacentSameCol] using hcolT) ≠ U)
    (hT'U' : adjacentSwapTableau T a
      (by simpa [adjacentSameRow] using hrowT)
      (by simpa [adjacentSameCol] using hcolT) ≠
        adjacentSwapTableau U a
          (by simpa [adjacentSameRow] using hrowU)
          (by simpa [adjacentSameCol] using hcolU)) :
    tableauInner (S05_normalizedAdjacentPlusVector T a hrowT hcolT)
      (S05_normalizedAdjacentPlusVector U a hrowU hcolU) = 0 := by
  let T' := adjacentSwapTableau T a
    (by simpa [adjacentSameRow] using hrowT)
    (by simpa [adjacentSameCol] using hcolT)
  let U' := adjacentSwapTableau U a
    (by simpa [adjacentSameRow] using hrowU)
    (by simpa [adjacentSameCol] using hcolU)
  let dT := youngAdjacentDiagCoeff T a
  let bT := youngAdjacentOffCoeff T a
  let cT := (Real.sqrt (2 * (1 + dT)))⁻¹
  let dU := youngAdjacentDiagCoeff U a
  let bU := youngAdjacentOffCoeff U a
  let cU := (Real.sqrt (2 * (1 + dU)))⁻¹
  have hvecT :
      S05_normalizedAdjacentPlusVector T a hrowT hcolT =
        fun S => (cT * (1 + dT)) * tableauBasisVec T S +
          (cT * bT) * tableauBasisVec T' S := by
    funext S
    rw [S05_normalizedAdjacentPlusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq T a hrowT hcolT]
    simp [T', dT, bT, cT]
    ring
  have hvecU :
      S05_normalizedAdjacentPlusVector U a hrowU hcolU =
        fun S => (cU * (1 + dU)) * tableauBasisVec U S +
          (cU * bU) * tableauBasisVec U' S := by
    funext S
    rw [S05_normalizedAdjacentPlusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq U a hrowU hcolU]
    simp [U', dU, bU, cU]
    ring
  rw [hvecT, hvecU]
  exact S05_tableauInner_twoBasis_twoBasis_of_disjoint
    hTU (by simpa [U'] using hTU') (by simpa [T'] using hT'U)
      (by simpa [T', U'] using hT'U') _ _ _ _

/-- Negative final-edge eigenvectors over disjoint extension fibers are
orthogonal. -/
theorem S05_normalizedAdjacentMinusVector_inner_of_disjoint
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T U : StandardYoungTableau lam) (a : Fin n)
    (hrowT : ¬ adjacentSameRow T a) (hcolT : ¬ adjacentSameCol T a)
    (hrowU : ¬ adjacentSameRow U a) (hcolU : ¬ adjacentSameCol U a)
    (hTU : T ≠ U)
    (hTU' : T ≠ adjacentSwapTableau U a
      (by simpa [adjacentSameRow] using hrowU)
      (by simpa [adjacentSameCol] using hcolU))
    (hT'U : adjacentSwapTableau T a
      (by simpa [adjacentSameRow] using hrowT)
      (by simpa [adjacentSameCol] using hcolT) ≠ U)
    (hT'U' : adjacentSwapTableau T a
      (by simpa [adjacentSameRow] using hrowT)
      (by simpa [adjacentSameCol] using hcolT) ≠
        adjacentSwapTableau U a
          (by simpa [adjacentSameRow] using hrowU)
          (by simpa [adjacentSameCol] using hcolU)) :
    tableauInner (S05_normalizedAdjacentMinusVector T a hrowT hcolT)
      (S05_normalizedAdjacentMinusVector U a hrowU hcolU) = 0 := by
  let T' := adjacentSwapTableau T a
    (by simpa [adjacentSameRow] using hrowT)
    (by simpa [adjacentSameCol] using hcolT)
  let U' := adjacentSwapTableau U a
    (by simpa [adjacentSameRow] using hrowU)
    (by simpa [adjacentSameCol] using hcolU)
  let dT := youngAdjacentDiagCoeff T a
  let bT := youngAdjacentOffCoeff T a
  let cT := (Real.sqrt (2 * (1 - dT)))⁻¹
  let dU := youngAdjacentDiagCoeff U a
  let bU := youngAdjacentOffCoeff U a
  let cU := (Real.sqrt (2 * (1 - dU)))⁻¹
  have hvecT :
      S05_normalizedAdjacentMinusVector T a hrowT hcolT =
        fun S => (cT * (1 - dT)) * tableauBasisVec T S +
          (-(cT * bT)) * tableauBasisVec T' S := by
    funext S
    rw [S05_normalizedAdjacentMinusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq T a hrowT hcolT]
    simp [T', dT, bT, cT]
    ring
  have hvecU :
      S05_normalizedAdjacentMinusVector U a hrowU hcolU =
        fun S => (cU * (1 - dU)) * tableauBasisVec U S +
          (-(cU * bU)) * tableauBasisVec U' S := by
    funext S
    rw [S05_normalizedAdjacentMinusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq U a hrowU hcolU]
    simp [U', dU, bU, cU]
    ring
  rw [hvecT, hvecU]
  exact S05_tableauInner_twoBasis_twoBasis_of_disjoint
    hTU (by simpa [U'] using hTU') (by simpa [T'] using hT'U)
      (by simpa [T', U'] using hT'U') _ _ _ _

/-- A tableau basis vector is orthogonal to a positive projected vector whose
two-point support avoids it. -/
theorem S05_tableauInner_basis_normalizedPlus_of_disjoint
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T U : StandardYoungTableau lam) (a : Fin n)
    (hrowU : ¬ adjacentSameRow U a) (hcolU : ¬ adjacentSameCol U a)
    (hTU : T ≠ U)
    (hTU' : T ≠ adjacentSwapTableau U a
      (by simpa [adjacentSameRow] using hrowU)
      (by simpa [adjacentSameCol] using hcolU)) :
    tableauInner (tableauBasisVec T)
      (S05_normalizedAdjacentPlusVector U a hrowU hcolU) = 0 := by
  let U' := adjacentSwapTableau U a
    (by simpa [adjacentSameRow] using hrowU)
    (by simpa [adjacentSameCol] using hcolU)
  let d := youngAdjacentDiagCoeff U a
  let b := youngAdjacentOffCoeff U a
  let c := (Real.sqrt (2 * (1 + d)))⁻¹
  have hbasis : tableauBasisVec T =
      fun S => 1 * tableauBasisVec T S + 0 * tableauBasisVec T S := by
    funext S
    ring
  have hvec : S05_normalizedAdjacentPlusVector U a hrowU hcolU =
      fun S => (c * (1 + d)) * tableauBasisVec U S +
        (c * b) * tableauBasisVec U' S := by
    funext S
    rw [S05_normalizedAdjacentPlusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq U a hrowU hcolU]
    simp [U', d, b, c]
    ring
  rw [hbasis, hvec]
  exact S05_tableauInner_twoBasis_twoBasis_of_disjoint
    hTU (by simpa [U'] using hTU') hTU (by simpa [U'] using hTU')
      _ _ _ _

/-- A tableau basis vector is orthogonal to a negative projected vector whose
two-point support avoids it. -/
theorem S05_tableauInner_basis_normalizedMinus_of_disjoint
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T U : StandardYoungTableau lam) (a : Fin n)
    (hrowU : ¬ adjacentSameRow U a) (hcolU : ¬ adjacentSameCol U a)
    (hTU : T ≠ U)
    (hTU' : T ≠ adjacentSwapTableau U a
      (by simpa [adjacentSameRow] using hrowU)
      (by simpa [adjacentSameCol] using hcolU)) :
    tableauInner (tableauBasisVec T)
      (S05_normalizedAdjacentMinusVector U a hrowU hcolU) = 0 := by
  let U' := adjacentSwapTableau U a
    (by simpa [adjacentSameRow] using hrowU)
    (by simpa [adjacentSameCol] using hcolU)
  let d := youngAdjacentDiagCoeff U a
  let b := youngAdjacentOffCoeff U a
  let c := (Real.sqrt (2 * (1 - d)))⁻¹
  have hbasis : tableauBasisVec T =
      fun S => 1 * tableauBasisVec T S + 0 * tableauBasisVec T S := by
    funext S
    ring
  have hvec : S05_normalizedAdjacentMinusVector U a hrowU hcolU =
      fun S => (c * (1 - d)) * tableauBasisVec U S +
        (-(c * b)) * tableauBasisVec U' S := by
    funext S
    rw [S05_normalizedAdjacentMinusVector]
    dsimp only
    rw [youngAdjacentOperator_basis_swappable_eq U a hrowU hcolU]
    simp [U', d, b, c]
    ring
  rw [hbasis, hvec]
  exact S05_tableauInner_twoBasis_twoBasis_of_disjoint
    hTU (by simpa [U'] using hTU') hTU (by simpa [U'] using hTU')
      _ _ _ _

/-- Basis vectors belonging to distinct positive signed two-box children are
orthogonal. -/
theorem S05_signedTwoBoxExtensionBasisVector_inner_of_distinct_positive
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam} (hpq : p ≠ q)
    (hposP : p.first.1 <= p.second.1)
    (hposQ : q.first.1 <= q.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q)) :
    tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
      (S05_signedTwoBoxExtensionBasisVector lam q V) = 0 := by
  let TP := S05_Lem5_13_twoBoxExtensionTableau lam p U
  let TQ := S05_Lem5_13_twoBoxExtensionTableau lam q V
  have hTP_TQ : TP ≠ TQ := by
    simpa [TP, TQ] using S05_twoBoxExtension_ne_of_removal_ne
      lam hpq U V
  by_cases hrowsP : p.second.1 = p.first.1
  · have hrowP : adjacentSameRow TP (Fin.last n) := by
      exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
        lam p U).2 hrowsP
    by_cases hrowsQ : q.second.1 = q.first.1
    · have hrowQ : adjacentSameRow TQ (Fin.last n) := by
        exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
          lam q V).2 hrowsQ
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_pos hposP, dif_pos (by simpa [TP] using hrowP),
        dif_pos hposQ, dif_pos (by simpa [TQ] using hrowQ)]
      exact tableauInner_basis_basis_ne hTP_TQ
    · have hrowQ : ¬ adjacentSameRow TQ (Fin.last n) := by
        intro h
        exact hrowsQ
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
            lam q V).1 h)
      have hcolQ : ¬ adjacentSameCol TQ (Fin.last n) := by
        simpa [TQ] using
          S05_twoBoxExtension_not_sameCol_of_positive lam q hposQ V
      have hTP_swapQ : TP ≠ adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_positive
              lam hposQ hposP V U hrowQ hcolQ)
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_pos hposP, dif_pos (by simpa [TP] using hrowP),
        dif_pos hposQ, dif_neg (by simpa [TQ] using hrowQ)]
      exact S05_tableauInner_basis_normalizedPlus_of_disjoint
        TP TQ (Fin.last n) hrowQ hcolQ hTP_TQ hTP_swapQ
  · have hrowP : ¬ adjacentSameRow TP (Fin.last n) := by
      intro h
      exact hrowsP
        ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
          lam p U).1 h)
    have hcolP : ¬ adjacentSameCol TP (Fin.last n) := by
      simpa [TP] using
        S05_twoBoxExtension_not_sameCol_of_positive lam p hposP U
    by_cases hrowsQ : q.second.1 = q.first.1
    · have hrowQ : adjacentSameRow TQ (Fin.last n) := by
        exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
          lam q V).2 hrowsQ
      have hTQ_swapP : TQ ≠ adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_positive
              lam hposP hposQ U V hrowP hcolP)
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_pos hposP, dif_neg (by simpa [TP] using hrowP),
        dif_pos hposQ, dif_pos (by simpa [TQ] using hrowQ)]
      rw [S05_tableauInner_symm]
      exact S05_tableauInner_basis_normalizedPlus_of_disjoint
        TQ TP (Fin.last n) hrowP hcolP (Ne.symm hTP_TQ) hTQ_swapP
    · have hrowQ : ¬ adjacentSameRow TQ (Fin.last n) := by
        intro h
        exact hrowsQ
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
            lam q V).1 h)
      have hcolQ : ¬ adjacentSameCol TQ (Fin.last n) := by
        simpa [TQ] using
          S05_twoBoxExtension_not_sameCol_of_positive lam q hposQ V
      have hTP_swapQ : TP ≠ adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_positive
              lam hposQ hposP V U hrowQ hcolQ)
      have hswapP_TQ : adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) ≠ TQ := by
        simpa [TP, TQ] using
          S05_twoBoxExtension_finalSwap_ne_extension_of_positive
            lam hposP hposQ U V hrowP hcolP
      have hswapP_swapQ : adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) ≠
        adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        simpa [TP, TQ] using
          S05_twoBoxExtension_finalSwap_ne_finalSwap_of_removal_ne
            lam hpq U V hrowP hcolP hrowQ hcolQ
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_pos hposP, dif_neg (by simpa [TP] using hrowP),
        dif_pos hposQ, dif_neg (by simpa [TQ] using hrowQ)]
      exact S05_normalizedAdjacentPlusVector_inner_of_disjoint
        TP TQ (Fin.last n) hrowP hcolP hrowQ hcolQ hTP_TQ
          hTP_swapQ hswapP_TQ hswapP_swapQ

/-- Basis vectors belonging to distinct negative signed two-box children are
orthogonal. -/
theorem S05_signedTwoBoxExtensionBasisVector_inner_of_distinct_negative
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam} (hpq : p ≠ q)
    (hnegP : ¬ p.first.1 <= p.second.1)
    (hnegQ : ¬ q.first.1 <= q.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q)) :
    tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
      (S05_signedTwoBoxExtensionBasisVector lam q V) = 0 := by
  let TP := S05_Lem5_13_twoBoxExtensionTableau lam p U
  let TQ := S05_Lem5_13_twoBoxExtensionTableau lam q V
  have hTP_TQ : TP ≠ TQ := by
    simpa [TP, TQ] using S05_twoBoxExtension_ne_of_removal_ne
      lam hpq U V
  have hrowP : ¬ adjacentSameRow TP (Fin.last n) := by
    simpa [TP] using S05_twoBoxExtension_not_sameRow_of_negative
      lam p hnegP U
  have hrowQ : ¬ adjacentSameRow TQ (Fin.last n) := by
    simpa [TQ] using S05_twoBoxExtension_not_sameRow_of_negative
      lam q hnegQ V
  by_cases hcolsP :
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 =
        youngRow (twoStepFirstChild lam p) p.first.1
  · have hcolP : adjacentSameCol TP (Fin.last n) := by
      exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
        lam p U).2 hcolsP
    by_cases hcolsQ :
        youngRow (deleteTwoRemovableRowsDiagram lam q) q.second.1 =
          youngRow (twoStepFirstChild lam q) q.first.1
    · have hcolQ : adjacentSameCol TQ (Fin.last n) := by
        exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
          lam q V).2 hcolsQ
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_neg hnegP, dif_pos (by simpa [TP] using hcolP),
        dif_neg hnegQ, dif_pos (by simpa [TQ] using hcolQ)]
      exact tableauInner_basis_basis_ne hTP_TQ
    · have hcolQ : ¬ adjacentSameCol TQ (Fin.last n) := by
        intro h
        exact hcolsQ
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
            lam q V).1 h)
      have hTP_swapQ : TP ≠ adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_negative
              lam hnegQ hnegP V U hrowQ hcolQ)
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_neg hnegP, dif_pos (by simpa [TP] using hcolP),
        dif_neg hnegQ, dif_neg (by simpa [TQ] using hcolQ)]
      exact S05_tableauInner_basis_normalizedMinus_of_disjoint
        TP TQ (Fin.last n) hrowQ hcolQ hTP_TQ hTP_swapQ
  · have hcolP : ¬ adjacentSameCol TP (Fin.last n) := by
      intro h
      exact hcolsP
        ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
          lam p U).1 h)
    by_cases hcolsQ :
        youngRow (deleteTwoRemovableRowsDiagram lam q) q.second.1 =
          youngRow (twoStepFirstChild lam q) q.first.1
    · have hcolQ : adjacentSameCol TQ (Fin.last n) := by
        exact (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
          lam q V).2 hcolsQ
      have hTQ_swapP : TQ ≠ adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_negative
              lam hnegP hnegQ U V hrowP hcolP)
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_neg hnegP, dif_neg (by simpa [TP] using hcolP),
        dif_neg hnegQ, dif_pos (by simpa [TQ] using hcolQ)]
      rw [S05_tableauInner_symm]
      exact S05_tableauInner_basis_normalizedMinus_of_disjoint
        TQ TP (Fin.last n) hrowP hcolP (Ne.symm hTP_TQ) hTQ_swapP
    · have hcolQ : ¬ adjacentSameCol TQ (Fin.last n) := by
        intro h
        exact hcolsQ
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
            lam q V).1 h)
      have hTP_swapQ : TP ≠ adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        exact Ne.symm (by
          simpa [TP, TQ] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_negative
              lam hnegQ hnegP V U hrowQ hcolQ)
      have hswapP_TQ : adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) ≠ TQ := by
        simpa [TP, TQ] using
          S05_twoBoxExtension_finalSwap_ne_extension_of_negative
            lam hnegP hnegQ U V hrowP hcolP
      have hswapP_swapQ : adjacentSwapTableau TP (Fin.last n)
          (by simpa [adjacentSameRow] using hrowP)
          (by simpa [adjacentSameCol] using hcolP) ≠
        adjacentSwapTableau TQ (Fin.last n)
          (by simpa [adjacentSameRow] using hrowQ)
          (by simpa [adjacentSameCol] using hcolQ) := by
        simpa [TP, TQ] using
          S05_twoBoxExtension_finalSwap_ne_finalSwap_of_removal_ne
            lam hpq U V hrowP hcolP hrowQ hcolQ
      simp only [S05_signedTwoBoxExtensionBasisVector,
        dif_neg hnegP, dif_neg (by simpa [TP] using hcolP),
        dif_neg hnegQ, dif_neg (by simpa [TQ] using hcolQ)]
      exact S05_normalizedAdjacentMinusVector_inner_of_disjoint
        TP TQ (Fin.last n) hrowP hcolP hrowQ hcolQ hTP_TQ
          hTP_swapQ hswapP_TQ hswapP_swapQ

/-- For one fixed signed two-box child, the explicit images of child tableau
basis vectors form an orthonormal family. -/
theorem S05_signedTwoBoxExtensionBasisVector_inner
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
        (S05_signedTwoBoxExtensionBasisVector lam p V) =
      if U = V then 1 else 0 := by
  classical
  by_cases hUV : U = V
  · subst V
    rw [if_pos rfl]
    exact S05_signedTwoBoxExtensionBasisVector_inner_self lam p U
  · rw [if_neg hUV]
    let TU := S05_Lem5_13_twoBoxExtensionTableau lam p U
    let TV := S05_Lem5_13_twoBoxExtensionTableau lam p V
    have hTU_TV : TU ≠ TV := by
      intro h
      exact hUV (S05_Lem5_13_twoBoxExtensionTableau_injective lam p h)
    by_cases hpos : p.first.1 <= p.second.1
    · by_cases hrowU : adjacentSameRow TU (Fin.last n)
      · have hrowV : adjacentSameRow TV (Fin.last n) :=
          (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff lam p V).2
            ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff lam p U).1
              (by simpa [TU] using hrowU))
        simp only [S05_signedTwoBoxExtensionBasisVector, dif_pos hpos,
          dif_pos (by simpa [TU] using hrowU),
          dif_pos (by simpa [TV] using hrowV)]
        exact tableauInner_basis_basis_ne hTU_TV
      · have hrowV : ¬ adjacentSameRow TV (Fin.last n) := by
          intro h
          apply hrowU
          simpa [TU] using
            (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff lam p U).2
              ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff lam p V).1
                (by simpa [TV] using h))
        have hcolU : ¬ adjacentSameCol TU (Fin.last n) := by
          simpa [TU] using
            S05_twoBoxExtension_not_sameCol_of_positive lam p hpos U
        have hcolV : ¬ adjacentSameCol TV (Fin.last n) := by
          simpa [TV] using
            S05_twoBoxExtension_not_sameCol_of_positive lam p hpos V
        have hTU_swapV : TU ≠ adjacentSwapTableau TV (Fin.last n)
            (by simpa [adjacentSameRow] using hrowV)
            (by simpa [adjacentSameCol] using hcolV) := by
          exact Ne.symm (by
            simpa [TU, TV] using
              S05_twoBoxExtension_finalSwap_ne_extension_of_ne lam p
                (Ne.symm hUV) hrowV hcolV)
        have hswapU_TV : adjacentSwapTableau TU (Fin.last n)
            (by simpa [adjacentSameRow] using hrowU)
            (by simpa [adjacentSameCol] using hcolU) ≠ TV := by
          simpa [TU, TV] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_ne lam p hUV
              hrowU hcolU
        have hswapU_swapV : adjacentSwapTableau TU (Fin.last n)
            (by simpa [adjacentSameRow] using hrowU)
            (by simpa [adjacentSameCol] using hcolU) ≠
              adjacentSwapTableau TV (Fin.last n)
                (by simpa [adjacentSameRow] using hrowV)
                (by simpa [adjacentSameCol] using hcolV) := by
          simpa [TU, TV] using
            S05_twoBoxExtension_finalSwap_ne_finalSwap_of_ne lam p hUV
              hrowU hcolU hrowV hcolV
        simp only [S05_signedTwoBoxExtensionBasisVector, dif_pos hpos,
          dif_neg (by simpa [TU] using hrowU),
          dif_neg (by simpa [TV] using hrowV)]
        exact S05_normalizedAdjacentPlusVector_inner_of_disjoint
          TU TV (Fin.last n) hrowU hcolU hrowV hcolV hTU_TV
            hTU_swapV hswapU_TV hswapU_swapV
    · have hrowU : ¬ adjacentSameRow TU (Fin.last n) := by
        simpa [TU] using
          S05_twoBoxExtension_not_sameRow_of_negative lam p hpos U
      have hrowV : ¬ adjacentSameRow TV (Fin.last n) := by
        simpa [TV] using
          S05_twoBoxExtension_not_sameRow_of_negative lam p hpos V
      by_cases hcolU : adjacentSameCol TU (Fin.last n)
      · have hcolV : adjacentSameCol TV (Fin.last n) :=
          (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff lam p V).2
            ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff lam p U).1
              (by simpa [TU] using hcolU))
        simp only [S05_signedTwoBoxExtensionBasisVector, dif_neg hpos,
          dif_pos (by simpa [TU] using hcolU),
          dif_pos (by simpa [TV] using hcolV)]
        exact tableauInner_basis_basis_ne hTU_TV
      · have hcolV : ¬ adjacentSameCol TV (Fin.last n) := by
          intro h
          apply hcolU
          simpa [TU] using
            (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff lam p U).2
              ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff lam p V).1
                (by simpa [TV] using h))
        have hTU_swapV : TU ≠ adjacentSwapTableau TV (Fin.last n)
            (by simpa [adjacentSameRow] using hrowV)
            (by simpa [adjacentSameCol] using hcolV) := by
          exact Ne.symm (by
            simpa [TU, TV] using
              S05_twoBoxExtension_finalSwap_ne_extension_of_ne lam p
                (Ne.symm hUV) hrowV hcolV)
        have hswapU_TV : adjacentSwapTableau TU (Fin.last n)
            (by simpa [adjacentSameRow] using hrowU)
            (by simpa [adjacentSameCol] using hcolU) ≠ TV := by
          simpa [TU, TV] using
            S05_twoBoxExtension_finalSwap_ne_extension_of_ne lam p hUV
              hrowU hcolU
        have hswapU_swapV : adjacentSwapTableau TU (Fin.last n)
            (by simpa [adjacentSameRow] using hrowU)
            (by simpa [adjacentSameCol] using hcolU) ≠
              adjacentSwapTableau TV (Fin.last n)
                (by simpa [adjacentSameRow] using hrowV)
                (by simpa [adjacentSameCol] using hcolV) := by
          simpa [TU, TV] using
            S05_twoBoxExtension_finalSwap_ne_finalSwap_of_ne lam p hUV
              hrowU hcolU hrowV hcolV
        simp only [S05_signedTwoBoxExtensionBasisVector, dif_neg hpos,
          dif_neg (by simpa [TU] using hcolU),
          dif_neg (by simpa [TV] using hcolV)]
        exact S05_normalizedAdjacentMinusVector_inner_of_disjoint
          TU TV (Fin.last n) hrowU hcolU hrowV hcolV hTU_TV
            hTU_swapV hswapU_TV hswapU_swapV

/-- In the positive same-row case, the signed embedding is the raw ordered
extension embedding. -/
theorem S05_signedTwoBoxChildEmbedding_eq_raw_of_positive_sameRow
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (hpos : p.first.1 <= p.second.1)
    (hrow : p.second.1 = p.first.1) :
    S05_signedTwoBoxChildEmbedding lam p f =
      S05_twoStepExtensionEmbedding lam p f := by
  classical
  funext T
  simp only [S05_signedTwoBoxChildEmbedding, S05_twoStepExtensionEmbedding]
  apply Finset.sum_congr rfl
  intro U _hU
  have hrowU : adjacentSameRow
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) :=
    (S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff lam p U).2 hrow
  rw [S05_signedTwoBoxExtensionBasisVector]
  dsimp only
  rw [dif_pos hpos, dif_pos hrowU]

/-- In the negative same-column case, the signed embedding is the raw ordered
extension embedding. -/
theorem S05_signedTwoBoxChildEmbedding_eq_raw_of_negative_sameCol
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (hneg : ¬ p.first.1 <= p.second.1)
    (hcol :
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 =
        youngRow (twoStepFirstChild lam p) p.first.1) :
    S05_signedTwoBoxChildEmbedding lam p f =
      S05_twoStepExtensionEmbedding lam p f := by
  classical
  funext T
  simp only [S05_signedTwoBoxChildEmbedding, S05_twoStepExtensionEmbedding]
  apply Finset.sum_congr rfl
  intro U _hU
  have hcolU : adjacentSameCol
      (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) :=
    (S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff lam p U).2 hcol
  rw [S05_signedTwoBoxExtensionBasisVector]
  dsimp only
  rw [dif_neg hneg, dif_pos hcolU]

/-- In the disconnected positive case, the signed embedding is the normalized
`+1` projection of the raw extension embedding. -/
theorem S05_signedTwoBoxChildEmbedding_eq_plusProjection
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (hpos : p.first.1 <= p.second.1)
    (hrow : p.second.1 ≠ p.first.1) :
    S05_signedTwoBoxChildEmbedding lam p f =
      fun T =>
        (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (S05_twoStepExtensionEmbedding lam p f T +
            youngAdjacentOperator (Fin.last n)
              (S05_twoStepExtensionEmbedding lam p f) T) := by
  classical
  rw [S05_twoStepExtensionEmbedding_operator_expansion]
  funext T
  change
    (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
      f U * S05_signedTwoBoxExtensionBasisVector lam p U T) =
      (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
        ((∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * tableauBasisVec
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) +
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * youngAdjacentOperator (Fin.last n)
            (tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)
  calc
    _ = ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U *
          ((Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U) T +
              youngAdjacentOperator (Fin.last n)
                (tableauBasisVec
                  (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)) := by
      apply Finset.sum_congr rfl
      intro U _hU
      have hrowU : ¬ adjacentSameRow
          (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) := by
        intro hp
        exact hrow
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
            lam p U).1 hp)
      rw [S05_signedTwoBoxExtensionBasisVector_eq_plusProjection
        lam p U hpos hrowU]
    _ = ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p), (
        (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (f U * tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) +
          (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (f U * youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)) := by
      apply Finset.sum_congr rfl
      intro U _hU
      ring
    _ = (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            f U * tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) +
        (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            f U * youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by ring

/-- In the disconnected negative case, the signed embedding is the normalized
`-1` projection of the raw extension embedding. -/
theorem S05_signedTwoBoxChildEmbedding_eq_minusProjection
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (hneg : ¬ p.first.1 <= p.second.1)
    (hcol :
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 ≠
        youngRow (twoStepFirstChild lam p) p.first.1) :
    S05_signedTwoBoxChildEmbedding lam p f =
      fun T =>
        (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (S05_twoStepExtensionEmbedding lam p f T -
            youngAdjacentOperator (Fin.last n)
              (S05_twoStepExtensionEmbedding lam p f) T) := by
  classical
  rw [S05_twoStepExtensionEmbedding_operator_expansion]
  funext T
  change
    (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
      f U * S05_signedTwoBoxExtensionBasisVector lam p U T) =
      (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
        ((∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * tableauBasisVec
            (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) -
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * youngAdjacentOperator (Fin.last n)
            (tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)
  calc
    _ = ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U *
          ((Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U) T -
              youngAdjacentOperator (Fin.last n)
                (tableauBasisVec
                  (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)) := by
      apply Finset.sum_congr rfl
      intro U _hU
      have hcolU : ¬ adjacentSameCol
          (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) := by
        intro hp
        exact hcol
          ((S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
            lam p U).1 hp)
      rw [S05_signedTwoBoxExtensionBasisVector_eq_minusProjection
        lam p U hneg hcolU]
    _ = ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p), (
        (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (f U * tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) -
          (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
            (f U * youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T)) := by
      apply Finset.sum_congr rfl
      intro U _hU
      ring
    _ = (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            f U * tableauBasisVec
              (S05_Lem5_13_twoBoxExtensionTableau lam p U) T) -
        (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
          ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            f U * youngAdjacentOperator (Fin.last n)
              (tableauBasisVec
                (S05_Lem5_13_twoBoxExtensionTableau lam p U)) T := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by ring

/-- The signed child embedding sends a child basis vector to the corresponding
explicit signed extension vector. -/
theorem S05_signedTwoBoxChildEmbedding_basis
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    S05_signedTwoBoxChildEmbedding lam p (tableauBasisVec U) =
      S05_signedTwoBoxExtensionBasisVector lam p U := by
  classical
  funext T
  rw [S05_signedTwoBoxChildEmbedding]
  rw [Fintype.sum_eq_single U]
  · simp [tableauBasisVec]
  · intro V hVU
    simp [tableauBasisVec, hVU]

/-- The signed child embedding is additive. -/
theorem S05_signedTwoBoxChildEmbedding_add
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f g : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    S05_signedTwoBoxChildEmbedding lam p (f + g) =
      S05_signedTwoBoxChildEmbedding lam p f +
        S05_signedTwoBoxChildEmbedding lam p g := by
  classical
  funext T
  simp only [S05_signedTwoBoxChildEmbedding, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- The signed child embedding commutes with real scalar multiplication. -/
theorem S05_signedTwoBoxChildEmbedding_smul
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) (c : Real)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    S05_signedTwoBoxChildEmbedding lam p (c • f) =
      c • S05_signedTwoBoxChildEmbedding lam p f := by
  classical
  funext T
  simp only [S05_signedTwoBoxChildEmbedding, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _hU
  ring

/-- Each signed two-box child embedding preserves the tableau-coordinate inner
product. -/
theorem S05_signedTwoBoxChildEmbedding_isometry
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f g : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    tableauInner (S05_signedTwoBoxChildEmbedding lam p f)
        (S05_signedTwoBoxChildEmbedding lam p g) =
      tableauInner f g := by
  classical
  rw [tableauInner, tableauInner]
  change
    (∑ T : StandardYoungTableau lam,
      (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U * S05_signedTwoBoxExtensionBasisVector lam p U T) *
      (∑ V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        g V * S05_signedTwoBoxExtensionBasisVector lam p V T)) =
      ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U * g U
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _hU
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single U]
  · calc
      (∑ T : StandardYoungTableau lam,
          f U * S05_signedTwoBoxExtensionBasisVector lam p U T *
            (g U * S05_signedTwoBoxExtensionBasisVector lam p U T)) =
          (f U * g U) *
            tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
              (S05_signedTwoBoxExtensionBasisVector lam p U) := by
            rw [tableauInner, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro T _hT
            ring
      _ = f U * g U := by
        rw [S05_signedTwoBoxExtensionBasisVector_inner_self]
        ring
  · intro V hVU
    have hinner := S05_signedTwoBoxExtensionBasisVector_inner lam p U V
    rw [if_neg (Ne.symm hVU)] at hinner
    calc
      (∑ T : StandardYoungTableau lam,
          f U * S05_signedTwoBoxExtensionBasisVector lam p U T *
            (g V * S05_signedTwoBoxExtensionBasisVector lam p V T)) =
          (f U * g V) *
            tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
              (S05_signedTwoBoxExtensionBasisVector lam p V) := by
            rw [tableauInner, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro T _hT
            ring
      _ = 0 := by rw [hinner]; ring

/-- Every signed two-box child embedding is injective. -/
theorem S05_signedTwoBoxChildEmbedding_injective
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    Function.Injective (S05_signedTwoBoxChildEmbedding lam p) := by
  intro f g hfg
  funext U
  have hinner := congrArg
    (fun h => tableauInner h
      (S05_signedTwoBoxChildEmbedding lam p (tableauBasisVec U))) hfg
  rw [S05_signedTwoBoxChildEmbedding_isometry,
    S05_signedTwoBoxChildEmbedding_isometry] at hinner
  simpa [tableauInner_right_basis] using hinner

/-- The whole signed child embedding has the sign prescribed by its ordered
two-box removal under the final adjacent operator. -/
theorem S05_signedTwoBoxChildEmbedding_finalOperator
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOperator (Fin.last n)
        (S05_signedTwoBoxChildEmbedding lam p f) =
      S05_signedTwoBoxRemovalSign p •
        S05_signedTwoBoxChildEmbedding lam p f := by
  classical
  change
    youngAdjacentOperator (Fin.last n)
        (fun T =>
          ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
            f U * S05_signedTwoBoxExtensionBasisVector lam p U T) =
      fun T => S05_signedTwoBoxRemovalSign p *
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * S05_signedTwoBoxExtensionBasisVector lam p U T
  rw [youngAdjacentOperator_sum]
  funext T
  simp_rw [youngAdjacentOperator_smul,
    S05_signedTwoBoxExtensionBasisVector_finalOperator]
  change
    (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
      f U * (S05_signedTwoBoxRemovalSign p *
        S05_signedTwoBoxExtensionBasisVector lam p U T)) =
      S05_signedTwoBoxRemovalSign p *
        ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
          f U * S05_signedTwoBoxExtensionBasisVector lam p U T
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _hU
  ring

/-- The explicit signed two-box child embedding intertwines every adjacent
operator belonging to the child with the corresponding parent operator. -/
theorem S05_signedTwoBoxChildEmbedding_intertwinesEarlierAdjacent
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam) (a : Fin n)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
        (S05_signedTwoBoxChildEmbedding lam p f) =
      S05_signedTwoBoxChildEmbedding lam p
        (youngAdjacentOperator a f) := by
  let ap : Fin ((n + 1) + 1) := Fin.castSucc (Fin.castSucc a)
  let b : Fin ((n + 1) + 1) := Fin.last (n + 1)
  have hdisj : adjacentIndexDisjoint ap b := by
    unfold adjacentIndexDisjoint ap b
    left
    simp
  by_cases hpos : p.first.1 <= p.second.1
  · by_cases hrow : p.second.1 = p.first.1
    · rw [S05_signedTwoBoxChildEmbedding_eq_raw_of_positive_sameRow
          lam p f hpos hrow,
        S05_signedTwoBoxChildEmbedding_eq_raw_of_positive_sameRow
          lam p (youngAdjacentOperator a f) hpos hrow]
      exact S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent
        lam p a f
    · rw [S05_signedTwoBoxChildEmbedding_eq_plusProjection
          lam p f hpos hrow,
        S05_signedTwoBoxChildEmbedding_eq_plusProjection
          lam p (youngAdjacentOperator a f) hpos hrow]
      change youngAdjacentOperator ap
          (fun T =>
            (Real.sqrt (2 * (1 + S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
              (S05_twoStepExtensionEmbedding lam p f T +
                youngAdjacentOperator b
                  (S05_twoStepExtensionEmbedding lam p f) T)) = _
      rw [youngAdjacentOperator_smul, youngAdjacentOperator_add,
        youngAdjacentOperator_comm_of_disjoint_indices ap b hdisj,
        S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent]
  · by_cases hcol :
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 =
        youngRow (twoStepFirstChild lam p) p.first.1
    · rw [S05_signedTwoBoxChildEmbedding_eq_raw_of_negative_sameCol
          lam p f hpos hcol,
        S05_signedTwoBoxChildEmbedding_eq_raw_of_negative_sameCol
          lam p (youngAdjacentOperator a f) hpos hcol]
      exact S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent
        lam p a f
    · rw [S05_signedTwoBoxChildEmbedding_eq_minusProjection
          lam p f hpos hcol,
        S05_signedTwoBoxChildEmbedding_eq_minusProjection
          lam p (youngAdjacentOperator a f) hpos hcol]
      change youngAdjacentOperator ap
          (fun T =>
            (Real.sqrt (2 * (1 - S05_twoBoxFinalDiagCoeff lam p)))⁻¹ *
              (S05_twoStepExtensionEmbedding lam p f T -
                youngAdjacentOperator b
                  (S05_twoStepExtensionEmbedding lam p f) T)) = _
      rw [youngAdjacentOperator_smul]
      have hsub :
          youngAdjacentOperator ap
              (fun T => S05_twoStepExtensionEmbedding lam p f T -
                youngAdjacentOperator b
                  (S05_twoStepExtensionEmbedding lam p f) T) =
            fun T =>
              youngAdjacentOperator ap
                  (S05_twoStepExtensionEmbedding lam p f) T -
                youngAdjacentOperator ap
                  (youngAdjacentOperator b
                    (S05_twoStepExtensionEmbedding lam p f)) T := by
        change youngAdjacentOperator ap
            (fun T => S05_twoStepExtensionEmbedding lam p f T +
              -(youngAdjacentOperator b
                (S05_twoStepExtensionEmbedding lam p f) T)) = _
        rw [youngAdjacentOperator_add, youngAdjacentOperator_neg]
        funext T
        ring
      rw [hsub,
        youngAdjacentOperator_comm_of_disjoint_indices ap b hdisj,
        S05_twoStepExtensionEmbedding_intertwinesEarlierAdjacent]

/-- If two signed-child basis families are pointwise orthogonal, then their
full coordinate ranges are orthogonal. -/
theorem S05_signedTwoBoxChildEmbedding_inner_eq_zero_of_basis
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p q : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (g : TableauSpace (deleteTwoRemovableRowsDiagram lam q))
    (hbasis : ∀
      (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
      (V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q)),
      tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
        (S05_signedTwoBoxExtensionBasisVector lam q V) = 0) :
    tableauInner (S05_signedTwoBoxChildEmbedding lam p f)
      (S05_signedTwoBoxChildEmbedding lam q g) = 0 := by
  classical
  rw [tableauInner]
  change
    (∑ T : StandardYoungTableau lam,
      (∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
        f U * S05_signedTwoBoxExtensionBasisVector lam p U T) *
      (∑ V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam q),
        g V * S05_signedTwoBoxExtensionBasisVector lam q V T)) = 0
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro U _hU
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro V _hV
  calc
    (∑ T : StandardYoungTableau lam,
      f U * S05_signedTwoBoxExtensionBasisVector lam p U T *
        (g V * S05_signedTwoBoxExtensionBasisVector lam q V T)) =
      (f U * g V) *
        tableauInner (S05_signedTwoBoxExtensionBasisVector lam p U)
          (S05_signedTwoBoxExtensionBasisVector lam q V) := by
      rw [tableauInner, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _hT
      ring
    _ = 0 := by rw [hbasis U V]; ring

/-- The coordinate ranges of distinct signed two-box children are pairwise
orthogonal. -/
theorem S05_signedTwoBoxChildEmbedding_ranges_orthogonal
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    {p q : TwoStepRemovableRows lam} (hpq : p ≠ q)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
    (g : TableauSpace (deleteTwoRemovableRowsDiagram lam q)) :
    tableauInner (S05_signedTwoBoxChildEmbedding lam p f)
      (S05_signedTwoBoxChildEmbedding lam q g) = 0 := by
  by_cases hposP : p.first.1 <= p.second.1
  · by_cases hposQ : q.first.1 <= q.second.1
    · exact S05_signedTwoBoxChildEmbedding_inner_eq_zero_of_basis
        lam p q f g
        (S05_signedTwoBoxExtensionBasisVector_inner_of_distinct_positive
          lam hpq hposP hposQ)
    · apply S05_tableauInner_eq_zero_of_distinct_adjacent_eigenvalues
        (Fin.last n)
        (S05_signedTwoBoxChildEmbedding lam p f)
        (S05_signedTwoBoxChildEmbedding lam q g) 1 (-1)
      · simpa [S05_signedTwoBoxRemovalSign, hposP] using
          S05_signedTwoBoxChildEmbedding_finalOperator lam p f
      · simpa [S05_signedTwoBoxRemovalSign, hposQ] using
          S05_signedTwoBoxChildEmbedding_finalOperator lam q g
      · norm_num
  · by_cases hposQ : q.first.1 <= q.second.1
    · apply S05_tableauInner_eq_zero_of_distinct_adjacent_eigenvalues
        (Fin.last n)
        (S05_signedTwoBoxChildEmbedding lam p f)
        (S05_signedTwoBoxChildEmbedding lam q g) (-1) 1
      · simpa [S05_signedTwoBoxRemovalSign, hposP] using
          S05_signedTwoBoxChildEmbedding_finalOperator lam p f
      · simpa [S05_signedTwoBoxRemovalSign, hposQ] using
          S05_signedTwoBoxChildEmbedding_finalOperator lam q g
      · norm_num
    · exact S05_signedTwoBoxChildEmbedding_inner_eq_zero_of_basis
        lam p q f g
        (S05_signedTwoBoxExtensionBasisVector_inner_of_distinct_negative
          lam hpq hposP hposQ)

local instance S05_signedTwoBoxBasisIndexDecidableEq
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    DecidableEq (S05_SignedTwoBoxBasisIndex lam) :=
  Classical.decEq _

/-- The global signed-child family in the parent tableau coordinate space. -/
noncomputable def S05_signedTwoBoxGlobalBasisVector
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : S05_SignedTwoBoxBasisIndex lam) : TableauSpace lam :=
  S05_signedTwoBoxExtensionBasisVector lam x.1 x.2

/-- The global signed-child family is orthonormal. -/
theorem S05_signedTwoBoxGlobalBasisVector_inner
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x y : S05_SignedTwoBoxBasisIndex lam) :
    tableauInner (S05_signedTwoBoxGlobalBasisVector lam x)
        (S05_signedTwoBoxGlobalBasisVector lam y) =
      if x = y then 1 else 0 := by
  classical
  rcases x with ⟨p, U⟩
  rcases y with ⟨q, V⟩
  simp only [S05_signedTwoBoxGlobalBasisVector]
  by_cases hpq : p = q
  · subst q
    simpa using S05_signedTwoBoxExtensionBasisVector_inner lam p U V
  · have hinner := S05_signedTwoBoxChildEmbedding_ranges_orthogonal
      lam hpq (tableauBasisVec U) (tableauBasisVec V)
    rw [S05_signedTwoBoxChildEmbedding_basis,
      S05_signedTwoBoxChildEmbedding_basis] at hinner
    have hxy :
        (⟨p, U⟩ : S05_SignedTwoBoxBasisIndex lam) ≠ ⟨q, V⟩ := by
      intro h
      exact hpq (congrArg Sigma.fst h)
    simpa [hxy] using hinner

/-- The signed-child sigma index has exactly as many elements as the parent
tableau basis. -/
theorem S05_card_signedTwoBoxBasisIndex
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    Fintype.card (S05_SignedTwoBoxBasisIndex lam) =
      Fintype.card (StandardYoungTableau lam) := by
  classical
  rw [Fintype.card_sigma]
  have hdim := tableauDim_eq_sum_twoStepRemovableRows lam
  unfold tableauDim tableauDimNat at hdim
  exact_mod_cast hdim.symm

/-- Inner product commutes with a finite sum in its left argument. -/
theorem S05_tableauInner_sum_left
    {n : Nat} {lam : YoungDiagram n} {ι : Type} [Fintype ι]
    (f : ι -> TableauSpace lam) (g : TableauSpace lam) :
    tableauInner (fun T => ∑ i : ι, f i T) g =
      ∑ i : ι, tableauInner (f i) g := by
  classical
  unfold tableauInner
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The global signed-child family is linearly independent. -/
theorem S05_signedTwoBoxGlobalBasisVector_linearIndependent
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    LinearIndependent Real (S05_signedTwoBoxGlobalBasisVector lam) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  have hinner := congrArg
    (fun f => tableauInner f (S05_signedTwoBoxGlobalBasisVector lam x)) hc
  have hcomb :
      (∑ i : S05_SignedTwoBoxBasisIndex lam,
          c i • S05_signedTwoBoxGlobalBasisVector lam i) =
        fun T => ∑ i : S05_SignedTwoBoxBasisIndex lam,
          c i * S05_signedTwoBoxGlobalBasisVector lam i T := by
    funext T
    simp
  rw [hcomb] at hinner
  rw [S05_tableauInner_sum_left] at hinner
  simp_rw [S05_tableauInner_mul_left,
    S05_signedTwoBoxGlobalBasisVector_inner] at hinner
  simpa [tableauInner] using hinner

/-- The signed-child family spans the full parent tableau coordinate space. -/
theorem S05_signedTwoBoxChildEmbeddings_span
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    Submodule.span Real
        (Set.range (S05_signedTwoBoxGlobalBasisVector lam)) = ⊤ := by
  classical
  apply
    (S05_signedTwoBoxGlobalBasisVector_linearIndependent lam).span_eq_top_of_card_eq_finrank'
  rw [S05_card_signedTwoBoxBasisIndex]
  exact (Module.finrank_pi Real :
      Module.finrank Real (StandardYoungTableau lam -> Real) =
        Fintype.card (StandardYoungTableau lam)).symm

/-- Internal signed two-box orthogonal decomposition: the explicit child
embeddings are isometric, have the prescribed final sign, intertwine every
earlier adjacent operator, have pairwise orthogonal ranges, and jointly span
the parent tableau space. -/
theorem S05_signedTwoBoxChild_orthogonal_decomposition
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1)) :
    (∀ (p : TwoStepRemovableRows lam)
      (f g : TableauSpace (deleteTwoRemovableRowsDiagram lam p)),
      tableauInner (S05_signedTwoBoxChildEmbedding lam p f)
          (S05_signedTwoBoxChildEmbedding lam p g) = tableauInner f g) ∧
    (∀ (p : TwoStepRemovableRows lam)
      (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)),
      youngAdjacentOperator (Fin.last (n + 1))
          (S05_signedTwoBoxChildEmbedding lam p f) =
        S05_signedTwoBoxRemovalSign p •
          S05_signedTwoBoxChildEmbedding lam p f) ∧
    (∀ (a : Fin n) (p : TwoStepRemovableRows lam)
      (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)),
      youngAdjacentOperator (Fin.castSucc (Fin.castSucc a))
          (S05_signedTwoBoxChildEmbedding lam p f) =
        S05_signedTwoBoxChildEmbedding lam p
          (youngAdjacentOperator a f)) ∧
    (∀ (p q : TwoStepRemovableRows lam), p ≠ q ->
      ∀ (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p))
        (g : TableauSpace (deleteTwoRemovableRowsDiagram lam q)),
        tableauInner (S05_signedTwoBoxChildEmbedding lam p f)
          (S05_signedTwoBoxChildEmbedding lam q g) = 0) ∧
    Submodule.span Real
        (Set.range (S05_signedTwoBoxGlobalBasisVector lam)) = ⊤ := by
  refine ⟨S05_signedTwoBoxChildEmbedding_isometry lam,
    S05_signedTwoBoxChildEmbedding_finalOperator lam, ?_, ?_,
    S05_signedTwoBoxChildEmbeddings_span lam⟩
  · intro a p f
    exact S05_signedTwoBoxChildEmbedding_intertwinesEarlierAdjacent
      lam p a f
  · intro p q hpq f g
    exact S05_signedTwoBoxChildEmbedding_ranges_orthogonal lam hpq f g

/-!
## Recursive canonical even eigenbasis

The recursive index below records an ordered signed two-box child at each
stage.  The order is mathematically significant: for a disconnected two-box
skew shape, the two deletion orders give the positive and negative copies of
the same child.  Thus the sigma type retains exactly the multiplicity present
in `S05_evenSignPatternMultiset`.
-/

/-- The unique standard tableau of an empty Young diagram. -/
noncomputable def S05_emptyStandardYoungTableau
    (lam : YoungDiagram 0) : StandardYoungTableau lam where
  entry := fun u => Fin.elim0 u.1.1
  bijective := by
    constructor
    · intro u
      exact Fin.elim0 u.1.1
    · intro a
      exact Fin.elim0 a
  row_strict := by
    intro u
    exact Fin.elim0 u.1.1
  col_strict := by
    intro u
    exact Fin.elim0 u.1.1

/-- Recursive finite index for the canonical even matching eigenbasis. -/
def S05_CanonicalEvenEigenbasisIndex :
    (m : Nat) → YoungDiagram (2 * m) → Type
  | 0, _ => PUnit
  | m + 1, lam =>
      Sigma fun p : TwoStepRemovableRows lam =>
        S05_CanonicalEvenEigenbasisIndex m
          (deleteTwoRemovableRowsDiagram lam p)

/-- The recursive index is finite at every level. -/
@[reducible] noncomputable def S05_canonicalEvenEigenbasisIndexFintype :
    (m : Nat) → (lam : YoungDiagram (2 * m)) →
      Fintype (S05_CanonicalEvenEigenbasisIndex m lam)
  | 0, _ => by
      change Fintype PUnit
      infer_instance
  | m + 1, lam => by
      change Fintype (Sigma fun p : TwoStepRemovableRows lam =>
        S05_CanonicalEvenEigenbasisIndex m
          (deleteTwoRemovableRowsDiagram lam p))
      letI (p : TwoStepRemovableRows lam) :=
        S05_canonicalEvenEigenbasisIndexFintype m
          (deleteTwoRemovableRowsDiagram lam p)
      infer_instance

private def S05_twoStepRemovableRowsKey {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (p : TwoStepRemovableRows lam) : Nat × Nat :=
  (p.first.1, p.second.1)

private theorem S05_twoStepRemovableRowsKey_injective {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} :
    Function.Injective (@S05_twoStepRemovableRowsKey n lam) := by
  intro p q h
  change (p.first.1, p.second.1) = (q.first.1, q.second.1) at h
  apply twoStepRemovableRows_ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

private noncomputable def S05_twoStepRemovableRowsDecidableEq {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    DecidableEq (TwoStepRemovableRows lam) :=
  Function.Injective.decidableEq S05_twoStepRemovableRowsKey_injective

/-- Decidable equality obtained recursively from the signed-child index. -/
@[reducible] noncomputable def S05_canonicalEvenEigenbasisIndexDecidableEq :
    (m : Nat) → (lam : YoungDiagram (2 * m)) →
      DecidableEq (S05_CanonicalEvenEigenbasisIndex m lam)
  | 0, _ => by
      change DecidableEq PUnit
      infer_instance
  | m + 1, lam => by
      change DecidableEq (Sigma fun p : TwoStepRemovableRows lam =>
        S05_CanonicalEvenEigenbasisIndex m
          (deleteTwoRemovableRowsDiagram lam p))
      letI : DecidableEq (TwoStepRemovableRows lam) :=
        S05_twoStepRemovableRowsDecidableEq lam
      letI (p : TwoStepRemovableRows lam) :=
        S05_canonicalEvenEigenbasisIndexDecidableEq m
          (deleteTwoRemovableRowsDiagram lam p)
      infer_instance

attribute [instance] S05_canonicalEvenEigenbasisIndexFintype
  S05_canonicalEvenEigenbasisIndexDecidableEq

/-- Explicit recursively transported vector attached to a canonical even
eigenbasis index. -/
noncomputable def S05_canonicalEvenEigenbasisVector :
    (m : Nat) → (lam : YoungDiagram (2 * m)) →
      S05_CanonicalEvenEigenbasisIndex m lam → TableauSpace lam
  | 0, lam, _ => tableauBasisVec (S05_emptyStandardYoungTableau lam)
  | m + 1, lam, ⟨p, i⟩ =>
      S05_signedTwoBoxChildEmbedding lam p
        (S05_canonicalEvenEigenbasisVector m
          (deleteTwoRemovableRowsDiagram lam p) i)

/-- Recursive character label attached to a canonical even eigenbasis index.
The final coordinate is present exactly for a negative signed child. -/
def S05_canonicalEvenEigenbasisLabel :
    (m : Nat) → (lam : YoungDiagram (2 * m)) →
      S05_CanonicalEvenEigenbasisIndex m lam → Finset (Fin m)
  | 0, _, _ => ∅
  | m + 1, lam, ⟨p, i⟩ =>
      if p.first.1 <= p.second.1 then
        S05_liftEvenSignPattern
          (S05_canonicalEvenEigenbasisLabel m
            (deleteTwoRemovableRowsDiagram lam p) i)
      else
        S05_liftEvenSignPatternWithLast
          (S05_canonicalEvenEigenbasisLabel m
            (deleteTwoRemovableRowsDiagram lam p) i)

/-- Multiset of labels of the explicit recursive index, retaining repeated
labels with their full multiplicity. -/
noncomputable def S05_canonicalEvenEigenbasisLabelMultiset
    (m : Nat) (lam : YoungDiagram (2 * m)) : Multiset (Finset (Fin m)) :=
  (Finset.univ : Finset (S05_CanonicalEvenEigenbasisIndex m lam)).1.map
    (S05_canonicalEvenEigenbasisLabel m lam)

@[simp] theorem S05_canonicalEvenEigenbasisLabelMultiset_zero
    (lam : YoungDiagram 0) :
    S05_canonicalEvenEigenbasisLabelMultiset 0 lam = {∅} := by
  classical
  simp [S05_canonicalEvenEigenbasisLabelMultiset,
    S05_CanonicalEvenEigenbasisIndex, S05_canonicalEvenEigenbasisLabel]

private theorem S05_multiset_map_sigma_eq_sum_map
    {α γ : Type*} {β : α → Type*}
    (s : Multiset α) (t : ∀ a, Multiset (β a))
    (f : (Sigma β) → γ) :
    (s.sigma t).map f =
      (s.map fun a => (t a).map fun b => f ⟨a, b⟩).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp [ih]

/-- Expanding the sigma index gives the signed-child recursion for the label
multiset before identifying signed occurrences with strip children. -/
theorem S05_canonicalEvenEigenbasisLabelMultiset_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_canonicalEvenEigenbasisLabelMultiset (m + 1) lam =
      ∑ p : TwoStepRemovableRows lam,
        if p.first.1 <= p.second.1 then
          (S05_canonicalEvenEigenbasisLabelMultiset m
              (deleteTwoRemovableRowsDiagram lam p)).map
            S05_liftEvenSignPattern
        else
          (S05_canonicalEvenEigenbasisLabelMultiset m
              (deleteTwoRemovableRowsDiagram lam p)).map
            S05_liftEvenSignPatternWithLast := by
  classical
  change
    ((Finset.univ : Finset (TwoStepRemovableRows lam)).1.sigma
        (fun p =>
          (Finset.univ : Finset
            (S05_CanonicalEvenEigenbasisIndex m
              (deleteTwoRemovableRowsDiagram lam p))).1)).map
      (fun x =>
        if x.1.first.1 <= x.1.second.1 then
          S05_liftEvenSignPattern
            (S05_canonicalEvenEigenbasisLabel m
              (deleteTwoRemovableRowsDiagram lam x.1) x.2)
        else
          S05_liftEvenSignPatternWithLast
            (S05_canonicalEvenEigenbasisLabel m
              (deleteTwoRemovableRowsDiagram lam x.1) x.2)) = _
  rw [S05_multiset_map_sigma_eq_sum_map]
  simp only [S05_canonicalEvenEigenbasisLabelMultiset,
    Multiset.map_map, Function.comp_apply]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _hp
  by_cases hpos : p.first.1 <= p.second.1 <;> simp [hpos]

/-- Multiplicity-preserving bridge from ordered signed removals to the tagged
horizontal/vertical two-strip children.  In particular, a disconnected child
appears in both sums because its two deletion orders lie on opposite sides of
the row-order test. -/
theorem S05_sum_signedTwoBoxChildren_eq_horizontal_add_vertical
    {α : Type*} [AddCommMonoid α]
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (horizontalValue verticalValue : YoungDiagram (2 * m) → α) :
    (∑ p : TwoStepRemovableRows lam,
        if p.first.1 <= p.second.1 then
          horizontalValue (deleteTwoRemovableRowsDiagram lam p)
        else
          verticalValue (deleteTwoRemovableRowsDiagram lam p)) =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum horizontalValue +
        (verticalTwoStripChildrenEven (m + 1) lam).sum verticalValue := by
  classical
  calc
    (∑ p : TwoStepRemovableRows lam,
        if p.first.1 <= p.second.1 then
          horizontalValue (deleteTwoRemovableRowsDiagram lam p)
        else
          verticalValue (deleteTwoRemovableRowsDiagram lam p)) =
        ∑ x : TaggedTwoStripChildrenSized lam,
          match x with
          | Sum.inl h => horizontalValue h.1
          | Sum.inr v => verticalValue v.1 := by
      exact Fintype.sum_equiv
        (twoStepRemovableRowsEquivTaggedTwoStripChildren lam)
        (fun p : TwoStepRemovableRows lam =>
          if p.first.1 <= p.second.1 then
            horizontalValue (deleteTwoRemovableRowsDiagram lam p)
          else
            verticalValue (deleteTwoRemovableRowsDiagram lam p))
        (fun x : TaggedTwoStripChildrenSized lam =>
          match x with
          | Sum.inl h => horizontalValue h.1
          | Sum.inr v => verticalValue v.1)
        (fun p => by
          by_cases hpos : p.first.1 <= p.second.1 <;>
            simp [twoStepRemovableRowsEquivTaggedTwoStripChildren,
              twoStepToTaggedTwoStripChild, hpos])
    _ = (horizontalTwoStripChildrenSized lam).sum horizontalValue +
          (verticalTwoStripChildrenSized lam).sum verticalValue := by
      rw [Fintype.sum_sum_type]
      congr 1
      · rw [Finset.univ_eq_attach]
        exact Finset.sum_attach
          (horizontalTwoStripChildrenSized lam) horizontalValue
      · rw [Finset.univ_eq_attach]
        exact Finset.sum_attach
          (verticalTwoStripChildrenSized lam) verticalValue
    _ = _ := by
      rw [horizontalTwoStripChildrenSized_eq_even_succ,
        verticalTwoStripChildrenSized_eq_even_succ]
      rfl

/-- The explicit recursive eigenbasis labels reproduce Definition 5.10 as a
literal multiset equality, including every repeated label. -/
theorem S05_canonicalEvenEigenbasisLabelMultiset_eq :
    ∀ (m : Nat) (lam : YoungDiagram (2 * m)),
      S05_canonicalEvenEigenbasisLabelMultiset m lam =
        S05_evenSignPatternMultiset m lam := by
  intro m
  induction m with
  | zero =>
      intro lam
      rw [S05_canonicalEvenEigenbasisLabelMultiset_zero]
      rfl
  | succ m ih =>
      intro lam
      rw [S05_canonicalEvenEigenbasisLabelMultiset_succ]
      simp_rw [ih]
      calc
        (∑ p : TwoStepRemovableRows lam,
            if p.first.1 <= p.second.1 then
              (S05_evenSignPatternMultiset m
                (deleteTwoRemovableRowsDiagram lam p)).map
                  S05_liftEvenSignPattern
            else
              (S05_evenSignPatternMultiset m
                (deleteTwoRemovableRowsDiagram lam p)).map
                  S05_liftEvenSignPatternWithLast) =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu =>
                  (S05_evenSignPatternMultiset m mu).map
                    S05_liftEvenSignPattern) +
              (verticalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu =>
                  (S05_evenSignPatternMultiset m mu).map
                    S05_liftEvenSignPatternWithLast) :=
          S05_sum_signedTwoBoxChildren_eq_horizontal_add_vertical
            m lam
            (fun mu =>
              (S05_evenSignPatternMultiset m mu).map
                S05_liftEvenSignPattern)
            (fun mu =>
              (S05_evenSignPatternMultiset m mu).map
                S05_liftEvenSignPatternWithLast)
        _ = S05_evenSignPatternMultiset (m + 1) lam := rfl

/-- The recursively transported vectors form an orthonormal family. -/
theorem S05_canonicalEvenEigenbasisVector_inner :
    ∀ (m : Nat) (lam : YoungDiagram (2 * m))
      (i j : S05_CanonicalEvenEigenbasisIndex m lam),
      tableauInner
          (S05_canonicalEvenEigenbasisVector m lam i)
          (S05_canonicalEvenEigenbasisVector m lam j) =
        if i = j then 1 else 0 := by
  intro m
  induction m with
  | zero =>
      intro lam i j
      cases i
      cases j
      simp [S05_canonicalEvenEigenbasisVector]
  | succ m ih =>
      intro lam i j
      rcases i with ⟨p, i⟩
      rcases j with ⟨q, j⟩
      by_cases hpq : p = q
      · subst q
        rw [S05_canonicalEvenEigenbasisVector,
          S05_canonicalEvenEigenbasisVector,
          S05_signedTwoBoxChildEmbedding_isometry, ih]
        by_cases hij : i = j
        · subst j
          simp
        · rw [if_neg hij, if_neg]
          intro h
          exact hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      · rw [S05_canonicalEvenEigenbasisVector,
          S05_canonicalEvenEigenbasisVector,
          S05_signedTwoBoxChildEmbedding_ranges_orthogonal lam hpq]
        rw [if_neg]
        intro h
        exact hpq (congrArg Sigma.fst h)

/-- The recursively transported orthonormal family is linearly independent. -/
theorem S05_canonicalEvenEigenbasisVector_linearIndependent
    (m : Nat) (lam : YoungDiagram (2 * m)) :
    LinearIndependent Real (S05_canonicalEvenEigenbasisVector m lam) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  have hinner := congrArg
    (fun f => tableauInner f (S05_canonicalEvenEigenbasisVector m lam x)) hc
  have hcomb :
      (∑ i : S05_CanonicalEvenEigenbasisIndex m lam,
          c i • S05_canonicalEvenEigenbasisVector m lam i) =
        fun T => ∑ i : S05_CanonicalEvenEigenbasisIndex m lam,
          c i * S05_canonicalEvenEigenbasisVector m lam i T := by
    funext T
    simp
  rw [hcomb] at hinner
  rw [S05_tableauInner_sum_left] at hinner
  simp_rw [S05_tableauInner_mul_left,
    S05_canonicalEvenEigenbasisVector_inner] at hinner
  simpa [tableauInner] using hinner

/-- The recursive index has exactly the cardinality of the tableau coordinate
basis. -/
theorem S05_card_canonicalEvenEigenbasisIndex
    (m : Nat) (lam : YoungDiagram (2 * m)) :
    Fintype.card (S05_CanonicalEvenEigenbasisIndex m lam) =
      Fintype.card (StandardYoungTableau lam) := by
  classical
  calc
    Fintype.card (S05_CanonicalEvenEigenbasisIndex m lam) =
        (S05_canonicalEvenEigenbasisLabelMultiset m lam).card := by
      simp [S05_canonicalEvenEigenbasisLabelMultiset]
    _ = (S05_evenSignPatternMultiset m lam).card := by
      rw [S05_canonicalEvenEigenbasisLabelMultiset_eq]
    _ = Fintype.card (StandardYoungTableau lam) := by
      have h := S05_signPatternCardinality_evenSignPatternMultiset_card m lam
      unfold tableauDim tableauDimNat at h
      exact_mod_cast h

/-- The explicit recursive family spans the full parent tableau space. -/
theorem S05_canonicalEvenEigenbasisVector_span
    (m : Nat) (lam : YoungDiagram (2 * m)) :
    Submodule.span Real
        (Set.range (S05_canonicalEvenEigenbasisVector m lam)) = ⊤ := by
  classical
  apply
    (S05_canonicalEvenEigenbasisVector_linearIndependent m lam).span_eq_top_of_card_eq_finrank'
  rw [S05_card_canonicalEvenEigenbasisIndex]
  exact (Module.finrank_pi Real :
      Module.finrank Real (StandardYoungTableau lam → Real) =
        Fintype.card (StandardYoungTableau lam)).symm

/-- Mathlib basis carried by the explicit recursive canonical-even family. -/
noncomputable def S05_canonicalEvenMatchingBasis
    (m : Nat) (lam : YoungDiagram (2 * m)) :
    Module.Basis (S05_CanonicalEvenEigenbasisIndex m lam) Real
      (TableauSpace lam) :=
  Module.Basis.mk (S05_canonicalEvenEigenbasisVector_linearIndependent m lam)
    (S05_canonicalEvenEigenbasisVector_span m lam).ge

@[simp] theorem S05_canonicalEvenMatchingBasis_apply
    (m : Nat) (lam : YoungDiagram (2 * m))
    (i : S05_CanonicalEvenEigenbasisIndex m lam) :
    S05_canonicalEvenMatchingBasis m lam i =
      S05_canonicalEvenEigenbasisVector m lam i := by
  exact Module.Basis.mk_apply _ _ _

/-- Earlier canonical matching edges are the twice-cast child edges. -/
theorem S05_canonicalMatchingAdjacentIndex_succ_castSucc
    (m : Nat) (r : Fin m) :
    canonicalMatchingAdjacentIndex (m + 1) r.castSucc =
      Fin.cast (by
        have hr := r.isLt
        omega)
        (Fin.castSucc (Fin.castSucc (canonicalMatchingAdjacentIndex m r))) := by
  apply Fin.ext
  simp [canonicalMatchingAdjacentIndex]

/-- The last canonical matching edge is the final adjacent generator. -/
theorem S05_canonicalMatchingAdjacentIndex_succ_last (m : Nat) :
    canonicalMatchingAdjacentIndex (m + 1) (Fin.last m) =
      Fin.last (2 * m) := by
  apply Fin.ext
  simp [canonicalMatchingAdjacentIndex]

@[simp] theorem S05_matchingEdgeSign_liftEvenSignPattern_castSucc
    {m : Nat} (R : Finset (Fin m)) (r : Fin m) :
    matchingEdgeSign (S05_liftEvenSignPattern R) r.castSucc =
      matchingEdgeSign R r := by
  simp [matchingEdgeSign, S05_liftEvenSignPattern]

@[simp] theorem S05_matchingEdgeSign_liftEvenSignPatternWithLast_castSucc
    {m : Nat} (R : Finset (Fin m)) (r : Fin m) :
    matchingEdgeSign (S05_liftEvenSignPatternWithLast R) r.castSucc =
      matchingEdgeSign R r := by
  simp [matchingEdgeSign, S05_liftEvenSignPatternWithLast,
    S05_liftEvenSignPattern]

@[simp] theorem S05_matchingEdgeSign_liftEvenSignPattern_last
    {m : Nat} (R : Finset (Fin m)) :
    matchingEdgeSign (S05_liftEvenSignPattern R) (Fin.last m) = 1 := by
  simp [matchingEdgeSign, S05_liftEvenSignPattern]

@[simp] theorem S05_matchingEdgeSign_liftEvenSignPatternWithLast_last
    {m : Nat} (R : Finset (Fin m)) :
    matchingEdgeSign (S05_liftEvenSignPatternWithLast R) (Fin.last m) = -1 := by
  simp [matchingEdgeSign, S05_liftEvenSignPatternWithLast]

/-- The signed-child final eigenvalue is exactly the character sign prescribed
by the recursively lifted label. -/
theorem S05_signedTwoBoxRemovalSign_eq_matchingEdgeSign_label
    {m : Nat} {lam : YoungDiagram (2 * (m + 1))}
    (p : TwoStepRemovableRows lam) (R : Finset (Fin m)) :
    S05_signedTwoBoxRemovalSign p =
      matchingEdgeSign
        (if p.first.1 <= p.second.1 then
          S05_liftEvenSignPattern R
        else
          S05_liftEvenSignPatternWithLast R)
        (Fin.last m) := by
  by_cases hpos : p.first.1 <= p.second.1 <;>
    simp [S05_signedTwoBoxRemovalSign, hpos]

/-- The final canonical perfect-matching operator is the final adjacent
operator from the signed-child decomposition. -/
theorem S05_signedTwoBoxChildEmbedding_finalCanonicalOperator
    {m : Nat} (lam : YoungDiagram (2 * (m + 1)))
    (p : TwoStepRemovableRows lam)
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    canonicalMatchingYoungOperatorEven (Fin.last m)
        (S05_signedTwoBoxChildEmbedding lam p f) =
      S05_signedTwoBoxRemovalSign p •
        S05_signedTwoBoxChildEmbedding lam p f := by
  unfold canonicalMatchingYoungOperatorEven
  rw [S05_canonicalMatchingAdjacentIndex_succ_last]
  convert S05_signedTwoBoxChildEmbedding_finalOperator lam p f using 1 <;> rfl

/-- Every earlier canonical perfect-matching edge is transported from the
child by the signed two-box embedding. -/
theorem S05_signedTwoBoxChildEmbedding_intertwinesEarlierCanonical
    {m : Nat} (lam : YoungDiagram (2 * ((m + 1) + 1)))
    (p : TwoStepRemovableRows lam) (r : Fin (m + 1))
    (f : TableauSpace (deleteTwoRemovableRowsDiagram lam p)) :
    canonicalMatchingYoungOperatorEven r.castSucc
        (S05_signedTwoBoxChildEmbedding lam p f) =
      S05_signedTwoBoxChildEmbedding lam p
        (canonicalMatchingYoungOperatorEven r f) := by
  unfold canonicalMatchingYoungOperatorEven
  have h := S05_signedTwoBoxChildEmbedding_intertwinesEarlierAdjacent
    lam p (canonicalMatchingAdjacentIndex (m + 1) r) f
  have hbound :
      ((2 * (m + 1) - 1) + 1) + 1 =
        2 * ((m + 1) + 1) - 1 := by
    omega
  have hindex :
      canonicalMatchingAdjacentIndex ((m + 1) + 1) r.castSucc =
        Fin.cast hbound
          (Fin.castSucc
            (Fin.castSucc (canonicalMatchingAdjacentIndex (m + 1) r))) := by
    apply Fin.ext
    simp [canonicalMatchingAdjacentIndex]
  rw [hindex]
  cases hbound
  exact h

/-- Every vector in the recursively constructed positive-level basis is a
simultaneous eigenvector for the canonical perfect-matching edges, with the
recursively constructed label.  The theorem starts at one edge because the
auxiliary predicate's size expression is not the empty-diagram size at `m = 0`. -/
theorem S05_canonicalEvenEigenbasisVector_isMatchingEigenvector :
    ∀ (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
      (i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam),
      S05_IsMatchingEigenvectorEven
        (S05_canonicalEvenEigenbasisVector (m + 1) lam i)
        (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) := by
  intro m
  induction m with
  | zero =>
      intro lam i
      rcases i with ⟨p, i⟩
      intro r
      refine Fin.lastCases ?_ (fun r => Fin.elim0 r) r
      let childVector :=
        S05_canonicalEvenEigenbasisVector 0
          (deleteTwoRemovableRowsDiagram lam p) i
      let childLabel :=
        S05_canonicalEvenEigenbasisLabel 0
          (deleteTwoRemovableRowsDiagram lam p) i
      change
        canonicalMatchingYoungOperatorEven (Fin.last 0)
            (S05_signedTwoBoxChildEmbedding lam p childVector) =
          matchingEdgeSign
              (if p.first.1 <= p.second.1 then
                S05_liftEvenSignPattern childLabel
              else
                S05_liftEvenSignPatternWithLast childLabel)
              (Fin.last 0) •
            S05_signedTwoBoxChildEmbedding lam p childVector
      rw [S05_signedTwoBoxChildEmbedding_finalCanonicalOperator,
        S05_signedTwoBoxRemovalSign_eq_matchingEdgeSign_label]
  | succ m ih =>
      intro lam i
      rcases i with ⟨p, i⟩
      intro r
      refine Fin.lastCases ?_ (fun r => ?_) r
      · let childVector :=
          S05_canonicalEvenEigenbasisVector (m + 1)
            (deleteTwoRemovableRowsDiagram lam p) i
        let childLabel :=
          S05_canonicalEvenEigenbasisLabel (m + 1)
            (deleteTwoRemovableRowsDiagram lam p) i
        change
          canonicalMatchingYoungOperatorEven (Fin.last (m + 1))
              (S05_signedTwoBoxChildEmbedding lam p childVector) =
            matchingEdgeSign
                (if p.first.1 <= p.second.1 then
                  S05_liftEvenSignPattern childLabel
                else
                  S05_liftEvenSignPatternWithLast childLabel)
                (Fin.last (m + 1)) •
              S05_signedTwoBoxChildEmbedding lam p childVector
        rw [S05_signedTwoBoxChildEmbedding_finalCanonicalOperator,
          S05_signedTwoBoxRemovalSign_eq_matchingEdgeSign_label]
      · let childVector :=
          S05_canonicalEvenEigenbasisVector (m + 1)
            (deleteTwoRemovableRowsDiagram lam p) i
        let childLabel :=
          S05_canonicalEvenEigenbasisLabel (m + 1)
            (deleteTwoRemovableRowsDiagram lam p) i
        change
          canonicalMatchingYoungOperatorEven r.castSucc
              (S05_signedTwoBoxChildEmbedding lam p childVector) =
            matchingEdgeSign
                (if p.first.1 <= p.second.1 then
                  S05_liftEvenSignPattern childLabel
                else
                  S05_liftEvenSignPatternWithLast childLabel)
                r.castSucc •
              S05_signedTwoBoxChildEmbedding lam p childVector
        calc
          canonicalMatchingYoungOperatorEven r.castSucc
              (S05_signedTwoBoxChildEmbedding lam p childVector) =
              S05_signedTwoBoxChildEmbedding lam p
                (canonicalMatchingYoungOperatorEven r childVector) := by
            exact S05_signedTwoBoxChildEmbedding_intertwinesEarlierCanonical
              lam p r childVector
          _ = S05_signedTwoBoxChildEmbedding lam p
                (matchingEdgeSign childLabel r • childVector) := by
            convert congrArg
              (S05_signedTwoBoxChildEmbedding lam p)
              (ih (deleteTwoRemovableRowsDiagram lam p) i r) using 1
            all_goals rfl
          _ = matchingEdgeSign childLabel r •
                S05_signedTwoBoxChildEmbedding lam p childVector := by
            exact S05_signedTwoBoxChildEmbedding_smul lam p _ childVector
          _ = matchingEdgeSign
                (if p.first.1 <= p.second.1 then
                  S05_liftEvenSignPattern childLabel
                else
                  S05_liftEvenSignPatternWithLast childLabel)
                r.castSucc •
              S05_signedTwoBoxChildEmbedding lam p childVector := by
            by_cases hpos : p.first.1 <= p.second.1 <;> simp [hpos]

/-- Canonical even labeled eigenbasis theorem.  The named recursive index is
finite, `S05_canonicalEvenMatchingBasis` is an actual Mathlib basis, every
basis vector has its simultaneous canonical matching label, and enumerating
those labels gives Definition 5.10 with exact multiplicity. -/
theorem S05_Lem5_16_canonicalEvenMatchingEigenbasis
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    (∀ i j : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      tableauInner
          (S05_canonicalEvenMatchingBasis (m + 1) lam i)
          (S05_canonicalEvenMatchingBasis (m + 1) lam j) =
        if i = j then 1 else 0) ∧
    (∀ i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      S05_IsMatchingEigenvectorEven
        (S05_canonicalEvenMatchingBasis (m + 1) lam i)
        (S05_canonicalEvenEigenbasisLabel (m + 1) lam i)) ∧
    (Finset.univ : Finset
        (S05_CanonicalEvenEigenbasisIndex (m + 1) lam)).1.map
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam) =
      S05_evenSignPatternMultiset (m + 1) lam := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [S05_canonicalEvenMatchingBasis_apply,
      S05_canonicalEvenMatchingBasis_apply]
    exact S05_canonicalEvenEigenbasisVector_inner (m + 1) lam i j
  · intro i
    rw [S05_canonicalEvenMatchingBasis_apply]
    exact S05_canonicalEvenEigenbasisVector_isMatchingEigenvector m lam i
  · exact S05_canonicalEvenEigenbasisLabelMultiset_eq (m + 1) lam

/-- The canonical matching cube acts on each recursive basis vector by the
character attached to its exact recursive label. -/
theorem S05_canonicalEvenMatchingBasis_character_action
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam) (x : Cube (m + 1)) :
    canonicalMatchingCubeOperatorEven x
        (S05_canonicalEvenMatchingBasis (m + 1) lam i) =
      S05_matchingCharacter
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x •
        S05_canonicalEvenMatchingBasis (m + 1) lam i := by
  exact canonicalMatchingCubeOperatorEven_apply_character_of_isMatchingEigenvector
    ((S05_Lem5_16_canonicalEvenMatchingEigenbasis m lam).2.1 i) x

/-! ## Canonical odd eigenbasis from one-box fibers -/

/-- Insert the maximum entry into the removable corner indexed by `r`. -/
noncomputable def S05_oneBoxExtensionTableau
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (U : StandardYoungTableau (removableRowToOneBoxChild lam r)) :
    StandardYoungTableau lam :=
  S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
    (removableRowToOneBoxChild_isOneBoxChild lam r)
    (row_form_deleteRemovableRowDiagram lam r.2) U

/-- The inserted tableau lies in exactly the removable-row fiber used for the
insertion. -/
theorem S05_oneBoxExtensionTableau_maxRemovableRow
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (U : StandardYoungTableau (removableRowToOneBoxChild lam r)) :
    maxRemovableRow (S05_oneBoxExtensionTableau lam r U) = r := by
  apply maxRemovableRow_eq_of_tableauMaxAt_deletedCorner r
  exact S05_oneBoxDeletion_insertMax_tableauMaxAt_deletedCorner
    (removableRowToOneBoxChild_isOneBoxChild lam r)
    (row_form_deleteRemovableRowDiagram lam r.2) U

/-- Insertion at a fixed removable row is injective on child tableaux. -/
theorem S05_oneBoxExtensionTableau_injective
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    Function.Injective (S05_oneBoxExtensionTableau lam r) := by
  intro U V hUV
  exact S05_oneBoxIntertwining_insertMax_injective
    (removableRowToOneBoxChild_isOneBoxChild lam r)
    (row_form_deleteRemovableRowDiagram lam r.2) hUV

/-- Extend child tableau coordinates by zero outside the removable-row fiber.
The formula is explicit in the parent tableau basis. -/
noncomputable def S05_oneBoxExtensionEmbedding
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    TableauSpace (removableRowToOneBoxChild lam r) -> TableauSpace lam :=
  fun f T =>
    ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
      f U * tableauBasisVec (S05_oneBoxExtensionTableau lam r U) T

/-- A child basis vector extends to the corresponding inserted parent basis
vector. -/
theorem S05_oneBoxExtensionEmbedding_basis
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (U : StandardYoungTableau (removableRowToOneBoxChild lam r)) :
    S05_oneBoxExtensionEmbedding lam r (tableauBasisVec U) =
      tableauBasisVec (S05_oneBoxExtensionTableau lam r U) := by
  classical
  funext T
  rw [S05_oneBoxExtensionEmbedding]
  rw [Fintype.sum_eq_single U]
  · simp [tableauBasisVec]
  · intro V hVU
    simp [tableauBasisVec, hVU]

/-- Reading an extended coordinate at its inserted tableau recovers the child
coordinate. -/
theorem S05_oneBoxExtensionEmbedding_apply_extension
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (f : TableauSpace (removableRowToOneBoxChild lam r))
    (U : StandardYoungTableau (removableRowToOneBoxChild lam r)) :
    S05_oneBoxExtensionEmbedding lam r f
        (S05_oneBoxExtensionTableau lam r U) = f U := by
  classical
  rw [S05_oneBoxExtensionEmbedding]
  rw [Fintype.sum_eq_single U]
  · simp [tableauBasisVec]
  · intro V hVU
    have hExt :
        S05_oneBoxExtensionTableau lam r V ≠
          S05_oneBoxExtensionTableau lam r U := by
      intro h
      exact hVU (S05_oneBoxExtensionTableau_injective lam r h)
    rw [tableauBasisVec_ne (Ne.symm hExt)]
    ring

/-- The extension is zero on every other removable-row fiber. -/
theorem S05_oneBoxExtensionEmbedding_apply_of_maxRemovableRow_ne
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (f : TableauSpace (removableRowToOneBoxChild lam r))
    (T : StandardYoungTableau lam) (hT : maxRemovableRow T ≠ r) :
    S05_oneBoxExtensionEmbedding lam r f T = 0 := by
  classical
  rw [S05_oneBoxExtensionEmbedding]
  apply Finset.sum_eq_zero
  intro U _hU
  have hne : T ≠ S05_oneBoxExtensionTableau lam r U := by
    intro h
    apply hT
    rw [h, S05_oneBoxExtensionTableau_maxRemovableRow]
  rw [tableauBasisVec_ne hne]
  ring

/-- One-box extension preserves the full coordinate inner product. -/
theorem S05_oneBoxExtensionEmbedding_isometry
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (f g : TableauSpace (removableRowToOneBoxChild lam r)) :
    tableauInner (S05_oneBoxExtensionEmbedding lam r f)
        (S05_oneBoxExtensionEmbedding lam r g) = tableauInner f g := by
  classical
  rw [tableauInner, tableauInner]
  change
    (∑ T : StandardYoungTableau lam,
      S05_oneBoxExtensionEmbedding lam r f T *
        (∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
          g U * tableauBasisVec (S05_oneBoxExtensionTableau lam r U) T)) =
      ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
        f U * g U
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _hU
  have hright :
      (∑ T : StandardYoungTableau lam,
        S05_oneBoxExtensionEmbedding lam r f T *
          tableauBasisVec (S05_oneBoxExtensionTableau lam r U) T) =
        S05_oneBoxExtensionEmbedding lam r f
          (S05_oneBoxExtensionTableau lam r U) := by
    simpa [tableauInner] using tableauInner_right_basis
      (S05_oneBoxExtensionEmbedding lam r f)
      (S05_oneBoxExtensionTableau lam r U)
  calc
    (∑ T : StandardYoungTableau lam,
        S05_oneBoxExtensionEmbedding lam r f T *
          (g U * tableauBasisVec (S05_oneBoxExtensionTableau lam r U) T)) =
        g U * ∑ T : StandardYoungTableau lam,
          S05_oneBoxExtensionEmbedding lam r f T *
            tableauBasisVec (S05_oneBoxExtensionTableau lam r U) T := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _hT
      ring
    _ = g U * S05_oneBoxExtensionEmbedding lam r f
          (S05_oneBoxExtensionTableau lam r U) := by rw [hright]
    _ = f U * g U := by
      rw [S05_oneBoxExtensionEmbedding_apply_extension]
      ring

/-- Extensions from distinct removable-row fibers are orthogonal. -/
theorem S05_oneBoxExtensionEmbedding_ranges_orthogonal
    {n : Nat} (lam : YoungDiagram (n + 1))
    {r s : RemovableRow lam} (hrs : r ≠ s)
    (f : TableauSpace (removableRowToOneBoxChild lam r))
    (g : TableauSpace (removableRowToOneBoxChild lam s)) :
    tableauInner (S05_oneBoxExtensionEmbedding lam r f)
        (S05_oneBoxExtensionEmbedding lam s g) = 0 := by
  classical
  unfold tableauInner
  apply Finset.sum_eq_zero
  intro T _hT
  by_cases hTr : maxRemovableRow T = r
  · have hTs : maxRemovableRow T ≠ s := by
      intro h
      exact hrs (hTr.symm.trans h)
    rw [S05_oneBoxExtensionEmbedding_apply_of_maxRemovableRow_ne
      lam s g T hTs]
    ring
  · rw [S05_oneBoxExtensionEmbedding_apply_of_maxRemovableRow_ne
      lam r f T hTr]
    ring

/-- One-box extension is additive. -/
theorem S05_oneBoxExtensionEmbedding_add
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (f g : TableauSpace (removableRowToOneBoxChild lam r)) :
    S05_oneBoxExtensionEmbedding lam r (f + g) =
      S05_oneBoxExtensionEmbedding lam r f +
        S05_oneBoxExtensionEmbedding lam r g := by
  classical
  funext T
  simp only [S05_oneBoxExtensionEmbedding, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- One-box extension commutes with real scalar multiplication. -/
theorem S05_oneBoxExtensionEmbedding_smul
    {n : Nat} (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (c : Real) (f : TableauSpace (removableRowToOneBoxChild lam r)) :
    S05_oneBoxExtensionEmbedding lam r (c • f) =
      c • S05_oneBoxExtensionEmbedding lam r f := by
  classical
  funext T
  simp only [S05_oneBoxExtensionEmbedding, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _hU
  ring

/-- One-box extension commutes with finite coordinate sums. -/
theorem S05_oneBoxExtensionEmbedding_sum
    {n : Nat} {ι : Type} [Fintype ι]
    (lam : YoungDiagram (n + 1)) (r : RemovableRow lam)
    (f : ι -> TableauSpace (removableRowToOneBoxChild lam r)) :
    S05_oneBoxExtensionEmbedding lam r (fun U => ∑ i : ι, f i U) =
      fun T => ∑ i : ι, S05_oneBoxExtensionEmbedding lam r (f i) T := by
  classical
  funext T
  simp only [S05_oneBoxExtensionEmbedding]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Basis-level intertwining for every adjacent pair retained by one-box
deletion. -/
theorem S05_oneBoxExtensionEmbedding_intertwinesEarlierAdjacent_basis
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (r : RemovableRow lam)
    (U : StandardYoungTableau (removableRowToOneBoxChild lam r))
    (a : Fin n) :
    youngAdjacentOperator (Fin.castSucc a)
        (S05_oneBoxExtensionEmbedding lam r (tableauBasisVec U)) =
      S05_oneBoxExtensionEmbedding lam r
        (youngAdjacentOperator a (tableauBasisVec U)) := by
  let TU := S05_oneBoxExtensionTableau lam r U
  let h := removableRowToOneBoxChild_isOneBoxChild lam r
  let hr := row_form_deleteRemovableRowDiagram lam r.2
  rw [S05_oneBoxExtensionEmbedding_basis]
  by_cases hrow : adjacentSameRow U a
  · have hrowP : adjacentSameRow TU (Fin.castSucc a) := by
      exact (S05_oneBoxIntertwining_insertMax_adjacentSameRow_iff h hr U a).2 hrow
    rw [youngAdjacentOperator_basis_sameRow TU _ hrowP,
      youngAdjacentOperator_basis_sameRow U a hrow,
      S05_oneBoxExtensionEmbedding_basis]
  · by_cases hcol : adjacentSameCol U a
    · have hcolP : adjacentSameCol TU (Fin.castSucc a) := by
        exact (S05_oneBoxIntertwining_insertMax_adjacentSameCol_iff h hr U a).2 hcol
      rw [youngAdjacentOperator_basis_sameCol TU _ hcolP,
        youngAdjacentOperator_basis_sameCol U a hcol]
      have hnegP : (fun S => -tableauBasisVec TU S) =
          (-1 : Real) • tableauBasisVec TU := by
        funext S
        simp
      have hnegC : (fun S => -tableauBasisVec U S) =
          (-1 : Real) • tableauBasisVec U := by
        funext S
        simp
      rw [hnegP, hnegC, S05_oneBoxExtensionEmbedding_smul,
        S05_oneBoxExtensionEmbedding_basis]
    · have hrowP : ¬ adjacentSameRow TU (Fin.castSucc a) := by
        intro hp
        exact hrow ((S05_oneBoxIntertwining_insertMax_adjacentSameRow_iff h hr U a).1 hp)
      have hcolP : ¬ adjacentSameCol TU (Fin.castSucc a) := by
        intro hp
        exact hcol ((S05_oneBoxIntertwining_insertMax_adjacentSameCol_iff h hr U a).1 hp)
      let U' := adjacentSwapTableau U a hrow hcol
      have hswap :
          S05_oneBoxExtensionTableau lam r U' =
            adjacentSwapTableau TU (Fin.castSucc a) hrowP hcolP := by
        simpa [TU, U', h, hr, S05_oneBoxExtensionTableau] using
          S05_oneBoxIntertwining_insertMax_adjacentSwapTableau h hr U a hrow hcol
      rw [youngAdjacentOperator_basis_swappable_eq TU _ hrowP hcolP,
        youngAdjacentOperator_basis_swappable_eq U a hrow hcol]
      have hchild :
          (fun S => youngAdjacentDiagCoeff U a * tableauBasisVec U S +
            youngAdjacentOffCoeff U a * tableauBasisVec U' S) =
          youngAdjacentDiagCoeff U a • tableauBasisVec U +
            youngAdjacentOffCoeff U a • tableauBasisVec U' := by
        rfl
      rw [hchild, S05_oneBoxExtensionEmbedding_add,
        S05_oneBoxExtensionEmbedding_smul,
        S05_oneBoxExtensionEmbedding_smul,
        S05_oneBoxExtensionEmbedding_basis,
        S05_oneBoxExtensionEmbedding_basis]
      funext S
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hdiag :
          youngAdjacentDiagCoeff TU (Fin.castSucc a) =
            youngAdjacentDiagCoeff U a := by
        simpa [TU, S05_oneBoxExtensionTableau] using
          (S05_oneBoxIntertwining_insertMax_youngAdjacentDiagCoeff h hr U a).symm
      have hoff :
          youngAdjacentOffCoeff TU (Fin.castSucc a) =
            youngAdjacentOffCoeff U a := by
        simpa [TU, S05_oneBoxExtensionTableau] using
          (S05_oneBoxIntertwining_insertMax_youngAdjacentOffCoeff h hr U a).symm
      rw [hdiag, hoff, ← hswap]

/-- One-box extension intertwines every adjacent operator that acts before the
new maximum entry. -/
theorem S05_oneBoxExtensionEmbedding_intertwinesEarlierAdjacent
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (r : RemovableRow lam) (a : Fin n)
    (f : TableauSpace (removableRowToOneBoxChild lam r)) :
    youngAdjacentOperator (Fin.castSucc a)
        (S05_oneBoxExtensionEmbedding lam r f) =
      S05_oneBoxExtensionEmbedding lam r (youngAdjacentOperator a f) := by
  classical
  have hf := tableauBasis_expansion f
  calc
    youngAdjacentOperator (Fin.castSucc a)
        (S05_oneBoxExtensionEmbedding lam r f) =
      youngAdjacentOperator (Fin.castSucc a)
        (S05_oneBoxExtensionEmbedding lam r
          (fun S =>
            ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
              f U * tableauBasisVec U S)) := by
        exact congrArg
          (fun g => youngAdjacentOperator (Fin.castSucc a)
            (S05_oneBoxExtensionEmbedding lam r g)) hf
    _ = youngAdjacentOperator (Fin.castSucc a)
        (fun T =>
          ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
            S05_oneBoxExtensionEmbedding lam r
              (fun S => f U * tableauBasisVec U S) T) := by
        rw [S05_oneBoxExtensionEmbedding_sum]
    _ = fun T =>
        ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
          youngAdjacentOperator (Fin.castSucc a)
            (S05_oneBoxExtensionEmbedding lam r
              (fun S => f U * tableauBasisVec U S)) T := by
        rw [youngAdjacentOperator_sum]
    _ = fun T =>
        ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
          S05_oneBoxExtensionEmbedding lam r
            (youngAdjacentOperator a
              (fun S => f U * tableauBasisVec U S)) T := by
        funext T
        apply Finset.sum_congr rfl
        intro U _hU
        have hembed :
            S05_oneBoxExtensionEmbedding lam r
                (fun S => f U * tableauBasisVec U S) =
              fun T => f U * S05_oneBoxExtensionEmbedding lam r
                (tableauBasisVec U) T := by
          funext V
          simp only [S05_oneBoxExtensionEmbedding]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro W _hW
          ring
        have hembedOp :
            S05_oneBoxExtensionEmbedding lam r
                (fun S => f U * youngAdjacentOperator a (tableauBasisVec U) S) =
              fun T => f U * S05_oneBoxExtensionEmbedding lam r
                (youngAdjacentOperator a (tableauBasisVec U)) T := by
          funext V
          simp only [S05_oneBoxExtensionEmbedding]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro W _hW
          ring
        have hparentSmul := youngAdjacentOperator_smul (Fin.castSucc a) (f U)
          (S05_oneBoxExtensionEmbedding lam r (tableauBasisVec U))
        have hchildSmul := youngAdjacentOperator_smul a (f U)
          (tableauBasisVec U)
        have hscaled :
            youngAdjacentOperator (Fin.castSucc a)
                (S05_oneBoxExtensionEmbedding lam r
                  (fun S => f U * tableauBasisVec U S)) =
              S05_oneBoxExtensionEmbedding lam r
                (youngAdjacentOperator a
                  (fun S => f U * tableauBasisVec U S)) := by
          calc
            youngAdjacentOperator (Fin.castSucc a)
                (S05_oneBoxExtensionEmbedding lam r
                  (fun S => f U * tableauBasisVec U S)) =
              youngAdjacentOperator (Fin.castSucc a)
                (fun T => f U * S05_oneBoxExtensionEmbedding lam r
                  (tableauBasisVec U) T) := congrArg _ hembed
            _ = fun T => f U * youngAdjacentOperator (Fin.castSucc a)
                  (S05_oneBoxExtensionEmbedding lam r (tableauBasisVec U)) T :=
              hparentSmul
            _ = fun T => f U * S05_oneBoxExtensionEmbedding lam r
                (youngAdjacentOperator a (tableauBasisVec U)) T := by
              rw [S05_oneBoxExtensionEmbedding_intertwinesEarlierAdjacent_basis]
            _ = S05_oneBoxExtensionEmbedding lam r
                (fun S => f U * youngAdjacentOperator a (tableauBasisVec U) S) :=
              hembedOp.symm
            _ = S05_oneBoxExtensionEmbedding lam r
                (youngAdjacentOperator a
                  (fun S => f U * tableauBasisVec U S)) := by
              exact congrArg (S05_oneBoxExtensionEmbedding lam r)
                hchildSmul.symm
        exact congrFun hscaled T
    _ = S05_oneBoxExtensionEmbedding lam r
        (fun S =>
          ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
            youngAdjacentOperator a
              (fun R => f U * tableauBasisVec U R) S) := by
        rw [S05_oneBoxExtensionEmbedding_sum]
    _ = S05_oneBoxExtensionEmbedding lam r
        (youngAdjacentOperator a
          (fun S =>
            ∑ U : StandardYoungTableau (removableRowToOneBoxChild lam r),
              f U * tableauBasisVec U S)) := by
        rw [youngAdjacentOperator_sum]
    _ = S05_oneBoxExtensionEmbedding lam r
        (youngAdjacentOperator a f) := by
      exact congrArg (S05_oneBoxExtensionEmbedding lam r)
        (congrArg (youngAdjacentOperator a) hf).symm

/-- Sigma index for the canonical odd eigenbasis.  The outer coordinate is a
removable-corner occurrence, so multiplicities are retained exactly. -/
def S05_CanonicalOddEigenbasisIndex
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) : Type :=
  Sigma fun r : RemovableRow lam =>
    S05_CanonicalEvenEigenbasisIndex m
      (removableRowToOneBoxChild lam r)

noncomputable instance S05_canonicalOddEigenbasisIndexFintype
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Fintype (S05_CanonicalOddEigenbasisIndex m lam) := by
  unfold S05_CanonicalOddEigenbasisIndex
  infer_instance

noncomputable instance S05_canonicalOddEigenbasisIndexDecidableEq
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    DecidableEq (S05_CanonicalOddEigenbasisIndex m lam) :=
  Classical.decEq _

/-- Explicit odd vector obtained by extending a canonical even child vector
into its parent removable-row fiber. -/
noncomputable def S05_canonicalOddEigenbasisVector
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) : TableauSpace lam :=
  S05_oneBoxExtensionEmbedding lam i.1
    (S05_canonicalEvenEigenbasisVector m
      (removableRowToOneBoxChild lam i.1) i.2)

/-- The odd label is exactly the canonical even label of the selected child;
the unmatched maximum contributes no matching coordinate. -/
def S05_canonicalOddEigenbasisLabel
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) : Finset (Fin m) :=
  S05_canonicalEvenEigenbasisLabel m
    (removableRowToOneBoxChild lam i.1) i.2

/-- Literal multiset of labels obtained by enumerating the odd sigma index. -/
noncomputable def S05_canonicalOddEigenbasisLabelMultiset
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Multiset (Finset (Fin m)) :=
  (Finset.univ : Finset (S05_CanonicalOddEigenbasisIndex m lam)).1.map
    (S05_canonicalOddEigenbasisLabel m lam)

/-- Expanding the sigma index expresses the odd label multiset as the sum of
the exact canonical-even child label multisets. -/
theorem S05_canonicalOddEigenbasisLabelMultiset_eq_sum_removableRows
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_canonicalOddEigenbasisLabelMultiset m lam =
      ∑ r : RemovableRow lam,
        S05_canonicalEvenEigenbasisLabelMultiset m
          (removableRowToOneBoxChild lam r) := by
  classical
  change
    ((Finset.univ : Finset (RemovableRow lam)).1.sigma
      (fun r =>
        (Finset.univ : Finset
          (S05_CanonicalEvenEigenbasisIndex m
            (removableRowToOneBoxChild lam r))).1)).map
      (fun x => S05_canonicalEvenEigenbasisLabel m
        (removableRowToOneBoxChild lam x.1) x.2) = _
  rw [S05_multiset_map_sigma_eq_sum_map]
  simp only [S05_canonicalEvenEigenbasisLabelMultiset]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r _hr
  rfl

/-- Summing any child value over removable rows is the same as summing it over
the paper's one-box-child finset. -/
theorem S05_sum_removableRows_eq_oneBoxChildrenOdd
    {α : Type*} [AddCommMonoid α]
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (f : YoungDiagram (2 * m) -> α) :
    (∑ r : RemovableRow lam, f (removableRowToOneBoxChild lam r)) =
      (oneBoxChildrenOdd m lam).sum f := by
  classical
  have hsum_subtype :
      (∑ mu : {mu : YoungDiagram (2 * m) //
          mu ∈ oneBoxChildrenSized lam}, f mu.1) =
        (oneBoxChildrenSized lam).sum f := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (oneBoxChildrenSized lam) f
  calc
    (∑ r : RemovableRow lam, f (removableRowToOneBoxChild lam r)) =
        ∑ mu : {mu : YoungDiagram (2 * m) //
          mu ∈ oneBoxChildrenSized lam}, f mu.1 := by
      exact Fintype.sum_equiv
        (removableRowsEquivOneBoxChildren lam)
        (fun r : RemovableRow lam => f (removableRowToOneBoxChild lam r))
        (fun mu : {mu : YoungDiagram (2 * m) //
          mu ∈ oneBoxChildrenSized lam} => f mu.1)
        (fun _ => rfl)
    _ = (oneBoxChildrenSized lam).sum f := hsum_subtype
    _ = (oneBoxChildrenOdd m lam).sum f := by
      rw [oneBoxChildrenSized_eq_oneBoxChildrenOdd]

/-- The explicit odd labels reproduce Definition 5.10 with literal multiset
equality, including every removable-corner occurrence. -/
theorem S05_canonicalOddEigenbasisLabelMultiset_eq
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_canonicalOddEigenbasisLabelMultiset m lam =
      S05_oddSignPatternMultiset m lam := by
  rw [S05_canonicalOddEigenbasisLabelMultiset_eq_sum_removableRows]
  simp_rw [S05_canonicalEvenEigenbasisLabelMultiset_eq]
  exact S05_sum_removableRows_eq_oneBoxChildrenOdd m lam
    (fun mu => S05_evenSignPatternMultiset m mu)

/-- The recursively assembled canonical odd family is orthonormal. -/
theorem S05_canonicalOddEigenbasisVector_inner
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (i j : S05_CanonicalOddEigenbasisIndex m lam) :
    tableauInner (S05_canonicalOddEigenbasisVector m lam i)
        (S05_canonicalOddEigenbasisVector m lam j) =
      if i = j then 1 else 0 := by
  classical
  rcases i with ⟨r, i⟩
  rcases j with ⟨s, j⟩
  by_cases hrs : r = s
  · subst s
    rw [S05_canonicalOddEigenbasisVector,
      S05_canonicalOddEigenbasisVector,
      S05_oneBoxExtensionEmbedding_isometry,
      S05_canonicalEvenEigenbasisVector_inner]
    by_cases hij : i = j
    · subst j
      simp
    · rw [if_neg hij, if_neg]
      intro h
      exact hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · rw [S05_canonicalOddEigenbasisVector,
      S05_canonicalOddEigenbasisVector,
      S05_oneBoxExtensionEmbedding_ranges_orthogonal lam hrs,
      if_neg]
    intro h
    exact hrs (congrArg Sigma.fst h)

/-- The odd recursive index has exactly the cardinality of the parent tableau
coordinate basis. -/
theorem S05_card_canonicalOddEigenbasisIndex
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Fintype.card (S05_CanonicalOddEigenbasisIndex m lam) =
      Fintype.card (StandardYoungTableau lam) := by
  classical
  change
    Fintype.card (Sigma fun r : RemovableRow lam =>
      S05_CanonicalEvenEigenbasisIndex m
        (removableRowToOneBoxChild lam r)) = _
  rw [Fintype.card_sigma,
    card_standardYoungTableau_eq_sum_removableRow_children lam]
  apply Finset.sum_congr rfl
  intro r _hr
  exact S05_card_canonicalEvenEigenbasisIndex m
    (removableRowToOneBoxChild lam r)

/-- The canonical odd family is linearly independent. -/
theorem S05_canonicalOddEigenbasisVector_linearIndependent
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    LinearIndependent Real (S05_canonicalOddEigenbasisVector m lam) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  have hinner := congrArg
    (fun f => tableauInner f (S05_canonicalOddEigenbasisVector m lam x)) hc
  have hcomb :
      (∑ i : S05_CanonicalOddEigenbasisIndex m lam,
          c i • S05_canonicalOddEigenbasisVector m lam i) =
        fun T => ∑ i : S05_CanonicalOddEigenbasisIndex m lam,
          c i * S05_canonicalOddEigenbasisVector m lam i T := by
    funext T
    simp
  rw [hcomb] at hinner
  rw [S05_tableauInner_sum_left] at hinner
  simp_rw [S05_tableauInner_mul_left,
    S05_canonicalOddEigenbasisVector_inner] at hinner
  simpa [tableauInner] using hinner

/-- The canonical odd family spans the full parent tableau space. -/
theorem S05_canonicalOddEigenbasisVector_span
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Submodule.span Real
        (Set.range (S05_canonicalOddEigenbasisVector m lam)) = ⊤ := by
  classical
  apply
    (S05_canonicalOddEigenbasisVector_linearIndependent m lam).span_eq_top_of_card_eq_finrank'
  rw [S05_card_canonicalOddEigenbasisIndex]
  exact (Module.finrank_pi Real :
    Module.finrank Real (StandardYoungTableau lam -> Real) =
      Fintype.card (StandardYoungTableau lam)).symm

/-- Mathlib basis carried by the explicit one-box-assembled odd family. -/
noncomputable def S05_canonicalOddMatchingBasis
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    Module.Basis (S05_CanonicalOddEigenbasisIndex m lam) Real
      (TableauSpace lam) :=
  Module.Basis.mk (S05_canonicalOddEigenbasisVector_linearIndependent m lam)
    (S05_canonicalOddEigenbasisVector_span m lam).ge

@[simp] theorem S05_canonicalOddMatchingBasis_apply
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) :
    S05_canonicalOddMatchingBasis m lam i =
      S05_canonicalOddEigenbasisVector m lam i := by
  exact Module.Basis.mk_apply _ _ _

/-- For positive matching size, a canonical odd matching edge is the cast of
the corresponding canonical even edge in every one-box child. -/
theorem S05_oneBoxExtensionEmbedding_intertwinesCanonicalMatching
    (m : Nat) (lam : YoungDiagram (2 * (m + 1) + 1))
    (r : RemovableRow lam) (a : Fin (m + 1))
    (f : TableauSpace (removableRowToOneBoxChild lam r)) :
    canonicalMatchingYoungOperatorOdd a
        (S05_oneBoxExtensionEmbedding lam r f) =
      S05_oneBoxExtensionEmbedding lam r
        (canonicalMatchingYoungOperatorEven a f) := by
  unfold canonicalMatchingYoungOperatorOdd canonicalMatchingYoungOperatorEven
  have hindex :
      canonicalNearMatchingAdjacentIndex (m + 1) a =
        Fin.cast (by omega)
          (Fin.castSucc (canonicalMatchingAdjacentIndex (m + 1) a)) := by
    apply Fin.ext
    simp [canonicalNearMatchingAdjacentIndex, canonicalMatchingAdjacentIndex]
  rw [hindex]
  exact S05_oneBoxExtensionEmbedding_intertwinesEarlierAdjacent lam r
    (canonicalMatchingAdjacentIndex (m + 1) a) f

/-- Every explicit canonical odd basis vector is a simultaneous eigenvector
with the inherited even-child label. -/
theorem S05_canonicalOddEigenbasisVector_isMatchingEigenvector :
    ∀ (m : Nat) (lam : YoungDiagram (2 * m + 1))
      (i : S05_CanonicalOddEigenbasisIndex m lam),
      S05_IsMatchingEigenvectorOdd
        (S05_canonicalOddEigenbasisVector m lam i)
        (S05_canonicalOddEigenbasisLabel m lam i) := by
  intro m
  cases m with
  | zero =>
      intro lam i r
      exact Fin.elim0 r
  | succ m =>
      intro lam i
      rcases i with ⟨r, i⟩
      intro a
      change
        canonicalMatchingYoungOperatorOdd a
            (S05_oneBoxExtensionEmbedding lam r
              (S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i)) =
          matchingEdgeSign
              (S05_canonicalEvenEigenbasisLabel (m + 1)
                (removableRowToOneBoxChild lam r) i) a •
            S05_oneBoxExtensionEmbedding lam r
              (S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i)
      calc
        canonicalMatchingYoungOperatorOdd a
            (S05_oneBoxExtensionEmbedding lam r
              (S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i)) =
          S05_oneBoxExtensionEmbedding lam r
            (canonicalMatchingYoungOperatorEven a
              (S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i)) := by
            exact S05_oneBoxExtensionEmbedding_intertwinesCanonicalMatching
              m lam r a _
        _ = S05_oneBoxExtensionEmbedding lam r
            (matchingEdgeSign
                (S05_canonicalEvenEigenbasisLabel (m + 1)
                  (removableRowToOneBoxChild lam r) i) a •
              S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i) := by
            exact congrArg (S05_oneBoxExtensionEmbedding lam r)
              (S05_canonicalEvenEigenbasisVector_isMatchingEigenvector
                m (removableRowToOneBoxChild lam r) i a)
        _ = matchingEdgeSign
              (S05_canonicalEvenEigenbasisLabel (m + 1)
                (removableRowToOneBoxChild lam r) i) a •
            S05_oneBoxExtensionEmbedding lam r
              (S05_canonicalEvenEigenbasisVector (m + 1)
                (removableRowToOneBoxChild lam r) i) := by
            exact S05_oneBoxExtensionEmbedding_smul lam r _ _

/-- Canonical odd labeled eigenbasis theorem: an actual orthonormal spanning
basis, simultaneous matching-edge eigenvalues, and the literal Definition 5.10
label multiset. -/
theorem S05_Lem5_16_canonicalOddMatchingEigenbasis
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    (∀ i j : S05_CanonicalOddEigenbasisIndex m lam,
      tableauInner
          (S05_canonicalOddMatchingBasis m lam i)
          (S05_canonicalOddMatchingBasis m lam j) =
        if i = j then 1 else 0) ∧
    (Submodule.span Real
        (Set.range (S05_canonicalOddMatchingBasis m lam)) = ⊤) ∧
    (∀ i : S05_CanonicalOddEigenbasisIndex m lam,
      S05_IsMatchingEigenvectorOdd
        (S05_canonicalOddMatchingBasis m lam i)
        (S05_canonicalOddEigenbasisLabel m lam i)) ∧
    (Finset.univ : Finset
        (S05_CanonicalOddEigenbasisIndex m lam)).1.map
          (S05_canonicalOddEigenbasisLabel m lam) =
      S05_oddSignPatternMultiset m lam := by
  refine ⟨?_, (S05_canonicalOddMatchingBasis m lam).span_eq, ?_, ?_⟩
  · intro i j
    rw [S05_canonicalOddMatchingBasis_apply,
      S05_canonicalOddMatchingBasis_apply]
    exact S05_canonicalOddEigenbasisVector_inner m lam i j
  · intro i
    rw [S05_canonicalOddMatchingBasis_apply]
    exact S05_canonicalOddEigenbasisVector_isMatchingEigenvector m lam i
  · exact S05_canonicalOddEigenbasisLabelMultiset_eq m lam

/-- The canonical odd matching cube acts on each basis vector through the
character attached to its exact recursive label. -/
theorem S05_canonicalOddMatchingBasis_character_action
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd x
        (S05_canonicalOddMatchingBasis m lam i) =
      S05_matchingCharacter (S05_canonicalOddEigenbasisLabel m lam i) x •
        S05_canonicalOddMatchingBasis m lam i := by
  exact canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    ((S05_Lem5_16_canonicalOddMatchingEigenbasis m lam).2.2.1 i) x

/-! ## Transport from the canonical perfect matching -/

/-- The canonical endpoint encoding `(r,b) ↦ 2*r+b`. -/
def S05_canonicalMatchingEndpointEquiv (m : Nat) :
    Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

@[simp] theorem S05_canonicalMatchingEndpointEquiv_zero_val
    (m : Nat) (r : Fin m) :
    ((S05_canonicalMatchingEndpointEquiv m (r, 0) : Fin (2 * m)) : Nat) =
      2 * (r : Nat) := by
  simp [S05_canonicalMatchingEndpointEquiv, finProdFinEquiv]

@[simp] theorem S05_canonicalMatchingEndpointEquiv_one_val
    (m : Nat) (r : Fin m) :
    ((S05_canonicalMatchingEndpointEquiv m (r, 1) : Fin (2 * m)) : Nat) =
      2 * (r : Nat) + 1 := by
  simp [S05_canonicalMatchingEndpointEquiv, finProdFinEquiv]
  omega

/-- The canonical ordered perfect matching `(0,1),(2,3),...`. -/
noncomputable def S05_canonicalOrderedPerfectMatching (m : Nat) :
    OrderedMatching (Fin (2 * m)) where
  edgeCount := m
  left r := S05_canonicalMatchingEndpointEquiv m (r, 0)
  right r := S05_canonicalMatchingEndpointEquiv m (r, 1)
  left_ne_right r := by
    intro h
    have hp := (S05_canonicalMatchingEndpointEquiv m).injective h
    simpa using congrArg Prod.snd hp
  edges_disjoint := by
    intro r s hrs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hrs (congrArg Prod.fst
        ((S05_canonicalMatchingEndpointEquiv m).injective h))
    · intro h
      have hb := congrArg Prod.snd
        ((S05_canonicalMatchingEndpointEquiv m).injective h)
      simp at hb
    · intro h
      have hb := congrArg Prod.snd
        ((S05_canonicalMatchingEndpointEquiv m).injective h)
      simp at hb
    · intro h
      exact hrs (congrArg Prod.fst
        ((S05_canonicalMatchingEndpointEquiv m).injective h))

@[simp] theorem S05_canonicalOrderedPerfectMatching_edgeCount (m : Nat) :
    (S05_canonicalOrderedPerfectMatching m).edgeCount = m := by
  rfl

/-- Extensionality for ordered matchings, including the dependent edge index. -/
theorem S05_orderedMatching_ext
    {α : Type*} [DecidableEq α] (M N : OrderedMatching α)
    (hcount : M.edgeCount = N.edgeCount)
    (hleft : ∀ r : Fin M.edgeCount,
      M.left r = N.left (Fin.cast hcount r))
    (hright : ∀ r : Fin M.edgeCount,
      M.right r = N.right (Fin.cast hcount r)) :
    M = N := by
  cases M with
  | mk mc ml mr mlr med =>
      cases N with
      | mk nc nl nr nlr ned =>
          change mc = nc at hcount
          subst nc
          simp only [Fin.cast_refl] at hleft hright
          have hleft_fun : ml = nl := funext hleft
          have hright_fun : mr = nr := funext hright
          subst nl
          subst nr
          rfl

/-- The edge count of an even near-perfect matching is exactly half its
ambient cardinality. -/
theorem S05_evenMatching_edgeCount_eq
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    m = M.toOrdered.edgeCount := by
  simp [NearPerfectMatching.toOrdered]

/-- Reindex an even near-perfect matching by the literal edge type `Fin m`. -/
noncomputable def S05_evenOrderedMatching
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    OrderedMatching (Fin (2 * m)) where
  edgeCount := m
  left r := M.toOrdered.left (Fin.cast (S05_evenMatching_edgeCount_eq m M) r)
  right r := M.toOrdered.right (Fin.cast (S05_evenMatching_edgeCount_eq m M) r)
  left_ne_right r := M.toOrdered.left_ne_right _
  edges_disjoint := by
    intro r s hrs
    apply M.toOrdered.edges_disjoint
    intro h
    apply hrs
    exact Fin.cast_injective (S05_evenMatching_edgeCount_eq m M) h

/-- The reindexed matching is propositionally the original ordered matching. -/
theorem S05_evenOrderedMatching_eq_toOrdered
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    S05_evenOrderedMatching m M = M.toOrdered := by
  apply S05_orderedMatching_ext _ _ (S05_evenMatching_edgeCount_eq m M)
  · intro r
    rfl
  · intro r
    rfl

/-- Endpoint map of an even near-perfect matching, with an explicit side bit. -/
def S05_matchingEndpointMap
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    Fin m × Fin 2 → Fin (2 * m)
  | (r, b) => Fin.cases ((S05_evenOrderedMatching m M).left r)
      (fun _ => (S05_evenOrderedMatching m M).right r) b

@[simp] theorem S05_matchingEndpointMap_zero
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_matchingEndpointMap m M (r, 0) =
      (S05_evenOrderedMatching m M).left r := by
  rfl

@[simp] theorem S05_matchingEndpointMap_one
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_matchingEndpointMap m M (r, 1) =
      (S05_evenOrderedMatching m M).right r := by
  rfl

/-- Matching endpoint disjointness makes the endpoint map injective. -/
theorem S05_matchingEndpointMap_injective
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    Function.Injective (S05_matchingEndpointMap m M) := by
  intro x y h
  rcases x with ⟨r, b⟩
  rcases y with ⟨s, c⟩
  fin_cases b <;> fin_cases c
  · have hrs : r = s := by
      by_contra hne
      exact ((S05_evenOrderedMatching m M).edges_disjoint hne).1 h
    subst s
    rfl
  · by_cases hrs : r = s
    · subst s
      exact False.elim ((S05_evenOrderedMatching m M).left_ne_right r h)
    · exact False.elim
        (((S05_evenOrderedMatching m M).edges_disjoint hrs).2.1 h)
  · by_cases hrs : r = s
    · subst s
      exact False.elim ((S05_evenOrderedMatching m M).left_ne_right r h.symm)
    · exact False.elim
        (((S05_evenOrderedMatching m M).edges_disjoint hrs).2.2.1 h)
  · have hrs : r = s := by
      by_contra hne
      exact ((S05_evenOrderedMatching m M).edges_disjoint hne).2.2.2 h
    subst s
    rfl

/-- In the even case the injective endpoint map is surjective by cardinality. -/
theorem S05_matchingEndpointMap_bijective
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    Function.Bijective (S05_matchingEndpointMap m M) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨S05_matchingEndpointMap_injective m M, ?_⟩
  simp [Nat.mul_comm]

/-- Every vertex of an even near-perfect matching is a unique edge endpoint. -/
noncomputable def S05_matchingEndpointEquiv
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    Fin m × Fin 2 ≃ Fin (2 * m) :=
  Equiv.ofBijective (S05_matchingEndpointMap m M)
    (S05_matchingEndpointMap_bijective m M)

@[simp] theorem S05_matchingEndpointEquiv_zero
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_matchingEndpointEquiv m M (r, 0) =
      (S05_evenOrderedMatching m M).left r := by
  rfl

@[simp] theorem S05_matchingEndpointEquiv_one
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_matchingEndpointEquiv m M (r, 1) =
      (S05_evenOrderedMatching m M).right r := by
  rfl

/-- The explicit permutation sending canonical edge endpoints to the endpoints
of `M`, without changing the edge coordinate. -/
noncomputable def S05_perfectMatchingRelabeling
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    Perm (Fin (2 * m)) :=
  (S05_canonicalMatchingEndpointEquiv m).symm.trans
    (S05_matchingEndpointEquiv m M)

@[simp] theorem S05_perfectMatchingRelabeling_left
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_perfectMatchingRelabeling m M
        ((S05_canonicalOrderedPerfectMatching m).left r) =
      (S05_evenOrderedMatching m M).left r := by
  simp [S05_perfectMatchingRelabeling,
    S05_canonicalOrderedPerfectMatching]

@[simp] theorem S05_perfectMatchingRelabeling_right
    (m : Nat) (M : NearPerfectMatching (2 * m)) (r : Fin m) :
    S05_perfectMatchingRelabeling m M
        ((S05_canonicalOrderedPerfectMatching m).right r) =
      (S05_evenOrderedMatching m M).right r := by
  simp [S05_perfectMatchingRelabeling,
    S05_canonicalOrderedPerfectMatching]

/-- Relabeling the canonical matching gives the supplied even matching. -/
theorem S05_canonicalOrderedPerfectMatching_relabel
    (m : Nat) (M : NearPerfectMatching (2 * m)) :
    (S05_canonicalOrderedPerfectMatching m).relabel
        (S05_perfectMatchingRelabeling m M) =
      M.toOrdered := by
  rw [← S05_evenOrderedMatching_eq_toOrdered m M]
  refine S05_orderedMatching_ext
    ((S05_canonicalOrderedPerfectMatching m).relabel
      (S05_perfectMatchingRelabeling m M))
    (S05_evenOrderedMatching m M) rfl ?_ ?_
  · intro r
    exact S05_perfectMatchingRelabeling_left m M r
  · intro r
    exact S05_perfectMatchingRelabeling_right m M r

/-- The matching-cube element for the reindexed arbitrary matching is the
conjugate of the canonical matching-cube element. -/
theorem S05_evenOrderedMatching_tau_conjugate
    (m : Nat) (M : NearPerfectMatching (2 * m)) (x : Cube m) :
    (S05_evenOrderedMatching m M).tau x =
      S05_perfectMatchingRelabeling m M *
        (S05_canonicalOrderedPerfectMatching m).tau x *
          (S05_perfectMatchingRelabeling m M).symm := by
  have htau :
      (S05_evenOrderedMatching m M).tau x =
        ((S05_canonicalOrderedPerfectMatching m).relabel
          (S05_perfectMatchingRelabeling m M)).tau x := by
    unfold OrderedMatching.tau
    change
      (List.ofFn fun r : Fin m =>
        (S05_evenOrderedMatching m M).edgePerm x r).prod =
      (List.ofFn fun r : Fin m =>
        ((S05_canonicalOrderedPerfectMatching m).relabel
          (S05_perfectMatchingRelabeling m M)).edgePerm x r).prod
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext r
    unfold OrderedMatching.edgePerm
    by_cases hx : x r
    · simp only [hx, if_true]
      unfold OrderedMatching.edgeSwap OrderedMatching.relabel
      change
        pswap ((S05_evenOrderedMatching m M).left r)
            ((S05_evenOrderedMatching m M).right r) =
          pswap
            (S05_perfectMatchingRelabeling m M
              ((S05_canonicalOrderedPerfectMatching m).left r))
            (S05_perfectMatchingRelabeling m M
              ((S05_canonicalOrderedPerfectMatching m).right r))
      rw [S05_perfectMatchingRelabeling_left,
        S05_perfectMatchingRelabeling_right]
    · simp [hx]
  rw [htau]
  exact orderedMatching_tau_relabel
    (S05_perfectMatchingRelabeling m M)
    (S05_canonicalOrderedPerfectMatching m) x

/-- A represented list product acts by composing the represented factors in
the same order. -/
theorem GroupRepresentationActionData.rho_list_prod
    {G V : Type*} [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V) (l : List G) (v : V) :
    rep.rho l.prod v = composeOperatorList (l.map rep.rho) v := by
  induction l with
  | nil =>
      simp [composeOperatorList, rep.map_one]
  | cons g l ih =>
      simp only [List.prod_cons, List.map_cons, composeOperatorList]
      rw [rep.map_mul, ih]

/-- A canonical matching edge is the corresponding adjacent transposition,
written in the arithmetic normal form used by `YoungOrthogonalActionData`. -/
theorem S05_canonicalOrderedPerfectMatching_edgeSwap
    (m : Nat) (r : Fin (m + 1)) :
    (S05_canonicalOrderedPerfectMatching (m + 1)).edgeSwap r =
      s05_adjacentTransposition
        (Fin.cast (by omega : 2 * (m + 1) - 1 = 2 * m + 1)
          (canonicalMatchingAdjacentIndex (m + 1) r)) := by
  unfold OrderedMatching.edgeSwap s05_adjacentTransposition
    S05_canonicalOrderedPerfectMatching
  congr 1
  · apply Fin.ext
    simp [S05_canonicalMatchingEndpointEquiv, finProdFinEquiv,
      canonicalMatchingAdjacentIndex]
  · apply Fin.ext
    simp [S05_canonicalMatchingEndpointEquiv, finProdFinEquiv,
      canonicalMatchingAdjacentIndex]
    omega

/-- The representation of one selected canonical edge is the corresponding
concrete Young operator bit. -/
theorem S05_rho_canonicalMatchingEdgePerm_eq
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (x : Cube (m + 1)) (r : Fin (m + 1)) (f : TableauSpace lam) :
    action.rep.rho
        ((S05_canonicalOrderedPerfectMatching (m + 1)).edgePerm x r) f =
      canonicalMatchingYoungOperatorEvenBit x r f := by
  unfold OrderedMatching.edgePerm canonicalMatchingYoungOperatorEvenBit
  by_cases hx : x r
  · simp only [hx, if_true]
    rw [S05_canonicalOrderedPerfectMatching_edgeSwap]
    have hadj := action.rho_adjacent
      (Fin.cast (by omega : 2 * (m + 1) - 1 = 2 * m + 1)
        (canonicalMatchingAdjacentIndex (m + 1) r)) f
    rw [hadj]
    unfold canonicalMatchingYoungOperatorEven
    congr 1
  · simp only [hx]
    exact action.rep.map_one f

/-- The represented canonical matching-cube element is exactly the concrete
canonical matching-cube operator. -/
theorem S05_rho_canonicalMatchingTau_eq_canonicalMatchingCubeOperatorEven
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (x : Cube (m + 1)) (f : TableauSpace lam) :
    action.rep.rho
        ((S05_canonicalOrderedPerfectMatching (m + 1)).tau x) f =
      canonicalMatchingCubeOperatorEven x f := by
  unfold OrderedMatching.tau
  change action.rep.rho
      ((List.ofFn fun r : Fin (m + 1) =>
        (S05_canonicalOrderedPerfectMatching (m + 1)).edgePerm x r).prod) f = _
  rw [action.rep.rho_list_prod]
  have hlist :
      (List.ofFn fun r : Fin (m + 1) =>
          (S05_canonicalOrderedPerfectMatching (m + 1)).edgePerm x r).map
            action.rep.rho =
        List.ofFn (fun r : Fin (m + 1) =>
          canonicalMatchingYoungOperatorEvenBit x r) := by
    calc
      _ = List.ofFn (fun r : Fin (m + 1) =>
          action.rep.rho
            ((S05_canonicalOrderedPerfectMatching (m + 1)).edgePerm x r)) :=
        (List.ofFn_comp'
          (fun r : Fin (m + 1) =>
            (S05_canonicalOrderedPerfectMatching (m + 1)).edgePerm x r)
          action.rep.rho).symm
      _ = _ := by
        apply congrArg List.ofFn
        funext r
        funext v
        exact S05_rho_canonicalMatchingEdgePerm_eq m lam action x r v
  rw [hlist]
  rfl

/-- The canonical basis transported by the explicit matching relabeling. -/
noncomputable def S05_arbitraryEvenMatchingBasis
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    Module.Basis (S05_CanonicalEvenEigenbasisIndex (m + 1) lam) Real
      (TableauSpace lam) :=
  (S05_canonicalEvenMatchingBasis (m + 1) lam).map
    (action.rhoLinearEquiv (S05_perfectMatchingRelabeling (m + 1) M))

@[simp] theorem S05_arbitraryEvenMatchingBasis_apply
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1)))
    (i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam) :
    S05_arbitraryEvenMatchingBasis m lam action M i =
      action.rep.rho (S05_perfectMatchingRelabeling (m + 1) M)
        (S05_canonicalEvenMatchingBasis (m + 1) lam i) := by
  rw [S05_arbitraryEvenMatchingBasis, Module.Basis.map_apply]
  rfl

/-- Transport preserves the canonical orthonormality relations. -/
theorem S05_arbitraryEvenMatchingBasis_inner
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1)))
    (i j : S05_CanonicalEvenEigenbasisIndex (m + 1) lam) :
    tableauInner
        (S05_arbitraryEvenMatchingBasis m lam action M i)
        (S05_arbitraryEvenMatchingBasis m lam action M j) =
      if i = j then 1 else 0 := by
  rw [S05_arbitraryEvenMatchingBasis_apply,
    S05_arbitraryEvenMatchingBasis_apply, action.rho_inner]
  exact (S05_Lem5_16_canonicalEvenMatchingEigenbasis m lam).1 i j

/-- The transported family spans because it is the image of a basis under the
represented permutation linear equivalence. -/
theorem S05_arbitraryEvenMatchingBasis_span
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    Submodule.span Real
        (Set.range (S05_arbitraryEvenMatchingBasis m lam action M)) = ⊤ :=
  (S05_arbitraryEvenMatchingBasis m lam action M).span_eq

/-- Every transported vector has its unchanged canonical character label for
the reindexed arbitrary matching. -/
theorem S05_arbitraryEvenMatchingBasis_character_action
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1)))
    (i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam)
    (x : Cube (m + 1)) :
    action.rep.rho ((S05_evenOrderedMatching (m + 1) M).tau x)
        (S05_arbitraryEvenMatchingBasis m lam action M i) =
      S05_matchingCharacter
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x •
        S05_arbitraryEvenMatchingBasis m lam action M i := by
  let σ := S05_perfectMatchingRelabeling (m + 1) M
  let τ := (S05_canonicalOrderedPerfectMatching (m + 1)).tau x
  let v := S05_canonicalEvenMatchingBasis (m + 1) lam i
  rw [S05_arbitraryEvenMatchingBasis_apply]
  rw [S05_evenOrderedMatching_tau_conjugate]
  change action.rep.rho (σ * τ * σ.symm) (action.rep.rho σ v) = _
  calc
    action.rep.rho (σ * τ * σ.symm) (action.rep.rho σ v) =
        action.rep.rho σ
          (action.rep.rho τ
            (action.rep.rho σ.symm (action.rep.rho σ v))) := by
      rw [action.rep.map_mul (σ * τ), action.rep.map_mul σ τ]
    _ = action.rep.rho σ (action.rep.rho τ v) := by
      rw [action.rho_leftInverse]
    _ = action.rep.rho σ (canonicalMatchingCubeOperatorEven x v) := by
      rw [S05_rho_canonicalMatchingTau_eq_canonicalMatchingCubeOperatorEven]
    _ = action.rep.rho σ
          (S05_matchingCharacter
            (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x • v) := by
      rw [S05_canonicalEvenMatchingBasis_character_action]
    _ = S05_matchingCharacter
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x •
          action.rep.rho σ v := by
      rw [action.rep.map_smul]

/-- Complete arbitrary-perfect-matching transport in normalized edge
coordinates: an orthonormal spanning basis, simultaneous character action, and
the literal canonical label multiset. -/
theorem S05_Lem5_16_arbitraryEvenMatchingEigenbasis
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    (∀ i j : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      tableauInner
          (S05_arbitraryEvenMatchingBasis m lam action M i)
          (S05_arbitraryEvenMatchingBasis m lam action M j) =
        if i = j then 1 else 0) ∧
    (Submodule.span Real
        (Set.range (S05_arbitraryEvenMatchingBasis m lam action M)) = ⊤) ∧
    (∀ i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      ∀ x : Cube (m + 1),
        action.rep.rho ((S05_evenOrderedMatching (m + 1) M).tau x)
            (S05_arbitraryEvenMatchingBasis m lam action M i) =
          S05_matchingCharacter
              (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x •
            S05_arbitraryEvenMatchingBasis m lam action M i) ∧
    (Finset.univ : Finset
        (S05_CanonicalEvenEigenbasisIndex (m + 1) lam)).1.map
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam) =
      S05_evenSignPatternMultiset (m + 1) lam := by
  refine ⟨?_, S05_arbitraryEvenMatchingBasis_span m lam action M, ?_, ?_⟩
  · exact S05_arbitraryEvenMatchingBasis_inner m lam action M
  · exact S05_arbitraryEvenMatchingBasis_character_action m lam action M
  · exact S05_canonicalEvenEigenbasisLabelMultiset_eq (m + 1) lam

/-- Transport a matching-cube coordinate function along equality of ordered
matchings. -/
def S05_matchingCubeCast
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (x : Cube M.edgeCount) : Cube N.edgeCount := by
  cases h
  exact x

/-- Transport a matching-character label along equality of ordered matchings. -/
def S05_matchingLabelCast
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (R : Finset (Fin M.edgeCount)) :
    Finset (Fin N.edgeCount) := by
  cases h
  exact R

@[simp] theorem S05_matchingCubeCast_refl
    {α : Type*} [DecidableEq α] (M : OrderedMatching α)
    (x : Cube M.edgeCount) :
    S05_matchingCubeCast (Eq.refl M) x = x := by
  rfl

@[simp] theorem S05_matchingLabelCast_refl
    {α : Type*} [DecidableEq α] (M : OrderedMatching α)
    (R : Finset (Fin M.edgeCount)) :
    S05_matchingLabelCast (Eq.refl M) R = R := by
  rfl

/-- Equality of ordered matchings transports their matching-cube elements. -/
theorem S05_orderedMatching_tau_cast
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (x : Cube N.edgeCount) :
    N.tau x = M.tau (S05_matchingCubeCast h.symm x) := by
  cases h
  rfl

/-- Simultaneously transporting a label and pulling back a cube point preserves
the matching character. -/
theorem S05_matchingCharacter_labelCast
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (R : Finset (Fin M.edgeCount))
    (x : Cube N.edgeCount) :
    S05_matchingCharacter (S05_matchingLabelCast h R) x =
      S05_matchingCharacter R (S05_matchingCubeCast h.symm x) := by
  cases h
  rfl

/-- The canonical label viewed in the literal edge type of `M.toOrdered`. -/
def S05_arbitraryEvenMatchingLabel
    (m : Nat) (M : NearPerfectMatching (2 * m))
    (R : Finset (Fin m)) : Finset (Fin M.toOrdered.edgeCount) :=
  S05_matchingLabelCast (S05_evenOrderedMatching_eq_toOrdered m M) R

/-- Pull a literal `M.toOrdered` cube point back to the normalized `Fin m`
edge coordinates. -/
def S05_arbitraryEvenMatchingCubePullback
    (m : Nat) (M : NearPerfectMatching (2 * m))
    (x : Cube M.toOrdered.edgeCount) : Cube m :=
  S05_matchingCubeCast (S05_evenOrderedMatching_eq_toOrdered m M).symm x

/-- The arithmetic edge-count transport does not alter the character value. -/
theorem S05_arbitraryEvenMatchingCharacter_eq_pullback
    (m : Nat) (M : NearPerfectMatching (2 * m))
    (R : Finset (Fin m)) (x : Cube M.toOrdered.edgeCount) :
    S05_matchingCharacter (S05_arbitraryEvenMatchingLabel m M R) x =
      S05_matchingCharacter R
        (S05_arbitraryEvenMatchingCubePullback m M x) := by
  exact S05_matchingCharacter_labelCast
    (S05_evenOrderedMatching_eq_toOrdered m M) R x

/-- Equality transport of the edge type preserves label cardinality. -/
@[simp] theorem S05_matchingLabelCast_card
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (R : Finset (Fin M.edgeCount)) :
    (S05_matchingLabelCast h R).card = R.card := by
  cases h
  rfl

/-- Equality transport of the edge type preserves the high-character
predicate. -/
@[simp] theorem S05_matchingCharacterHigh_labelCast
    {α : Type*} [DecidableEq α] {M N : OrderedMatching α}
    (h : M = N) (R : Finset (Fin M.edgeCount)) :
    S05_matchingCharacterHigh (S05_matchingLabelCast h R) ↔
      S05_matchingCharacterHigh R := by
  cases h
  rfl

/-- Exact transported label multiset. The right side is Definition 5.10 mapped
only through the propositional equality between `m` and `M.toOrdered.edgeCount`.
-/
theorem S05_arbitraryEvenMatchingLabelMultiset_eq
    (m : Nat) (lam : YoungDiagram (2 * m))
    (M : NearPerfectMatching (2 * m)) :
    (Finset.univ : Finset
        (S05_CanonicalEvenEigenbasisIndex m lam)).1.map
          (fun i => S05_arbitraryEvenMatchingLabel m M
            (S05_canonicalEvenEigenbasisLabel m lam i)) =
      (S05_evenSignPatternMultiset m lam).map
        (S05_matchingLabelCast (S05_evenOrderedMatching_eq_toOrdered m M)) := by
  rw [← S05_canonicalEvenEigenbasisLabelMultiset_eq m lam]
  change
    (Finset.univ : Finset
      (S05_CanonicalEvenEigenbasisIndex m lam)).1.map
        (fun i => S05_matchingLabelCast
          (S05_evenOrderedMatching_eq_toOrdered m M)
          (S05_canonicalEvenEigenbasisLabel m lam i)) =
      ((Finset.univ : Finset
        (S05_CanonicalEvenEigenbasisIndex m lam)).1.map
          (S05_canonicalEvenEigenbasisLabel m lam)).map
        (S05_matchingLabelCast (S05_evenOrderedMatching_eq_toOrdered m M))
  exact (Multiset.map_map
    (S05_matchingLabelCast (S05_evenOrderedMatching_eq_toOrdered m M))
    (S05_canonicalEvenEigenbasisLabel m lam) _).symm

/-- The transported arbitrary-matching labels have the same high-label count
as the canonical labels. -/
theorem S05_arbitraryEvenMatchingBasis_highLabelCount
    (m : Nat) (lam : YoungDiagram (2 * m))
    (M : NearPerfectMatching (2 * m)) :
    (∑ i : S05_CanonicalEvenEigenbasisIndex m lam,
        if S05_matchingCharacterHigh
            (S05_arbitraryEvenMatchingLabel m M
              (S05_canonicalEvenEigenbasisLabel m lam i))
        then (1 : Real) else 0) =
      hEvenTableau m lam := by
  change
    (∑ i : S05_CanonicalEvenEigenbasisIndex m lam,
      if S05_matchingCharacterHigh
          (S05_matchingLabelCast (S05_evenOrderedMatching_eq_toOrdered m M)
            (S05_canonicalEvenEigenbasisLabel m lam i))
      then (1 : Real) else 0) = hEvenTableau m lam
  simp_rw [S05_matchingCharacterHigh_labelCast]
  exact S05_signPatternCardinality_highLabelCount_of_evenSignPatternMultiset
    (S05_canonicalEvenEigenbasisLabel m lam)
    (S05_canonicalEvenEigenbasisLabelMultiset_eq m lam)

/-- Character action stated directly for `M.toOrdered`; the only coordinate
transport is the proof-level identification of its edge count with `m+1`. -/
theorem S05_arbitraryEvenMatchingBasis_toOrdered_character_action
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1)))
    (i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam)
    (x : Cube M.toOrdered.edgeCount) :
    action.rep.rho (M.toOrdered.tau x)
        (S05_arbitraryEvenMatchingBasis m lam action M i) =
      S05_matchingCharacter
          (S05_arbitraryEvenMatchingLabel (m + 1) M
            (S05_canonicalEvenEigenbasisLabel (m + 1) lam i)) x •
        S05_arbitraryEvenMatchingBasis m lam action M i := by
  let x₀ := S05_arbitraryEvenMatchingCubePullback (m + 1) M x
  calc
    action.rep.rho (M.toOrdered.tau x)
        (S05_arbitraryEvenMatchingBasis m lam action M i) =
        action.rep.rho ((S05_evenOrderedMatching (m + 1) M).tau x₀)
          (S05_arbitraryEvenMatchingBasis m lam action M i) := by
      rw [S05_orderedMatching_tau_cast
        (S05_evenOrderedMatching_eq_toOrdered (m + 1) M)]
      rfl
    _ = S05_matchingCharacter
          (S05_canonicalEvenEigenbasisLabel (m + 1) lam i) x₀ •
        S05_arbitraryEvenMatchingBasis m lam action M i :=
      S05_arbitraryEvenMatchingBasis_character_action m lam action M i x₀
    _ = S05_matchingCharacter
          (S05_arbitraryEvenMatchingLabel (m + 1) M
            (S05_canonicalEvenEigenbasisLabel (m + 1) lam i)) x •
        S05_arbitraryEvenMatchingBasis m lam action M i := by
      rw [← S05_arbitraryEvenMatchingCharacter_eq_pullback]

/-- Arbitrary-perfect-matching theorem stated directly for `M.toOrdered`.
The label multiset is the literal Definition 5.10 multiset transported through
the unavoidable propositional equality of the two edge-count expressions. -/
theorem S05_Lem5_16_arbitraryEvenMatchingEigenbasis_toOrdered
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * (m + 1))) :
    (∀ i j : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      tableauInner
          (S05_arbitraryEvenMatchingBasis m lam action M i)
          (S05_arbitraryEvenMatchingBasis m lam action M j) =
        if i = j then 1 else 0) ∧
    (Submodule.span Real
        (Set.range (S05_arbitraryEvenMatchingBasis m lam action M)) = ⊤) ∧
    (∀ i : S05_CanonicalEvenEigenbasisIndex (m + 1) lam,
      ∀ x : Cube M.toOrdered.edgeCount,
        action.rep.rho (M.toOrdered.tau x)
            (S05_arbitraryEvenMatchingBasis m lam action M i) =
          S05_matchingCharacter
              (S05_arbitraryEvenMatchingLabel (m + 1) M
                (S05_canonicalEvenEigenbasisLabel (m + 1) lam i)) x •
            S05_arbitraryEvenMatchingBasis m lam action M i) ∧
    (Finset.univ : Finset
        (S05_CanonicalEvenEigenbasisIndex (m + 1) lam)).1.map
          (fun i => S05_arbitraryEvenMatchingLabel (m + 1) M
            (S05_canonicalEvenEigenbasisLabel (m + 1) lam i)) =
      (S05_evenSignPatternMultiset (m + 1) lam).map
        (S05_matchingLabelCast
          (S05_evenOrderedMatching_eq_toOrdered (m + 1) M)) := by
  refine ⟨S05_arbitraryEvenMatchingBasis_inner m lam action M,
    S05_arbitraryEvenMatchingBasis_span m lam action M, ?_, ?_⟩
  · exact S05_arbitraryEvenMatchingBasis_toOrdered_character_action
      m lam action M
  · exact S05_arbitraryEvenMatchingLabelMultiset_eq (m + 1) lam M

/-! ## Transport to arbitrary odd near-perfect matchings -/

/-- The edge count of an odd near-perfect matching is `m`. -/
theorem S05_oddMatching_edgeCount_eq
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    m = M.toOrdered.edgeCount := by
  simp [NearPerfectMatching.toOrdered]
  omega

/-- Reindex an odd near-perfect matching by the literal edge type `Fin m`. -/
noncomputable def S05_oddOrderedMatching
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    OrderedMatching (Fin (2 * m + 1)) where
  edgeCount := m
  left r := M.toOrdered.left (Fin.cast (S05_oddMatching_edgeCount_eq m M) r)
  right r := M.toOrdered.right (Fin.cast (S05_oddMatching_edgeCount_eq m M) r)
  left_ne_right r := M.toOrdered.left_ne_right _
  edges_disjoint := by
    intro r s hrs
    apply M.toOrdered.edges_disjoint
    intro h
    apply hrs
    exact Fin.cast_injective (S05_oddMatching_edgeCount_eq m M) h

/-- The reindexed odd matching is propositionally the original ordered
matching. -/
theorem S05_oddOrderedMatching_eq_toOrdered
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    S05_oddOrderedMatching m M = M.toOrdered := by
  apply S05_orderedMatching_ext _ _ (S05_oddMatching_edgeCount_eq m M)
  · intro r
    rfl
  · intro r
    rfl

/-- Endpoint map for an odd near-perfect matching, before adjoining its unique
unmatched vertex. -/
def S05_nearPerfectMatchingEndpointMap
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Fin m × Fin 2 -> Fin (2 * m + 1)
  | (r, b) => Fin.cases ((S05_oddOrderedMatching m M).left r)
      (fun _ => (S05_oddOrderedMatching m M).right r) b

@[simp] theorem S05_nearPerfectMatchingEndpointMap_zero
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingEndpointMap m M (r, 0) =
      (S05_oddOrderedMatching m M).left r := by
  rfl

@[simp] theorem S05_nearPerfectMatchingEndpointMap_one
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingEndpointMap m M (r, 1) =
      (S05_oddOrderedMatching m M).right r := by
  rfl

/-- Matching disjointness makes the odd endpoint map injective. -/
theorem S05_nearPerfectMatchingEndpointMap_injective
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Function.Injective (S05_nearPerfectMatchingEndpointMap m M) := by
  intro x y h
  rcases x with ⟨r, b⟩
  rcases y with ⟨s, c⟩
  fin_cases b <;> fin_cases c
  · have hrs : r = s := by
      by_contra hne
      exact ((S05_oddOrderedMatching m M).edges_disjoint hne).1 h
    subst s
    rfl
  · by_cases hrs : r = s
    · subst s
      exact False.elim ((S05_oddOrderedMatching m M).left_ne_right r h)
    · exact False.elim
        (((S05_oddOrderedMatching m M).edges_disjoint hrs).2.1 h)
  · by_cases hrs : r = s
    · subst s
      exact False.elim ((S05_oddOrderedMatching m M).left_ne_right r h.symm)
    · exact False.elim
        (((S05_oddOrderedMatching m M).edges_disjoint hrs).2.2.1 h)
  · have hrs : r = s := by
      by_contra hne
      exact ((S05_oddOrderedMatching m M).edges_disjoint hne).2.2.2 h
    subst s
    rfl

/-- The finite set of all endpoints used by an odd near-perfect matching. -/
def S05_nearPerfectMatchingEndpointSet
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Finset (Fin (2 * m + 1)) :=
  Finset.univ.image (S05_nearPerfectMatchingEndpointMap m M)

/-- The endpoint set has cardinality exactly `2*m`. -/
theorem S05_nearPerfectMatchingEndpointSet_card
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    (S05_nearPerfectMatchingEndpointSet m M).card = 2 * m := by
  rw [S05_nearPerfectMatchingEndpointSet,
    Finset.card_image_of_injective Finset.univ
      (S05_nearPerfectMatchingEndpointMap_injective m M)]
  simp [Nat.mul_comm]

/-- Exactly one ambient vertex is absent from the endpoint set. -/
theorem S05_nearPerfectMatchingEndpointSet_compl_card
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    (S05_nearPerfectMatchingEndpointSet m M)ᶜ.card = 1 := by
  rw [Finset.card_compl, S05_nearPerfectMatchingEndpointSet_card]
  simp

/-- An odd near-perfect matching has a unique unmatched vertex. -/
theorem S05_existsUnique_nearPerfectMatchingUnmatchedPoint
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    ∃! u : Fin (2 * m + 1),
      u ∉ S05_nearPerfectMatchingEndpointSet m M := by
  simpa using Finset.card_eq_one_iff_existsUnique.mp
    (S05_nearPerfectMatchingEndpointSet_compl_card m M)

/-- The unique unmatched vertex of an odd near-perfect matching. -/
noncomputable def S05_nearPerfectMatchingUnmatchedPoint
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Fin (2 * m + 1) :=
  Classical.choose (S05_existsUnique_nearPerfectMatchingUnmatchedPoint m M)

theorem S05_nearPerfectMatchingUnmatchedPoint_not_endpoint
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    S05_nearPerfectMatchingUnmatchedPoint m M ∉
      S05_nearPerfectMatchingEndpointSet m M :=
  (Classical.choose_spec
    (S05_existsUnique_nearPerfectMatchingUnmatchedPoint m M)).1

/-- Any unmatched vertex equals the chosen unmatched point. -/
theorem S05_nearPerfectMatchingUnmatchedPoint_unique
    (m : Nat) (M : NearPerfectMatching (2 * m + 1))
    {u : Fin (2 * m + 1)}
    (hu : u ∉ S05_nearPerfectMatchingEndpointSet m M) :
    u = S05_nearPerfectMatchingUnmatchedPoint m M :=
  (Classical.choose_spec
    (S05_existsUnique_nearPerfectMatchingUnmatchedPoint m M)).2 u hu

theorem S05_nearPerfectMatchingUnmatchedPoint_ne_left
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingUnmatchedPoint m M ≠
      (S05_oddOrderedMatching m M).left r := by
  intro h
  apply S05_nearPerfectMatchingUnmatchedPoint_not_endpoint m M
  rw [h]
  exact Finset.mem_image.mpr ⟨(r, 0), Finset.mem_univ _, rfl⟩

theorem S05_nearPerfectMatchingUnmatchedPoint_ne_right
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingUnmatchedPoint m M ≠
      (S05_oddOrderedMatching m M).right r := by
  intro h
  apply S05_nearPerfectMatchingUnmatchedPoint_not_endpoint m M
  rw [h]
  exact Finset.mem_image.mpr ⟨(r, 1), Finset.mem_univ _, rfl⟩

/-- Every vertex other than the unique unmatched point is a matching
endpoint. -/
theorem S05_nearPerfectMatching_exists_endpoint_of_ne_unmatched
    (m : Nat) (M : NearPerfectMatching (2 * m + 1))
    (u : Fin (2 * m + 1))
    (hu : u ≠ S05_nearPerfectMatchingUnmatchedPoint m M) :
    ∃ r : Fin m,
      u = (S05_oddOrderedMatching m M).left r ∨
        u = (S05_oddOrderedMatching m M).right r := by
  have humem : u ∈ S05_nearPerfectMatchingEndpointSet m M := by
    by_contra hnot
    exact hu (S05_nearPerfectMatchingUnmatchedPoint_unique m M hnot)
  rcases Finset.mem_image.mp humem with ⟨x, _hx, hxu⟩
  rcases x with ⟨r, b⟩
  refine ⟨r, ?_⟩
  fin_cases b
  · exact Or.inl hxu.symm
  · exact Or.inr hxu.symm

/-- Canonical endpoint-plus-unmatched encoding for the odd matching. -/
def S05_canonicalNearMatchingEndpointEquiv (m : Nat) :
    (Fin m × Fin 2) ⊕ Fin 1 ≃ Fin (2 * m + 1) :=
  (Equiv.sumCongr (S05_canonicalMatchingEndpointEquiv m) (Equiv.refl (Fin 1))).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem S05_canonicalNearMatchingEndpointEquiv_zero
    (m : Nat) (r : Fin m) :
    S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 0)) =
      Fin.castSucc (S05_canonicalMatchingEndpointEquiv m (r, 0)) := by
  apply Fin.ext
  simp [S05_canonicalNearMatchingEndpointEquiv]

@[simp] theorem S05_canonicalNearMatchingEndpointEquiv_one
    (m : Nat) (r : Fin m) :
    S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 1)) =
      Fin.castSucc (S05_canonicalMatchingEndpointEquiv m (r, 1)) := by
  apply Fin.ext
  simp [S05_canonicalNearMatchingEndpointEquiv]

@[simp] theorem S05_canonicalNearMatchingEndpointEquiv_unmatched
    (m : Nat) (u : Fin 1) :
    S05_canonicalNearMatchingEndpointEquiv m (Sum.inr u) =
      Fin.last (2 * m) := by
  apply Fin.ext
  fin_cases u
  simp [S05_canonicalNearMatchingEndpointEquiv]

/-- The canonical ordered near-perfect matching, with final vertex unmatched.
-/
noncomputable def S05_canonicalOrderedNearPerfectMatching (m : Nat) :
    OrderedMatching (Fin (2 * m + 1)) where
  edgeCount := m
  left r := S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 0))
  right r := S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 1))
  left_ne_right r := by
    intro h
    have hinj := (S05_canonicalNearMatchingEndpointEquiv m).injective h
    simp at hinj
  edges_disjoint := by
    intro r s hrs
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact hrs (congrArg Prod.fst (Sum.inl.inj
        ((S05_canonicalNearMatchingEndpointEquiv m).injective h)))
    · have hb := congrArg Prod.snd (Sum.inl.inj
        ((S05_canonicalNearMatchingEndpointEquiv m).injective h))
      simp at hb
    · have hb := congrArg Prod.snd (Sum.inl.inj
        ((S05_canonicalNearMatchingEndpointEquiv m).injective h))
      simp at hb
    · exact hrs (congrArg Prod.fst (Sum.inl.inj
        ((S05_canonicalNearMatchingEndpointEquiv m).injective h)))

/-- Endpoint-plus-unmatched map for an arbitrary odd near-perfect matching. -/
def S05_nearPerfectMatchingEndpointWithUnmatchedMap
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    (Fin m × Fin 2) ⊕ Fin 1 -> Fin (2 * m + 1)
  | Sum.inl x => S05_nearPerfectMatchingEndpointMap m M x
  | Sum.inr _ => S05_nearPerfectMatchingUnmatchedPoint m M

theorem S05_nearPerfectMatchingEndpointWithUnmatchedMap_injective
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Function.Injective (S05_nearPerfectMatchingEndpointWithUnmatchedMap m M) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl
      (S05_nearPerfectMatchingEndpointMap_injective m M h)
  · exfalso
    apply S05_nearPerfectMatchingUnmatchedPoint_not_endpoint m M
    change S05_nearPerfectMatchingEndpointMap m M x =
      S05_nearPerfectMatchingUnmatchedPoint m M at h
    rw [← h]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · exfalso
    apply S05_nearPerfectMatchingUnmatchedPoint_not_endpoint m M
    change S05_nearPerfectMatchingUnmatchedPoint m M =
      S05_nearPerfectMatchingEndpointMap m M y at h
    rw [h]
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  · exact congrArg Sum.inr (Subsingleton.elim x y)

theorem S05_nearPerfectMatchingEndpointWithUnmatchedMap_surjective
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Function.Surjective (S05_nearPerfectMatchingEndpointWithUnmatchedMap m M) := by
  intro u
  by_cases hu : u = S05_nearPerfectMatchingUnmatchedPoint m M
  · exact ⟨Sum.inr 0, by simpa
      [S05_nearPerfectMatchingEndpointWithUnmatchedMap] using hu.symm⟩
  · rcases S05_nearPerfectMatching_exists_endpoint_of_ne_unmatched m M u hu with
      ⟨r, hleft | hright⟩
    · exact ⟨Sum.inl (r, 0), by simpa
        [S05_nearPerfectMatchingEndpointWithUnmatchedMap] using hleft.symm⟩
    · exact ⟨Sum.inl (r, 1), by simpa
        [S05_nearPerfectMatchingEndpointWithUnmatchedMap] using hright.symm⟩

/-- Endpoint-preserving equivalence including the unique unmatched vertex. -/
noncomputable def S05_nearPerfectMatchingEndpointEquiv
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    (Fin m × Fin 2) ⊕ Fin 1 ≃ Fin (2 * m + 1) :=
  Equiv.ofBijective (S05_nearPerfectMatchingEndpointWithUnmatchedMap m M)
    ⟨S05_nearPerfectMatchingEndpointWithUnmatchedMap_injective m M,
      S05_nearPerfectMatchingEndpointWithUnmatchedMap_surjective m M⟩

/-- Explicit odd conjugating permutation, preserving every edge coordinate and
sending the canonical final unmatched vertex to the unique unmatched point. -/
noncomputable def S05_nearPerfectMatchingRelabeling
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    Perm (Fin (2 * m + 1)) :=
  (S05_canonicalNearMatchingEndpointEquiv m).symm.trans
    (S05_nearPerfectMatchingEndpointEquiv m M)

@[simp] theorem S05_nearPerfectMatchingRelabeling_left
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingRelabeling m M
        ((S05_canonicalOrderedNearPerfectMatching m).left r) =
      (S05_oddOrderedMatching m M).left r := by
  change
    S05_nearPerfectMatchingEndpointEquiv m M
        ((S05_canonicalNearMatchingEndpointEquiv m).symm
          (S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 0)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem S05_nearPerfectMatchingRelabeling_right
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (r : Fin m) :
    S05_nearPerfectMatchingRelabeling m M
        ((S05_canonicalOrderedNearPerfectMatching m).right r) =
      (S05_oddOrderedMatching m M).right r := by
  change
    S05_nearPerfectMatchingEndpointEquiv m M
        ((S05_canonicalNearMatchingEndpointEquiv m).symm
          (S05_canonicalNearMatchingEndpointEquiv m (Sum.inl (r, 1)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem S05_nearPerfectMatchingRelabeling_unmatched
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    S05_nearPerfectMatchingRelabeling m M (Fin.last (2 * m)) =
      S05_nearPerfectMatchingUnmatchedPoint m M := by
  change
    S05_nearPerfectMatchingEndpointEquiv m M
        ((S05_canonicalNearMatchingEndpointEquiv m).symm
          (S05_canonicalNearMatchingEndpointEquiv m (Sum.inr 0))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Relabeling the canonical odd matching gives the supplied matching. -/
theorem S05_canonicalOrderedNearPerfectMatching_relabel
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) :
    (S05_canonicalOrderedNearPerfectMatching m).relabel
        (S05_nearPerfectMatchingRelabeling m M) = M.toOrdered := by
  rw [← S05_oddOrderedMatching_eq_toOrdered m M]
  refine S05_orderedMatching_ext _ _ rfl ?_ ?_
  · intro r
    exact S05_nearPerfectMatchingRelabeling_left m M r
  · intro r
    exact S05_nearPerfectMatchingRelabeling_right m M r

/-- The arbitrary odd matching-cube element is the conjugate of the canonical
odd matching-cube element. -/
theorem S05_oddOrderedMatching_tau_conjugate
    (m : Nat) (M : NearPerfectMatching (2 * m + 1)) (x : Cube m) :
    (S05_oddOrderedMatching m M).tau x =
      S05_nearPerfectMatchingRelabeling m M *
        (S05_canonicalOrderedNearPerfectMatching m).tau x *
          (S05_nearPerfectMatchingRelabeling m M).symm := by
  have htau :
      (S05_oddOrderedMatching m M).tau x =
        ((S05_canonicalOrderedNearPerfectMatching m).relabel
          (S05_nearPerfectMatchingRelabeling m M)).tau x := by
    unfold OrderedMatching.tau
    change
      (List.ofFn fun r : Fin m =>
        (S05_oddOrderedMatching m M).edgePerm x r).prod =
      (List.ofFn fun r : Fin m =>
        ((S05_canonicalOrderedNearPerfectMatching m).relabel
          (S05_nearPerfectMatchingRelabeling m M)).edgePerm x r).prod
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext r
    unfold OrderedMatching.edgePerm
    by_cases hx : x r
    · simp only [hx, if_true]
      unfold OrderedMatching.edgeSwap OrderedMatching.relabel
      change
        pswap ((S05_oddOrderedMatching m M).left r)
            ((S05_oddOrderedMatching m M).right r) =
          pswap
            (S05_nearPerfectMatchingRelabeling m M
              ((S05_canonicalOrderedNearPerfectMatching m).left r))
            (S05_nearPerfectMatchingRelabeling m M
              ((S05_canonicalOrderedNearPerfectMatching m).right r))
      rw [S05_nearPerfectMatchingRelabeling_left,
        S05_nearPerfectMatchingRelabeling_right]
    · simp [hx]
  rw [htau]
  exact orderedMatching_tau_relabel
    (S05_nearPerfectMatchingRelabeling m M)
    (S05_canonicalOrderedNearPerfectMatching m) x

/-- One canonical odd edge swap is the corresponding adjacent
transposition. -/
theorem S05_canonicalOrderedNearPerfectMatching_edgeSwap
    (m : Nat) (r : Fin m) :
    (S05_canonicalOrderedNearPerfectMatching m).edgeSwap r =
      s05_adjacentTransposition (canonicalNearMatchingAdjacentIndex m r) := by
  unfold OrderedMatching.edgeSwap s05_adjacentTransposition
    S05_canonicalOrderedNearPerfectMatching
  congr 1
  · apply Fin.ext
    simp [canonicalNearMatchingAdjacentIndex]
  · apply Fin.ext
    simp [canonicalNearMatchingAdjacentIndex]

/-- The representation of one selected canonical odd edge is the corresponding
concrete Young operator bit. -/
theorem S05_rho_canonicalNearMatchingEdgePerm_eq
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (x : Cube m) (r : Fin m) (f : TableauSpace lam) :
    action.rep.rho
        ((S05_canonicalOrderedNearPerfectMatching m).edgePerm x r) f =
      canonicalMatchingYoungOperatorOddBit x r f := by
  unfold OrderedMatching.edgePerm canonicalMatchingYoungOperatorOddBit
  by_cases hx : x r
  · simp only [hx, if_true]
    rw [S05_canonicalOrderedNearPerfectMatching_edgeSwap]
    rw [action.rho_adjacent]
    rfl
  · simp only [hx]
    exact action.rep.map_one f

/-- The represented canonical odd matching-cube element is exactly the
concrete canonical odd cube operator. -/
theorem S05_rho_canonicalNearMatchingTau_eq_canonicalMatchingCubeOperatorOdd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (x : Cube m) (f : TableauSpace lam) :
    action.rep.rho
        ((S05_canonicalOrderedNearPerfectMatching m).tau x) f =
      canonicalMatchingCubeOperatorOdd x f := by
  unfold OrderedMatching.tau
  change action.rep.rho
      ((List.ofFn fun r : Fin m =>
        (S05_canonicalOrderedNearPerfectMatching m).edgePerm x r).prod) f = _
  rw [action.rep.rho_list_prod]
  have hlist :
      (List.ofFn fun r : Fin m =>
          (S05_canonicalOrderedNearPerfectMatching m).edgePerm x r).map
            action.rep.rho =
        List.ofFn (fun r : Fin m =>
          canonicalMatchingYoungOperatorOddBit x r) := by
    calc
      _ = List.ofFn (fun r : Fin m =>
          action.rep.rho
            ((S05_canonicalOrderedNearPerfectMatching m).edgePerm x r)) :=
        (List.ofFn_comp'
          (fun r : Fin m =>
            (S05_canonicalOrderedNearPerfectMatching m).edgePerm x r)
          action.rep.rho).symm
      _ = _ := by
        apply congrArg List.ofFn
        funext r
        funext v
        exact S05_rho_canonicalNearMatchingEdgePerm_eq m lam action x r v
  rw [hlist]
  rfl

/-- The canonical odd basis transported by the explicit endpoint-plus-unmatched
relabeling. -/
noncomputable def S05_arbitraryOddMatchingBasis
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    Module.Basis (S05_CanonicalOddEigenbasisIndex m lam) Real
      (TableauSpace lam) :=
  (S05_canonicalOddMatchingBasis m lam).map
    (action.rhoLinearEquiv (S05_nearPerfectMatchingRelabeling m M))

@[simp] theorem S05_arbitraryOddMatchingBasis_apply
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) :
    S05_arbitraryOddMatchingBasis m lam action M i =
      action.rep.rho (S05_nearPerfectMatchingRelabeling m M)
        (S05_canonicalOddMatchingBasis m lam i) := by
  rw [S05_arbitraryOddMatchingBasis, Module.Basis.map_apply]
  rfl

/-- Odd transport preserves orthonormality. -/
theorem S05_arbitraryOddMatchingBasis_inner
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1))
    (i j : S05_CanonicalOddEigenbasisIndex m lam) :
    tableauInner
        (S05_arbitraryOddMatchingBasis m lam action M i)
        (S05_arbitraryOddMatchingBasis m lam action M j) =
      if i = j then 1 else 0 := by
  rw [S05_arbitraryOddMatchingBasis_apply,
    S05_arbitraryOddMatchingBasis_apply, action.rho_inner]
  exact (S05_Lem5_16_canonicalOddMatchingEigenbasis m lam).1 i j

/-- The transported odd family spans because it is the image of a basis under
the represented permutation linear equivalence. -/
theorem S05_arbitraryOddMatchingBasis_span
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    Submodule.span Real
        (Set.range (S05_arbitraryOddMatchingBasis m lam action M)) = ⊤ :=
  (S05_arbitraryOddMatchingBasis m lam action M).span_eq

/-- Every transported odd vector has its unchanged canonical character label
for the reindexed arbitrary matching. -/
theorem S05_arbitraryOddMatchingBasis_character_action
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam) (x : Cube m) :
    action.rep.rho ((S05_oddOrderedMatching m M).tau x)
        (S05_arbitraryOddMatchingBasis m lam action M i) =
      S05_matchingCharacter (S05_canonicalOddEigenbasisLabel m lam i) x •
        S05_arbitraryOddMatchingBasis m lam action M i := by
  let σ := S05_nearPerfectMatchingRelabeling m M
  let τ := (S05_canonicalOrderedNearPerfectMatching m).tau x
  let v := S05_canonicalOddMatchingBasis m lam i
  rw [S05_arbitraryOddMatchingBasis_apply]
  rw [S05_oddOrderedMatching_tau_conjugate]
  change action.rep.rho (σ * τ * σ.symm) (action.rep.rho σ v) = _
  calc
    action.rep.rho (σ * τ * σ.symm) (action.rep.rho σ v) =
        action.rep.rho σ
          (action.rep.rho τ
            (action.rep.rho σ.symm (action.rep.rho σ v))) := by
      rw [action.rep.map_mul (σ * τ), action.rep.map_mul σ τ]
    _ = action.rep.rho σ (action.rep.rho τ v) := by
      rw [action.rho_leftInverse]
    _ = action.rep.rho σ (canonicalMatchingCubeOperatorOdd x v) := by
      rw [S05_rho_canonicalNearMatchingTau_eq_canonicalMatchingCubeOperatorOdd]
    _ = action.rep.rho σ
          (S05_matchingCharacter
            (S05_canonicalOddEigenbasisLabel m lam i) x • v) := by
      rw [S05_canonicalOddMatchingBasis_character_action]
    _ = S05_matchingCharacter
          (S05_canonicalOddEigenbasisLabel m lam i) x •
          action.rep.rho σ v := by
      rw [action.rep.map_smul]

/-- Complete arbitrary odd transport in normalized edge coordinates. -/
theorem S05_Lem5_16_arbitraryOddMatchingEigenbasis
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    (∀ i j : S05_CanonicalOddEigenbasisIndex m lam,
      tableauInner
          (S05_arbitraryOddMatchingBasis m lam action M i)
          (S05_arbitraryOddMatchingBasis m lam action M j) =
        if i = j then 1 else 0) ∧
    (Submodule.span Real
        (Set.range (S05_arbitraryOddMatchingBasis m lam action M)) = ⊤) ∧
    (∀ i : S05_CanonicalOddEigenbasisIndex m lam,
      ∀ x : Cube m,
        action.rep.rho ((S05_oddOrderedMatching m M).tau x)
            (S05_arbitraryOddMatchingBasis m lam action M i) =
          S05_matchingCharacter (S05_canonicalOddEigenbasisLabel m lam i) x •
            S05_arbitraryOddMatchingBasis m lam action M i) ∧
    (Finset.univ : Finset
        (S05_CanonicalOddEigenbasisIndex m lam)).1.map
          (S05_canonicalOddEigenbasisLabel m lam) =
      S05_oddSignPatternMultiset m lam := by
  refine ⟨S05_arbitraryOddMatchingBasis_inner m lam action M,
    S05_arbitraryOddMatchingBasis_span m lam action M, ?_, ?_⟩
  · exact S05_arbitraryOddMatchingBasis_character_action m lam action M
  · exact S05_canonicalOddEigenbasisLabelMultiset_eq m lam

/-- The canonical odd label viewed in the literal edge type of
`M.toOrdered`. -/
def S05_arbitraryOddMatchingLabel
    (m : Nat) (M : NearPerfectMatching (2 * m + 1))
    (R : Finset (Fin m)) : Finset (Fin M.toOrdered.edgeCount) :=
  S05_matchingLabelCast (S05_oddOrderedMatching_eq_toOrdered m M) R

/-- Pull a literal odd `M.toOrdered` cube point back to normalized `Fin m`
coordinates. -/
def S05_arbitraryOddMatchingCubePullback
    (m : Nat) (M : NearPerfectMatching (2 * m + 1))
    (x : Cube M.toOrdered.edgeCount) : Cube m :=
  S05_matchingCubeCast (S05_oddOrderedMatching_eq_toOrdered m M).symm x

theorem S05_arbitraryOddMatchingCharacter_eq_pullback
    (m : Nat) (M : NearPerfectMatching (2 * m + 1))
    (R : Finset (Fin m)) (x : Cube M.toOrdered.edgeCount) :
    S05_matchingCharacter (S05_arbitraryOddMatchingLabel m M R) x =
      S05_matchingCharacter R
        (S05_arbitraryOddMatchingCubePullback m M x) := by
  exact S05_matchingCharacter_labelCast
    (S05_oddOrderedMatching_eq_toOrdered m M) R x

/-- Exact odd label multiset transported only through the edge-count equality.
-/
theorem S05_arbitraryOddMatchingLabelMultiset_eq
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (M : NearPerfectMatching (2 * m + 1)) :
    (Finset.univ : Finset
        (S05_CanonicalOddEigenbasisIndex m lam)).1.map
          (fun i => S05_arbitraryOddMatchingLabel m M
            (S05_canonicalOddEigenbasisLabel m lam i)) =
      (S05_oddSignPatternMultiset m lam).map
        (S05_matchingLabelCast (S05_oddOrderedMatching_eq_toOrdered m M)) := by
  rw [← S05_canonicalOddEigenbasisLabelMultiset_eq m lam]
  change
    (Finset.univ : Finset
      (S05_CanonicalOddEigenbasisIndex m lam)).1.map
        (fun i => S05_matchingLabelCast
          (S05_oddOrderedMatching_eq_toOrdered m M)
          (S05_canonicalOddEigenbasisLabel m lam i)) =
      ((Finset.univ : Finset
        (S05_CanonicalOddEigenbasisIndex m lam)).1.map
          (S05_canonicalOddEigenbasisLabel m lam)).map
        (S05_matchingLabelCast (S05_oddOrderedMatching_eq_toOrdered m M))
  exact (Multiset.map_map
    (S05_matchingLabelCast (S05_oddOrderedMatching_eq_toOrdered m M))
    (S05_canonicalOddEigenbasisLabel m lam) _).symm

/-- The transported odd labels have the high-label count prescribed by
Definition 5.10. -/
theorem S05_arbitraryOddMatchingBasis_highLabelCount
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (M : NearPerfectMatching (2 * m + 1)) :
    (∑ i : S05_CanonicalOddEigenbasisIndex m lam,
        if S05_matchingCharacterHigh
            (S05_arbitraryOddMatchingLabel m M
              (S05_canonicalOddEigenbasisLabel m lam i))
        then (1 : Real) else 0) =
      hOddTableau m lam := by
  change
    (∑ i : S05_CanonicalOddEigenbasisIndex m lam,
      if S05_matchingCharacterHigh
          (S05_matchingLabelCast (S05_oddOrderedMatching_eq_toOrdered m M)
            (S05_canonicalOddEigenbasisLabel m lam i))
      then (1 : Real) else 0) = hOddTableau m lam
  simp_rw [S05_matchingCharacterHigh_labelCast]
  exact S05_signPatternCardinality_highLabelCount_of_oddSignPatternMultiset
    (S05_canonicalOddEigenbasisLabel m lam)
    (S05_canonicalOddEigenbasisLabelMultiset_eq m lam)

/-- Odd character action stated directly for `M.toOrdered`. -/
theorem S05_arbitraryOddMatchingBasis_toOrdered_character_action
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1))
    (i : S05_CanonicalOddEigenbasisIndex m lam)
    (x : Cube M.toOrdered.edgeCount) :
    action.rep.rho (M.toOrdered.tau x)
        (S05_arbitraryOddMatchingBasis m lam action M i) =
      S05_matchingCharacter
          (S05_arbitraryOddMatchingLabel m M
            (S05_canonicalOddEigenbasisLabel m lam i)) x •
        S05_arbitraryOddMatchingBasis m lam action M i := by
  let x₀ := S05_arbitraryOddMatchingCubePullback m M x
  calc
    action.rep.rho (M.toOrdered.tau x)
        (S05_arbitraryOddMatchingBasis m lam action M i) =
        action.rep.rho ((S05_oddOrderedMatching m M).tau x₀)
          (S05_arbitraryOddMatchingBasis m lam action M i) := by
      rw [S05_orderedMatching_tau_cast
        (S05_oddOrderedMatching_eq_toOrdered m M)]
      rfl
    _ = S05_matchingCharacter
          (S05_canonicalOddEigenbasisLabel m lam i) x₀ •
        S05_arbitraryOddMatchingBasis m lam action M i :=
      S05_arbitraryOddMatchingBasis_character_action m lam action M i x₀
    _ = S05_matchingCharacter
          (S05_arbitraryOddMatchingLabel m M
            (S05_canonicalOddEigenbasisLabel m lam i)) x •
        S05_arbitraryOddMatchingBasis m lam action M i := by
      rw [← S05_arbitraryOddMatchingCharacter_eq_pullback]

/-- Full arbitrary-near-perfect-matching theorem stated directly for
`M.toOrdered`, with exact transported odd labels. -/
theorem S05_Lem5_16_arbitraryOddMatchingEigenbasis_toOrdered
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (2 * m + 1)) :
    (∀ i j : S05_CanonicalOddEigenbasisIndex m lam,
      tableauInner
          (S05_arbitraryOddMatchingBasis m lam action M i)
          (S05_arbitraryOddMatchingBasis m lam action M j) =
        if i = j then 1 else 0) ∧
    (Submodule.span Real
        (Set.range (S05_arbitraryOddMatchingBasis m lam action M)) = ⊤) ∧
    (∀ i : S05_CanonicalOddEigenbasisIndex m lam,
      ∀ x : Cube M.toOrdered.edgeCount,
        action.rep.rho (M.toOrdered.tau x)
            (S05_arbitraryOddMatchingBasis m lam action M i) =
          S05_matchingCharacter
              (S05_arbitraryOddMatchingLabel m M
                (S05_canonicalOddEigenbasisLabel m lam i)) x •
            S05_arbitraryOddMatchingBasis m lam action M i) ∧
    (Finset.univ : Finset
        (S05_CanonicalOddEigenbasisIndex m lam)).1.map
          (fun i => S05_arbitraryOddMatchingLabel m M
            (S05_canonicalOddEigenbasisLabel m lam i)) =
      (S05_oddSignPatternMultiset m lam).map
        (S05_matchingLabelCast
          (S05_oddOrderedMatching_eq_toOrdered m M)) := by
  refine ⟨S05_arbitraryOddMatchingBasis_inner m lam action M,
    S05_arbitraryOddMatchingBasis_span m lam action M, ?_, ?_⟩
  · exact S05_arbitraryOddMatchingBasis_toOrdered_character_action
      m lam action M
  · exact S05_arbitraryOddMatchingLabelMultiset_eq m lam M

/-- Lemma 5.16 matching-operator component: a canonical even matching edge
operator is an involution. -/
theorem S05_Lem5_16_canonicalMatchingYoungOperatorEven_involutive
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven r f) = f := by
  exact canonicalMatchingYoungOperatorEven_involutive r f

/-- Lemma 5.16 matching-operator component: distinct canonical even matching
edge operators commute. -/
theorem S05_Lem5_16_canonicalMatchingYoungOperatorEven_comm
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven s f) =
      canonicalMatchingYoungOperatorEven s
        (canonicalMatchingYoungOperatorEven r f) := by
  exact canonicalMatchingYoungOperatorEven_comm hrs f

/-- Lemma 5.16 matching-operator component: a canonical odd matching edge
operator is an involution. -/
theorem S05_Lem5_16_canonicalMatchingYoungOperatorOdd_involutive
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd r f) = f := by
  exact canonicalMatchingYoungOperatorOdd_involutive r f

/-- Lemma 5.16 matching-operator component: distinct canonical odd matching
edge operators commute. -/
theorem S05_Lem5_16_canonicalMatchingYoungOperatorOdd_comm
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd s f) =
      canonicalMatchingYoungOperatorOdd s
        (canonicalMatchingYoungOperatorOdd r f) := by
  exact canonicalMatchingYoungOperatorOdd_comm hrs f

/-- Lemma 5.16 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_16_matchingEdge_plusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T + canonicalMatchingYoungOperatorEven r f T) =
      fun T => f T + canonicalMatchingYoungOperatorEven r f T := by
  exact canonicalMatchingYoungOperatorEven_plusEigenVec r f

/-- Lemma 5.16 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_16_matchingEdge_minusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T - canonicalMatchingYoungOperatorEven r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorEven r f T) := by
  exact canonicalMatchingYoungOperatorEven_minusEigenVec r f

/-- Lemma 5.16 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_16_matchingEdge_plusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T + canonicalMatchingYoungOperatorOdd r f T) =
      fun T => f T + canonicalMatchingYoungOperatorOdd r f T := by
  exact canonicalMatchingYoungOperatorOdd_plusEigenVec r f

/-- Lemma 5.16 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_16_matchingEdge_minusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T - canonicalMatchingYoungOperatorOdd r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorOdd r f T) := by
  exact canonicalMatchingYoungOperatorOdd_minusEigenVec r f

/-- Lemma 5.16 matching-cube component: the zero cube element acts trivially in
the even canonical matching action. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorEven_zero
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)} :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorEven_zero

/-- Lemma 5.16 matching-cube component: the zero cube element acts trivially in
the odd canonical matching action. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorOdd_zero
    {m : Nat} {lam : YoungDiagram (2 * m + 1)} :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorOdd_zero

/-- Lemma 5.16 matching-cube component: the even canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorEven_xor
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorEven_xor x y

/-- Lemma 5.16 matching-cube component: the odd canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorOdd_xor
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorOdd (lam := lam) x
        (canonicalMatchingCubeOperatorOdd (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorOdd_xor x y

/-- Lemma 5.16 matching-cube component: the even canonical matching-cube
operator is the fixed ordered product of the selected edge operators. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorEven_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
        x (List.finRange m) := by
  exact canonicalMatchingCubeOperatorEven_eq_indexedProduct x

/-- Lemma 5.16 matching-cube component: the odd canonical matching-cube
operator is the fixed ordered product of the selected edge operators. -/
theorem S05_Lem5_16_canonicalMatchingCubeOperatorOdd_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
        x (List.finRange m) := by
  exact canonicalMatchingCubeOperatorOdd_eq_indexedProduct x

/-- Lemma 5.16 matching-character component: the product of selected edge
signs is the matching character. -/
theorem S05_Lem5_16_matchingEdgeSign_finRange_product_eq_matchingCharacter
    {m : Nat} (R : Finset (Fin m)) (x : Cube m) :
    ((List.finRange m).map
      (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod =
        S05_matchingCharacter R x := by
  exact matchingEdgeSign_finRange_product_eq_cubeChar R x

/-- Lemma 5.16 matching-character component: on an even simultaneous
matching-edge eigenspace, the cube action is the product of selected edge
signs. -/
theorem S05_Lem5_16_matchingCube_product_action_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  exact canonicalMatchingCubeOperatorEven_apply_of_isMatchingEigenvector hf x

/-- Lemma 5.16 matching-character component: on an odd simultaneous
matching-edge eigenspace, the cube action is the product of selected edge
signs. -/
theorem S05_Lem5_16_matchingCube_product_action_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  exact canonicalMatchingCubeOperatorOdd_apply_of_isMatchingEigenvector hf x

/-- Lemma 5.16 matching-character component: on an even simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_16_matchingCube_character_action_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorEven_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.16 matching-character component: on an odd simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_16_matchingCube_character_action_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.16 projection component: the one-edge even plus projection lands in
the `+1` eigenspace of that edge. -/
theorem S05_Lem5_16_matchingEdgePlusProjectionEven_isPlusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgePlusProjectionEven r f) =
      matchingEdgePlusProjectionEven r f := by
  exact matchingEdgePlusProjectionEven_isPlusEigen r f

/-- Lemma 5.16 projection component: the one-edge even minus projection lands
in the `-1` eigenspace of that edge. -/
theorem S05_Lem5_16_matchingEdgeMinusProjectionEven_isMinusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeMinusProjectionEven r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionEven r f := by
  exact matchingEdgeMinusProjectionEven_isMinusEigen r f

/-- Lemma 5.16 projection component: the one-edge odd plus projection lands in
the `+1` eigenspace of that edge. -/
theorem S05_Lem5_16_matchingEdgePlusProjectionOdd_isPlusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgePlusProjectionOdd r f) =
      matchingEdgePlusProjectionOdd r f := by
  exact matchingEdgePlusProjectionOdd_isPlusEigen r f

/-- Lemma 5.16 projection component: the one-edge odd minus projection lands
in the `-1` eigenspace of that edge. -/
theorem S05_Lem5_16_matchingEdgeMinusProjectionOdd_isMinusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeMinusProjectionOdd r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionOdd r f := by
  exact matchingEdgeMinusProjectionOdd_isMinusEigen r f

/-- Lemma 5.16 projection component: projecting to the `+1` eigenspace of one
even matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgePlusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgePlusProjectionEven r f) =
      c • matchingEdgePlusProjectionEven r f := by
  exact matchingEdgePlusProjectionEven_preserves_otherEigen hrs hf

/-- Lemma 5.16 projection component: projecting to the `-1` eigenspace of one
even matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgeMinusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgeMinusProjectionEven r f) =
      c • matchingEdgeMinusProjectionEven r f := by
  exact matchingEdgeMinusProjectionEven_preserves_otherEigen hrs hf

/-- Lemma 5.16 projection component: projecting to the `+1` eigenspace of one
odd matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgePlusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgePlusProjectionOdd r f) =
      c • matchingEdgePlusProjectionOdd r f := by
  exact matchingEdgePlusProjectionOdd_preserves_otherEigen hrs hf

/-- Lemma 5.16 projection component: projecting to the `-1` eigenspace of one
odd matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgeMinusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgeMinusProjectionOdd r f) =
      c • matchingEdgeMinusProjectionOdd r f := by
  exact matchingEdgeMinusProjectionOdd_preserves_otherEigen hrs hf

/-- Lemma 5.16 projection component: the sign-selected even one-edge
projection has the edge eigenvalue prescribed by the support. -/
theorem S05_Lem5_16_matchingEdgeSignProjectionEven_isMatchingEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeSignProjectionEven R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionEven R r f := by
  exact matchingEdgeSignProjectionEven_isMatchingEigen R r f

/-- Lemma 5.16 projection component: the sign-selected odd one-edge projection
has the edge eigenvalue prescribed by the support. -/
theorem S05_Lem5_16_matchingEdgeSignProjectionOdd_isMatchingEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeSignProjectionOdd R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionOdd R r f := by
  exact matchingEdgeSignProjectionOdd_isMatchingEigen R r f

/-- Lemma 5.16 projection component: the sign-selected even one-edge projection
preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgeSignProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s
        (matchingEdgeSignProjectionEven R r f) =
      c • matchingEdgeSignProjectionEven R r f := by
  exact matchingEdgeSignProjectionEven_preserves_otherEigen R hrs hf

/-- Lemma 5.16 projection component: the sign-selected odd one-edge projection
preserves every other edge eigenvalue. -/
theorem S05_Lem5_16_matchingEdgeSignProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s
        (matchingEdgeSignProjectionOdd R r f) =
      c • matchingEdgeSignProjectionOdd R r f := by
  exact matchingEdgeSignProjectionOdd_preserves_otherEigen R hrs hf

/-- Lemma 5.16 projection component: the iterated even support-selected
projection is a simultaneous matching-edge eigenvector. -/
theorem S05_Lem5_16_matchingSignProjectionEven_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    S05_IsMatchingEigenvectorEven (matchingSignProjectionEven R f) R := by
  exact matchingSignProjectionEven_isMatchingEigenvector R f

/-- Lemma 5.16 projection component: the iterated odd support-selected
projection is a simultaneous matching-edge eigenvector. -/
theorem S05_Lem5_16_matchingSignProjectionOdd_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    S05_IsMatchingEigenvectorOdd (matchingSignProjectionOdd R f) R := by
  exact matchingSignProjectionOdd_isMatchingEigenvector R f

/-- Lemma 5.16 one-edge component: an even matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_16_matchingEdge_basis_sameRow_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow T r hrow

/-- Lemma 5.16 one-edge component: an even matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_16_matchingEdge_basis_sameCol_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol T r hcol

/-- Lemma 5.16 one-edge eigenspace component: in the even case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_16_matchingEdge_sameRow_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow_eigen T r hrow

/-- Lemma 5.16 one-edge eigenspace component: in the even case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_16_matchingEdge_sameCol_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol_eigen T r hcol

/-- Lemma 5.16 one-edge component: in an even swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_16_matchingEdge_basis_swappable_self_value_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorEven_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.16 one-edge component: in an even swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_16_matchingEdge_basis_swappable_swap_value_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorEven_basis_swappable_swap_value
    T r hrow_ne hcol_ne

/-- Lemma 5.16 one-edge component: an odd matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_16_matchingEdge_basis_sameRow_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow T r hrow

/-- Lemma 5.16 one-edge component: an odd matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_16_matchingEdge_basis_sameCol_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol T r hcol

/-- Lemma 5.16 one-edge eigenspace component: in the odd case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_16_matchingEdge_sameRow_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow_eigen T r hrow

/-- Lemma 5.16 one-edge eigenspace component: in the odd case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_16_matchingEdge_sameCol_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol_eigen T r hcol

/-- Lemma 5.16 one-edge component: in an odd swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_16_matchingEdge_basis_swappable_self_value_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorOdd_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.16 one-edge component: in an odd swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_16_matchingEdge_basis_swappable_swap_value_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalNearMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorOdd_basis_swappable_swap_value
    T r hrow_ne hcol_ne

/-- Once an even matching eigenbasis is labeled by the genuine recursive
multiset, its high-label count is the active tableau height. -/
theorem S05_Lem5_16_highLabelCount_of_evenSignPatternMultiset
    {m : Nat} {lam : YoungDiagram (2 * m)}
    {ι : Type*} [Fintype ι]
    (label : ι -> Finset (Fin m))
    (hlabels : Finset.univ.1.map label = S05_evenSignPatternMultiset m lam) :
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
      hEvenTableau m lam := by
  exact S05_signPatternCardinality_highLabelCount_of_evenSignPatternMultiset label hlabels

/-- Once an odd matching eigenbasis is labeled by the genuine recursive
multiset, its high-label count is the active tableau height. -/
theorem S05_Lem5_16_highLabelCount_of_oddSignPatternMultiset
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {ι : Type*} [Fintype ι]
    (label : ι -> Finset (Fin m))
    (hlabels : Finset.univ.1.map label = S05_oddSignPatternMultiset m lam) :
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
      hOddTableau m lam := by
  exact S05_signPatternCardinality_highLabelCount_of_oddSignPatternMultiset label hlabels

end DictatorshipTesting

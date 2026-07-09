# Proof Obligation Ledger

This ledger tracks mathematical obligations, not just raw Lean declarations.
External literature inputs are represented as named axiom declarations, not as
`sorry` proofs.

Current classification:

- External standard inputs: Section 2 structural/stability theorems and the
  representation-theoretic pieces of the Section 5 spectral bridge.
- Internal finite certificates: Lemmas 5.36, 5.38, and 5.40 have
  tableau-count versions proved in Lean.  The older `youngDim` variants still
  require explicit dimension-branching typeclass hypotheses and are not the
  current tableau-count proof route.
- Internal open finite certificates: none currently listed.
- Current external axiom declarations are exactly the two Section 2 inputs
  `booleanU1_dictator_classification_input` and `fknStability_input`; the
  Appendix A ingredient markers
  `AppA_ThmA_01_youngOrthogonalRealization`,
  `AppA_ThmA_02_jucysMurphyContentSpectrum`,
  `AppA_LemA_03_degreeOneYoungBlockIdentification`, and
  `AppA_LemA_04_standardTableauxSwapConnectedness`.  Lemma 5.32 has no
  standalone axiom; it is a proved assembly theorem from these Appendix A
  ingredients.
- Appendix A bridge boundary: the remaining representation-theoretic obligation
  is the spectral-block model input consumed by Section 5.
- Old `youngDim` dimension axiom instances are gone.  The older `youngDim`
  wrappers remain only as theorems with explicit typeclass hypotheses, and no
  instance is registered for those hypotheses.

## Sections 1--4 Status Maps

The current paper source checked for the early sections is
`../dictatorship_testing_soda27_latest.tex`.

Statement-to-file maps are maintained here:

- `DictatorshipTesting/Paper/SECTION1_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION2_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION3_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION4_FILE_MAP.md`

Early-section statement counts:

| Section | Count | Main status |
| --- | ---: | --- |
| 1 | 1 | Main theorem wrapper is proved from Lemma 4.13 and its documented inputs. |
| 2 | 4 | Theorem 2.1 and Theorem 2.2 are external Filmus inputs; Lemma 2.3 and Definition 2.4 are internal. |
| 3 | 2 | Both matching-cube completeness lemmas are internal. |
| 4 | 13 | The local Fourier and soundness reductions are internal. Theorem 4.10 is proved through the Section 5 tableau-count bridge and uses Lemma 5.32, which assembles the Appendix A inputs into the spectral model. |

Theorem 4.10 status: the active theorem is proved through the tableau-count
Section 5 bridge, using the Lemma 5.32 spectral model theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA`.  It no longer carries the
older `youngDim` dimension-branching typeclass hypotheses.

Active Theorem 1.1 dependency chain:

```text
Thm1_1_MainIntro
  -> exists_dimensionFreeTester_of_oneTrialSoundness
  -> L4_13_OneTrialSoundness
  -> Thm2_2_FKNInput
  -> Prop4_12_SquareEnergyControlsGlobalDegree
  -> Thm4_10_MatchingGap
  -> S05_Lem5_33_tableauDim_evenSpectralGapFromCertificates
     / S05_Lem5_34_tableauDim_oddSpectralGapFromCertificates
  -> S05_Lem5_32_RegularYoungBlockDecomposition
     (`spectralBlockModelInputWithDim_even_from_appendixA`
      / `spectralBlockModelInputWithDim_odd_from_appendixA`)
```

The Boolean `U_1` classification theorem is not a direct dependency of this
active Lean chain.  This is not currently a paper/Lean mismatch: the FKN input
used by Lemma 4.13 is already stated in the distance-to-dictators form needed
for soundness.  The Section 3 completeness lemmas are proved separately; the
current Theorem 1.1 wrapper goes through the abstract tester-amplification
interface rather than reusing those lemmas directly.

## Current Section 5 Route Summary

Proven current Section 5 components:

- Lemma 5.6 tableau Coxeter model:
  `S05_Lem5_06_adjacentTranspositionsInYoungsBasis_coxeterModel`.
- Lemma 5.7 diagonal content eigenspaces:
  `S05_Lem5_07_tableauContentSequence_injective` and
  `S05_Lem5_07_diagonalContentEigenspaces`.
- Lemma 5.36 tableauDim z-bound certificate:
  `S05_Lem5_36_tableau_weightZeroEntries_never_majority`.
- Lemma 5.38 tableauDim even certificate:
  `S05_Lem5_38_tableau_even_certificate`.
- Lemma 5.40 tableauDim odd certificate:
  `S05_Lem5_40_tableau_odd_certificate`.
- Lemma 5.19 tableauDim two-strip dimension recursion:
  `S05_Lem5_19_tableauDim_twoStrip_branching_sized`.
- Lemma 5.20 tableauDim one-box dimension recursion:
  `S05_Lem5_20_tableauDim_oneBoxChildrenOdd_branching`.
- Dimension-parameterized spectral bridge algebra:
  `SpectralGapFromBlockScalarsWithDim` and
  `SpectralGapFromBlockModelWithDim`.

External Appendix A inputs:

- A.1 Young orthogonal realization:
  `AppA_ThmA_01_youngOrthogonalRealization`.
- A.2 Jucys--Murphy content spectrum:
  `AppA_ThmA_02_jucysMurphyContentSpectrum`.
- A.3 degree-one Young-block identification:
  `AppA_LemA_03_degreeOneYoungBlockIdentification`.
- A.4 standard-tableau swap connectedness:
  `AppA_LemA_04_standardTableauxSwapConnectedness`.

Internal Section 5 assembly:

- Lemma 5.32 regular Young-block decomposition:
  `spectralBlockModelInputWithDim_even_from_appA_inputs` and
  `spectralBlockModelInputWithDim_odd_from_appA_inputs` are proved from the
  A.1/A.2/A.3/A.4 external ingredients.

Remaining Section 5/AppA bridge boundary:

- Lemmas 5.33 and 5.34 prove the tableau-count algebraic bridge from an
  explicit `SpectralBlockModelInputWithDim` hypothesis for the `tableauDim`
  model with `hEvenTableau` and `hOddTableau` heights.
- Lemma 5.32 supplies the `SpectralBlockModelInputWithDim` / spectral-block
  model input for the paper application from Appendix A ingredients.
- Appendix A representation theory supplies the intended bridge: regular
  Specht-block decomposition, `U_1` identification, matching-average scalarity,
  trace/scalar value, and the matching-restriction data needed to instantiate
  the spectral-block model.
- The concrete Lemma 5.23 matching-cube operator/character/projection algebra
  is proved; the representation-theoretic Specht/Pieri content it shadows is
  accounted for inside the spectral-block model boundary rather than as a
  separate Lean axiom.

Implementation hygiene update: `hEvenTableau` and `hOddTableau` now live in the
definition-only files `S05_Def_TableauEvenHeight.lean` and
`S05_Def_TableauOddHeight.lean`.  Thus
`AppA_ThmA_02_JucysMurphyContentSpectrum.lean` imports neutral definitions
rather than the even/odd certificate proof files.

- Two substantial helper layers are exposed in the dependency graph for
  readability, but are not numbered separately in the paper:
  `Aux_StandardYoungTableaux.lean` for deletion/insertion tableau mechanics and
  `Aux_YoungMatchingOperators.lean` for canonical matching-edge operator
  algebra.

Obsolete old routes:

- No active file is classified as obsolete.  The older `youngDim` variants of
  Lemmas 5.35, 5.37, and 5.39 remain in their paper files for compatibility and
  for the original Specht-dimension route.  They now require explicit
  `TwoStripDimensionBranchingAssumption` and/or
  `OneBoxDimensionBranchingPositiveAssumption` hypotheses; no axiom instance is
  registered for those assumptions.  The current proof-status tables promote
  the tableau-count statements.
- The active helper files for local convolution and spectral certificate
  algebra are `Aux_PMConvolution.lean` and
  `Aux_SpectralBridgeFromCertificates.lean`.

## Lemma 5.6 Young Adjacent Action Status

Lemma 5.6 now has an axiom-free coordinate Coxeter model in Lean.

Proved internally:

- `Aux_YoungOrthogonal.lean` defines the tableau coordinate space, basis
  vectors, Young adjacent matrix coefficients, and `youngAdjacentOperator`.
- The paper-facing file
  `S05_Lem5_06_AdjacentTranspositionsInYoungsBasis.lean` exposes the
  same-row, same-column, and swappable two-by-two Young adjacent matrix
  formulas.
- The swappable block has a positive/nonzero off-diagonal coefficient and
  nonzero `+1` and `-1` eigenvectors.
- The concrete adjacent operators satisfy the Coxeter relations on the full
  tableau coordinate space:
  `youngAdjacentOperator_sq`,
  `youngAdjacentOperator_comm_of_disjoint_indices`, and
  `youngAdjacentOperator_braid_of_succ`.
- `Aux_YoungAdjacentAction.lean` packages these operators as
  `YoungAdjacentActionModel`, defines adjacent words and
  `youngAdjacentWordOperator`, proves invariance under the elementary Coxeter
  word moves, defines the adjacent-word permutation shadow `adjacentWordPerm`,
  and descends both the operator and permutation shadow to the formal quotient
  `AdjacentCoxeterClass`.
- The strongest paper-facing package currently exposed is
  `S05_Lem5_06_adjacentTranspositionsInYoungsBasis_coxeterModel`.

Not proved, and not claimed:

- The coordinate model has not been identified with the classical Specht module
  or irreducible Young orthogonal representation.
- There is no full action of `Equiv.Perm (Fin (n+1))` on `TableauSpace lam`
  defined from arbitrary permutations.  The precise missing theorem is the
  type-A symmetric-group Coxeter presentation/Matsumoto theorem for adjacent
  words, or a mathlib `CoxeterSystem (CoxeterMatrix.A n)
  (Equiv.Perm (Fin (n+1)))` interface connecting the adjacent-word quotient to
  permutations.

## TableauDim Migration Status

The tableau-count recursion track has now proved the internal two-strip and
one-box dimension recurrences for `tableauDim`, not for the hook-length proxy
`youngDim`.

Current tableau-count finite-certificate status:

| Certificate layer | Tableau-count status | Active theorem path status |
| --- | --- | --- |
| Lemma 5.36, z-bound | Proved as `S05_Lem5_36_tableau_weightZeroEntries_never_majority` and `zEven_le_tableauDim` | Consumed by the dimension-parameterized bridge once a tableauDim spectral model is supplied |
| Lemma 5.38, even certificate | Proved as `S05_Lem5_38_tableau_even_certificate` using `hEvenTableau` and all four exceptional families | Connected by `S05_Lem5_33_tableauDim_evenSpectralGapFromCertificates` |
| Lemma 5.40, odd certificate | Proved as `S05_Lem5_40_tableau_odd_certificate` using `hOddTableau` and the tableau one-box branching theorem | Connected by `S05_Lem5_34_tableauDim_oddSpectralGapFromCertificates` |

The bridge algebra is no longer hard-coded to `youngDim`: the file
`Aux_SpectralBridgeDimensionParam.lean` defines
`SpectralBlockModelInputWithDim` and proves the scalar lower-bound and
spectral-gap wrappers for an arbitrary dimension function.  Lemmas 5.31--5.34
expose these wrappers for the paper-facing interface.

Active path note: Theorem 4.10 now uses the dimension-parametric `tableauDim`
interface through Lemmas 5.32--5.34.  The remaining Section 5 mathematical
input for this active route is the tableauDim spectral block model itself:
Young-block decomposition, `U_1` identification, matching-average scalarity,
and trace/scalar value with block dimension `tableauDim`.

The newest internal representation-layer objects are still coordinate-level:
they give a concrete Young adjacent Coxeter model, not a formal Specht-module
realization.  Schur-lemma scalarity and the spectral block model remain outside
Lemma 5.6 and are tracked separately below.

## Section 5 Paper/Lean Status Table

The current Section 5 source has 40 numbered paper-facing statements when
remarks and Appendix A inputs are excluded.  The paper-facing Lean files also
number 40.  The full statement-to-file map is maintained in
`DictatorshipTesting/Paper/SECTION5_FILE_MAP.md`; the four Appendix A external
inputs are mapped in `DictatorshipTesting/Paper/APPENDIX_A_FILE_MAP.md`.

The most important numbering corrections after the Lemma 5.6 rewrite are:

- Definitions 5.1--5.5 are the numbered tableau-preliminary interfaces,
  represented by `S05_Def5_01_YoungDiagramsAndBoxes.lean` through
  `S05_Def5_05_ContentAndAdjacentOperators.lean`.
- Lemma 5.6 is the explicit tableau Coxeter model, represented by
  `S05_Lem5_06_AdjacentTranspositionsInYoungsBasis.lean`.
- The two-box and one-box dimension recursions are Lemmas 5.19 and 5.20,
  represented by `S05_Lem5_19_TwoBoxDimensionRecursion.lean` and
  `S05_Lem5_20_OneBoxDimensionRecursion.lean`.
- The spectral bridge is split across Lemmas 5.31--5.34, with the remaining
  representation-layer input exposed by the named Appendix A ingredient
  axioms and the Lemma 5.32 assembly theorem.

## External Axiom Declarations

### Theorem 2.1 Boolean `U_1` Classification

Paper statement: Theorem 2.1 (`thm:boolean-u1`).

Lean file: `DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean`

Lean theorem name: `booleanU1_dictator_classification_input`

Current status: named external axiom.

Mathematical content: for `3 <= n`, every Boolean function on `S_n` whose real
indicator lies in the degree-one space `U_1` is a dictator.

Why it is external or why it should be proven: this is the nontrivial
classification theorem for Boolean degree-one functions on the symmetric group.
The small cases `n = 1, 2` and the converse direction are proved directly in
Lean.

Citation target if external: Filmus, *Boolean functions on `S_n` which are
nearly linear*, Discrete Analysis 2021:25, Theorem 2.8.

Downstream dependencies: `Thm2_1_BooleanU1` is the paper-facing wrapper.  No
active downstream Lean proof currently invokes this theorem directly; it
records the paper's structural classification input and is also part of the
citation context for the FKN/stability input.

### Theorem 2.2 FKN Stability

Paper statement: Theorem 2.2 (`thm:fkn-input`).

Lean file: `DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean`

Lean theorem name: `fknStability_input`

Current status: named external axiom.

Mathematical content: an FKN-type stability theorem on `S_n`, giving a positive
constant `cFKN` such that distance to dictators is controlled by distance to
`U_1`, in the `4 <= n` range used downstream.

Why it is external or why it should be proven: this is a literature theorem,
not part of the finite Section 5 certificate.

Citation target if external: Filmus, *Boolean functions on `S_n` which are
nearly linear*, Discrete Analysis 2021:25, Theorem 1.5, together with the
Boolean linear classification in Theorem 2.8 and the standard balanced-case
reduction recorded in the paper.

Downstream dependencies: `L4_13_OneTrialSoundness` consumes
`Thm2_2_FKNInput`, and `Thm1_1_MainIntro` consumes Lemma 4.13.

## Additional Paper-Level Obligations Without Registered Axioms

### Older `youngDim` Two-Box Dimension Branching Alternative

Current paper statement: Lemma 5.19 (`lem:dimension-two-strip-recurrence`) is
represented by the proved `tableauDim` wrapper
`S05_Lem5_19_tableauDim_twoStrip_branching_sized`.

Lean file: `DictatorshipTesting/Paper/S05_Lem5_19_TwoBoxDimensionRecursion.lean`

Older alternative Lean names: `TwoStripDimensionBranchingAssumption`,
`youngDim_twoStrip_branching_input`.

Current status: no axiom is registered.  The older `youngDim` wrapper is a
theorem with an explicit `[TwoStripDimensionBranchingAssumption]` hypothesis and
is not part of the current tableau-count proof spine.

Mathematical content: for `lambda |- 2m`, the Young dimension satisfies the
two-strip recursion
`d_lambda = sum_{horizontal two-strip children} d_mu
          + sum_{vertical two-strip children} d_mu`.

Why the older route is external: this is the dimension shadow of
Specht-module restriction via the two-strip Pieri/Littlewood--Richardson rule.
It should become internal only after a formal Specht-module/branching library is
available.

Citation target if external: James--Kerber, *The Representation Theory of the
Symmetric Group*, Section 2.8.13; Bowman--De Visscher--Orellana,
arXiv:1210.5579, Theorem 1.1 and the paragraph following it; Sagan,
*The Symmetric Group*, for the Pieri/Littlewood--Richardson background.

Downstream dependencies: only older `youngDim` alternatives such as
`L5_4_ZBoundApp`, `L5_5_HEvenApp`, and related compatibility wrappers carry
`[TwoStripDimensionBranchingAssumption]`.  The promoted Lemmas 5.14, 5.30, and
5.32 use `tableauDim` and do not need it.

### Older `youngDim` One-Box Dimension Branching Alternative

Current paper statement: Lemma 5.20 (`lem:dimension-one-box-recurrence`) is
represented by the proved `tableauDim` wrapper
`S05_Lem5_20_tableauDim_oneBoxChildrenOdd_branching`.

Lean file: `DictatorshipTesting/Paper/S05_Lem5_20_OneBoxDimensionRecursion.lean`

Older alternative Lean names:
`OneBoxDimensionBranchingPositiveAssumption`,
`youngDim_oneBox_branching_positive_input`,
`youngDim_oneBox_branching_input`.

Current status: no axiom is registered.  The older positive-range `youngDim`
wrapper is a theorem with an explicit
`[OneBoxDimensionBranchingPositiveAssumption]` hypothesis.  The `m = 0` and
`m = 1` cases are proved directly.

Mathematical content: for `lambda |- 2m+1`, the Young dimension is the sum of
the dimensions of its one-box children.

Why the older route is external: this is the ordinary branching rule for Specht
modules.  The remaining positive-range proof needs formal Specht-module
infrastructure.

Citation target if external: ordinary Specht-module branching rule, e.g. Sagan,
*The Symmetric Group*, Section 2.8, or James--Kerber.

Downstream dependencies: only older `youngDim` alternatives such as
`L5_6_HOddApp` and related compatibility wrappers carry
`[OneBoxDimensionBranchingPositiveAssumption]`.  The promoted Lemmas 5.20 and
5.40 use `tableauDim` and do not need it.

### Lemmas 5.31--5.34 Spectral Block Model Families

Paper statements: Lemma 5.31 block lower bound, Lemma 5.32 regular Young-block
decomposition assembly, Lemma 5.33 even spectral bridge, and Lemma 5.34 odd
spectral bridge, together with the Young-block decomposition,
matching-average scalarity, and trace/scalar value inputs they use.

Lean files: `DictatorshipTesting/Paper/S05_Lem5_31_BlockLowerBoundImpliesTheGap.lean`,
`DictatorshipTesting/Paper/S05_Lem5_32_RegularYoungBlockDecomposition.lean`,
`DictatorshipTesting/Paper/S05_Lem5_33_EvenSpectralBridge.lean`,
`DictatorshipTesting/Paper/S05_Lem5_34_OddSpectralBridge.lean`,
`DictatorshipTesting/Paper/Aux_SpectralBridgeFromCertificates.lean`,
and `DictatorshipTesting/Paper/Aux_SpectralBridgeDimensionParam.lean`.

Lean names consumed downstream:
`spectralBlockModelInputWithDim_even_from_appendixA`,
`spectralBlockModelInputWithDim_odd_from_appendixA`,
and `SpectralBlockModelInputWithDim`.

Raw Appendix A axiom declarations:
`AppA_ThmA_01_youngOrthogonalRealization`,
`AppA_ThmA_02_jucysMurphyContentSpectrum`,
`AppA_LemA_03_degreeOneYoungBlockIdentification`,
and `AppA_LemA_04_standardTableauxSwapConnectedness`.

Current status: named external axioms, not `sorry` declarations.  Together with
the two Section 2 Filmus inputs, these are the only remaining axiom
declarations.

Mathematical content: the regular representation decomposes `F` into
nonnegative Young-block energies whose non-`U_1` sum is `l2DistSqToU1 F`;
Schur's lemma gives matching-average scalars on those blocks; and the scalar
trace formula identifies those scalars as
`hEvenTableau m lambda / tableauDim lambda` in the even case and
`hOddTableau m lambda / tableauDim lambda` in the odd case.

Why it is external or why it should be proven: the finite weighted-sum
comparison and trace-divided-by-dimension algebra are formalized, but the
actual Young-block decomposition of `L^2(S_n)`, compatibility of those energies
with `U_1`, scalarity of the matching-average operator, tableau-count dimension
positivity inside the spectral model, and the trace/scalar identification
require the unformalized Specht-block model, conjugation-invariance argument,
Schur's lemma, and matching-restriction theorem.

Citation target if external: regular representation/Specht decomposition and
Schur's lemma from standard finite-group representation theory; the
Littlewood--Richardson restriction theorem for Specht modules to Young
subgroups from James--Kerber, Section 2.8.13, as quoted in
Bowman--De Visscher--Orellana, arXiv:1210.5579, Theorem 1.1 and the paragraph
following it; Pieri special cases for the two-strip matching-subgroup chain.

Downstream dependencies: `Thm4_10_MatchingGap`,
`Prop4_12_SquareEnergyControlsGlobalDegree`, `L4_13_OneTrialSoundness`, and
`Thm1_1_MainIntro`, which use the named dimension-parameterized Appendix A
spectral block model theorem wrappers through the tableauDim bridge.

### Lemma 5.23 Full Matching-Restriction/Pieri Statement

Paper statement: Lemma 5.23 (`lem:matching-restriction-X`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_23_MatchingSubgroupEigenbasis.lean`

Lean theorem names:
`matchingRestriction_even_specht_pieri_input`,
`matchingRestriction_odd_specht_pieri_input`.

Current status: the scalar/numerical shadow in Lean is proved; the full
paper-level Specht restriction statement is not formalized.

Mathematical content: restricting `S^lambda` to the matching subgroup
`A_M ~= (Z/2Z)^m` has the local character-weight multiset recursively counted
by the Section 5 `X_m(lambda)` data.

Why it is external or why it should be proven: the current Lean vocabulary does
not contain Specht modules or restriction functors.  The file therefore proves
only the scalar bounds needed by the scaffold, not the full representation
statement.

Citation target if external: repeated Pieri/Littlewood--Richardson branching
for restriction to Young subgroups and then to the matching subgroup.

Downstream dependencies: the trace/scalar-value inputs used by Lemmas
5.26--5.28.

## Proven Internal Components

- `S05_Lem5_24_LocalTruncationOnAMatchingCharacter.lean`: matching-cube
  character projection.
- `S05_Lem5_31_BlockLowerBoundImpliesTheGap.lean`:
  `blockScalar_lower_bound_of_traceScalarFormula`,
  `traceScalarValue_of_blockTraceIdentity`,
  `SpectralGapFromBlockScalars`,
  `SpectralGapFromBlockScalarLowerBounds`,
  `EvenSpectralGapFromCertificates`,
  `OddSpectralGapFromCertificates`,
  and `SpectralGapFromBlockModelWithDim` are proved algebraic implications.
- `S05_Lem5_33_EvenSpectralBridge.lean` and
  `S05_Lem5_34_OddSpectralBridge.lean`: tableau-count spectral bridges proved
  from explicit `SpectralBlockModelInputWithDim` hypotheses; Appendix A
  supplies those hypotheses for the paper application.
- `Aux_SpectralBridgeRepresentationInputs.lean`: compact interface definitions
  for the spectral-block model used by the Section 5 spectral bridge.
- `Aux_YoungOrthogonal.lean`: coordinate space on standard tableaux, basis
  vectors, basis inner product facts, concrete adjacent matrix coefficients,
  the adjacent operator on coordinates, the diagonal content operator,
  coefficient identities, self-adjointness on coordinate basis vectors, and the
  full distant-commutation relation for the concrete adjacent operators.
- `S05_Lem5_06_AdjacentTranspositionsInYoungsBasis.lean`: basis-level adjacent
  transposition facts, including same-row/same-column diagonal behavior and
  swappable two-coordinate support for the concrete coordinate operator.
- `S05_Lem5_07_DiagonalContentEigenspaces.lean`: basis-level content API,
  content-sequence injectivity, separation of distinct tableaux by a content
  coordinate, and the one-dimensional common eigenspaces of the explicit
  diagonal content operators.  The group-algebra Jucys--Murphy identification
  is the separate Appendix A.2 external input.
- `S05_Lem5_12_TwoBoxTableauBranching.lean`: fixed two-step deletion tableau
  branching through `S05_Lem5_12_twoStepDeletionTableauxEquivChildTableaux`,
  plus iterated deletion preservation of content, row, and column coordinates.
  This is a concrete tableau statement, not a Specht-module branching theorem.
- `S05_Lem5_15_OneBoxDeletionIsUnitary.lean`: set-level one-box
  deletion/insertion equivalence and coordinate inner-product preservation
  through `S05_Lem5_15_deletionCoordinateMap_inner`.
- `S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps.lean`: basis-level
  content preservation under maximum-entry deletion, earlier-adjacent
  matrix-coefficient preservation under one-box insertion through
  `S05_Lem5_16_insertMax_youngAdjacentMatrixCoeff`, coordinate-level
  Young-adjacent deletion-fiber intertwining through
  `S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines`, and
  coordinate-level diagonal-content intertwining through
  `S05_Lem5_16_deletionCoordinateMap_diagonalContent_intertwines`.
- `S05_Lem5_21_SizesOfTheSignPatternMultisets.lean`: scalar sign-pattern count
  recurrences and assumption-free `tableauDim` two-strip/one-box size wrappers
  through `S05_Lem5_21_tableauDim_twoStrip_size` and
  `S05_Lem5_21_tableauDim_oneBox_size`.  The older `youngDim` wrappers assume
  the named dimension-branching inputs.
- `S05_Lem5_23_MatchingSubgroupEigenbasis.lean`: concrete canonical
  matching-cube operator algebra, including fixed ordered-product wrappers and
  edge-sign product-to-character wrappers, plus preservation of other edge
  eigenvalues by one-edge projections through
  `S05_Lem5_23_matchingEdgePlusProjectionEven_preserves_otherEigen` and its
  even/odd plus/minus companions.  It also includes support-selected one-edge
  projection wrappers such as
  `S05_Lem5_23_matchingEdgeSignProjectionEven_isMatchingEigen`, and iterated
  support-selected simultaneous eigenspace wrappers such as
  `S05_Lem5_23_matchingSignProjectionEven_isMatchingEigenvector`.  The full
  Specht-module restriction theorem remains a representation-layer input.
- `S05_Def5_26_MatchingIdempotents.lean`: low/high matching idempotent
  vocabulary, including `S05_matchingLowIdempotent_idempotent` and
  `S05_matchingHighIdempotent_idempotent`, plus the complementary projection
  identities `S05_matchingLowIdempotent_high_eq_zero`,
  `S05_matchingHighIdempotent_low_eq_zero`, and
  `S05_matchingLow_add_matchingHigh`.
- `S05_Lem5_28_CentralAveragedRejection.lean`: finite-average local rejection
  identities, including the high-idempotent norm formula
  `S05_Lem5_28_matchingMeanProjectionError_eq_high_idempotent_average`.  The
  operator centrality refinement remains a representation-layer target.
- `S05_Lem5_31_BlockLowerBoundImpliesTheGap.lean`: weighted-sum spectral-gap
  algebra, including trace-model-to-gap wrappers
  `S05_Lem5_31_spectralGapFromBlockTraceModel` and
  `S05_Lem5_31_spectralGapFromBlockTraceModelWithDim`.
- `S05_Lem5_36_WeightZeroEntriesAreNeverAMajority.lean`: finite `zEven`
  certificate, with current tableau-count theorem
  `S05_Lem5_36_tableau_weightZeroEntries_never_majority`.  The older
  `youngDim` variant remains for the external Specht-dimension route.
- `S05_Lem5_38_EvenCertificate.lean`: finite even certificate, with both the
  current tableau-count theorem `S05_Lem5_38_tableau_even_certificate` and an
  older `hEven`/`youngDim` variant for the external Specht-dimension route.
- `S05_Lem5_40_OddCertificate.lean`: finite odd certificate, with both the
  current tableau-count theorem `S05_Lem5_40_tableau_odd_certificate` and an
  older `hOdd`/`youngDim` variant for the external Specht-dimension route.

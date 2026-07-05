# Proof Obligation Ledger

This ledger tracks mathematical obligations, not just the raw number of
`sorry`s.  A `sorry` is acceptable here only when the named declaration states a
precise external theorem or a precise internal theorem still intended for Lean.

Current classification:

- External standard inputs: Section 2 structural/stability theorems, explicit
  Specht dimension-branching hypotheses, and the representation-theoretic
  pieces of the Section 5 spectral bridge.
- Internal finite certificates: Lemmas 5.30, 5.32, and 5.34 have
  tableau-count versions proved in Lean.  The legacy `youngDim` variants still
  depend on the named dimension-branching inputs.
- Internal open finite certificates: none currently listed.

## Lemma 5.1 Young Adjacent Action Status

Lemma 5.1 now has an axiom-free coordinate Coxeter model in Lean.

Proved internally:

- `Aux_YoungOrthogonal.lean` defines the tableau coordinate space, basis
  vectors, Young adjacent matrix coefficients, and `youngAdjacentOperator`.
- The paper-facing file
  `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` exposes the
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
  `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel`.

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
| Lemma 5.30, z-bound | Proved as `S05_Lem5_30_tableau_weightZeroEntries_never_majority` and `zEven_le_tableauDim` | Consumed by the dimension-parameterized bridge once a tableauDim spectral model is supplied |
| Lemma 5.32, even certificate | Proved as `S05_Lem5_32_tableau_even_certificate` using `hEvenTableau` and all four exceptional families | Connected by `S05_Lem5_27_tableauDim_evenSpectralGapFromCertificates` |
| Lemma 5.34, odd certificate | Proved as `S05_Lem5_34_tableau_odd_certificate` using `hOddTableau` and the tableau one-box branching theorem | Connected by `S05_Lem5_28_tableauDim_oddSpectralGapFromCertificates` |

The bridge algebra is no longer hard-coded to `youngDim`: the file
`Aux_SpectralBridgeDimensionParam.lean` defines
`SpectralBlockModelInputWithDim` and proves the scalar lower-bound and
spectral-gap wrappers for an arbitrary dimension function.  Lemmas 5.26--5.28
expose these wrappers for the paper-facing interface.

Precise active-path blocker: Theorem 4.10 still uses the old `youngDim`
spectral model and has not yet been rewired through the new dimension-parametric
interface.  The remaining Section 5 mathematical input is the tableauDim
spectral block model itself: Young-block decomposition, `U_1` identification,
matching-average scalarity, and trace/scalar value with block dimension
`tableauDim`.

The newest internal representation-layer objects are still coordinate-level:
they give a concrete Young adjacent Coxeter model, not a formal Specht-module
realization.  Schur-lemma scalarity and the spectral block model remain outside
Lemma 5.1 and are tracked separately below.

## Section 5 Paper/Lean Status Table

The current Section 5 source has 34 theorem-like numbered statements when
remarks and Appendix A inputs are excluded.  The paper-facing Lean files also
number 34.  The full statement-to-file map is maintained in
`DictatorshipTesting/Paper/SECTION5_FILE_MAP.md`; the five Appendix A external
inputs are mapped in `DictatorshipTesting/Paper/APPENDIX_A_FILE_MAP.md`.

The most important numbering corrections after the Lemma 5.1 rewrite are:

- Lemma 5.1 is the explicit tableau Coxeter model, represented by
  `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean`.
- The two-box and one-box dimension recursions are Lemmas 5.14 and 5.15,
  represented by `S05_Lem5_14_TwoBoxDimensionRecursion.lean` and
  `S05_Lem5_15_OneBoxDimensionRecursion.lean`.
- The spectral bridge is split across Lemmas 5.26--5.28, with the remaining
  representation-layer input exposed by named spectral-block model axioms.

## Remaining `sorry` Declarations

### Theorem 2.1 Boolean `U_1` Classification

Paper statement: Theorem 2.1 (`thm:boolean-u1`).

Lean file: `DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean`

Lean theorem name: `booleanU1_dictator_classification_input`

Current status: external input.

Mathematical content: for `3 <= n`, every Boolean function on `S_n` whose real
indicator lies in the degree-one space `U_1` is a dictator.

Why it is external or why it should be proven: this is the nontrivial
classification theorem for Boolean degree-one functions on the symmetric group.
The small cases `n = 1, 2` and the converse direction are proved directly in
Lean.

Citation target if external: Filmus, *Boolean functions on `S_n` which are
nearly linear*, Discrete Analysis 2021:25, Theorem 2.8.

Downstream dependencies: `Thm2_1_BooleanU1`, perfect completeness and final
dictatorship-testing theorem statements.

### Theorem 2.2 FKN Stability

Paper statement: Theorem 2.2 (`thm:fkn-input`).

Lean file: `DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean`

Lean theorem name: `fknStability_input`

Current status: external input.

Mathematical content: an FKN-type stability theorem on `S_n`, giving a positive
constant `cFKN` such that distance to dictators is controlled by distance to
`U_1`, in the `4 <= n` range used downstream.

Why it is external or why it should be proven: this is a literature theorem,
not part of the finite Section 5 certificate.

Citation target if external: Filmus, *Boolean functions on `S_n` which are
nearly linear*, Discrete Analysis 2021:25, Theorem 1.5, together with the
Boolean linear classification in Theorem 2.8 and the standard balanced-case
reduction recorded in the paper.

Downstream dependencies: one-trial soundness and the main theorem.

## Paper-Level Obligations Without a Current `sorry`

### Lemma 5.14 Two-Box Dimension Branching

Paper statement: Lemma 5.14 (`lem:dimension-two-strip-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_14_TwoBoxDimensionRecursion.lean`

Lean names: `twoStripDimensionBranchingAssumption_from_specht_pieri`,
`TwoStripDimensionBranchingAssumption`,
`youngDim_twoStrip_branching_input`.

Current status: named external axiom/instance, not a `sorry` declaration.

Mathematical content: for `lambda |- 2m`, the Young dimension satisfies the
two-strip recursion
`d_lambda = sum_{horizontal two-strip children} d_mu
          + sum_{vertical two-strip children} d_mu`.

Why it is external or why it should be proven: this is the dimension shadow of
Specht-module restriction via the two-strip Pieri/Littlewood--Richardson rule.
It should become internal only after a formal Specht-module/branching library is
available.

Citation target if external: James--Kerber, *The Representation Theory of the
Symmetric Group*, Section 2.8.13; Bowman--De Visscher--Orellana,
arXiv:1210.5579, Theorem 1.1 and the paragraph following it; Sagan,
*The Symmetric Group*, for the Pieri/Littlewood--Richardson background.

Downstream dependencies: finite certificates `L5_4_ZBoundApp` and
`L5_5_HEvenApp`, which now carry `[TwoStripDimensionBranchingAssumption]`.

### Lemma 5.15 One-Box Dimension Branching

Paper statement: Lemma 5.15 (`lem:dimension-one-box-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_15_OneBoxDimensionRecursion.lean`

Lean names:
`oneBoxDimensionBranchingPositiveAssumption_from_specht_branching`,
`OneBoxDimensionBranchingPositiveAssumption`,
`youngDim_oneBox_branching_positive_input`,
`youngDim_oneBox_branching_input`.

Current status: named external axiom/instance for `2 <= m`, not a `sorry`
declaration.  The `m = 0` and `m = 1` cases are proved directly.

Mathematical content: for `lambda |- 2m+1`, the Young dimension is the sum of
the dimensions of its one-box children.

Why it is external or why it should be proven: this is the ordinary branching
rule for Specht modules.  The remaining positive-range proof needs formal
Specht-module infrastructure.

Citation target if external: ordinary Specht-module branching rule, e.g. Sagan,
*The Symmetric Group*, Section 2.8, or James--Kerber.

Downstream dependencies: finite certificate `L5_6_HOddApp`, which now carries
`[OneBoxDimensionBranchingPositiveAssumption]`.

### Lemmas 5.26--5.28 Spectral Block Model Families

Paper statements: Lemma 5.26 block lower bound, Lemma 5.27 even spectral
bridge, and Lemma 5.28 odd spectral bridge, together with the Young-block
decomposition, matching-average scalarity, and trace/scalar value inputs they
use.

Lean files: `DictatorshipTesting/Paper/S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean`,
`DictatorshipTesting/Paper/S05_Lem5_27_EvenSpectralBridge.lean`,
`DictatorshipTesting/Paper/S05_Lem5_28_OddSpectralBridge.lean`,
`DictatorshipTesting/Paper/Aux_SpectralBridgeFromCertificates_Legacy.lean`,
and `DictatorshipTesting/Paper/Aux_SpectralBridgeDimensionParam.lean`.

Lean names: `spectralBlockModelInput_even_from_specht_pieri_schur`,
`spectralBlockModelInput_odd_from_specht_pieri_schur`,
`SpectralBlockModelInput`, `EvenSpectralBlockModelFamily`,
`OddSpectralBlockModelFamily`.

Current status: named external axioms, not `sorry` declarations.

Mathematical content: the regular representation decomposes `F` into
nonnegative Young-block energies whose non-`U_1` sum is `l2DistSqToU1 F`;
Schur's lemma gives matching-average scalars on those blocks; and the scalar
trace formula identifies those scalars as `hEven m lambda / d_lambda` in the
even case and `hOdd m lambda / d_lambda` in the odd case.

Why it is external or why it should be proven: the finite weighted-sum
comparison and trace-divided-by-dimension algebra are formalized, but the
actual Young-block decomposition of `L^2(S_n)`, compatibility of those energies
with `U_1`, scalarity of the matching-average operator, Young-dimension
positivity inside the spectral model, and the trace/scalar identification
require the unformalized Specht-block model, conjugation-invariance argument,
Schur's lemma, and matching-restriction theorem.

Citation target if external: regular representation/Specht decomposition and
Schur's lemma from standard finite-group representation theory; the
Littlewood--Richardson restriction theorem for Specht modules to Young
subgroups from James--Kerber, Section 2.8.13, as quoted in
Bowman--De Visscher--Orellana, arXiv:1210.5579, Theorem 1.1 and the paragraph
following it; Pieri special cases for the two-strip matching-subgroup chain.

Downstream dependencies: `L5_2_SpectralCertificate`,
`Thm4_10_MatchingGap`, `Prop4_12_SquareEnergyControlsGlobalDegree`,
`L4_13_OneTrialSoundness`, and `Thm1_1_MainIntro`, which now use the named
external spectral block model axioms directly.

### Lemma 5.18 Full Matching-Restriction/Pieri Statement

Paper statement: Lemma 5.18 (`lem:matching-restriction-X`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_18_MatchingSubgroupEigenbasis.lean`

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

- `S05_Lem5_19_LocalTruncationOnAMatchingCharacter.lean`: matching-cube
  character projection.
- `S05_Lem5_20_TraceOfOneLocalTruncationOnOneYoungBlock.lean`: local trace formula in the current
  scalar vocabulary, conditional on the scalar matching-restriction data.
- `S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean`: trace-divided-by-dimension
  scalar algebra.
- `S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean`,
  `S05_Lem5_27_EvenSpectralBridge.lean`, and
  `S05_Lem5_28_OddSpectralBridge.lean`:
  `blockScalar_lower_bound_of_traceScalarFormula`,
  `traceScalarValue_of_blockTraceIdentity`,
  `SpectralGapFromBlockScalars`,
  `SpectralGapFromBlockScalarLowerBounds`,
  `EvenSpectralGapFromCertificates`,
  `OddSpectralGapFromCertificates`,
  `SpectralGapFromBlockModelWithDim`,
  `S05_Lem5_27_tableauDim_evenSpectralGapFromCertificates`, and
  `S05_Lem5_28_tableauDim_oddSpectralGapFromCertificates` are proved from the
  explicit inputs above.
- `Aux_SpectralBridgeRepresentationInputs.lean`: compact interface definitions
  for the spectral-block model used by the Section 5 spectral bridge.
- `Aux_YoungOrthogonal.lean`: coordinate space on standard tableaux, basis
  vectors, basis inner product facts, concrete adjacent matrix coefficients,
  the adjacent operator on coordinates, the diagonal content operator,
  coefficient identities, self-adjointness on coordinate basis vectors, and the
  full distant-commutation relation for the concrete adjacent operators.
- `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean`: basis-level adjacent
  transposition facts, including same-row/same-column diagonal behavior and
  swappable two-coordinate support for the concrete coordinate operator.
- `S05_Lem5_02_DiagonalContentEigenspaces.lean`: basis-level content API,
  content-sequence injectivity, separation of distinct tableaux by a content
  coordinate, and the one-dimensional common eigenspaces of the explicit
  diagonal content operators.  The group-algebra Jucys--Murphy identification
  is the separate Appendix A.2 external input.
- `S05_Lem5_07_TwoBoxTableauBranching.lean`: fixed two-step deletion tableau
  branching through `S05_Lem5_07_twoStepDeletionTableauxEquivChildTableaux`,
  plus iterated deletion preservation of content, row, and column coordinates.
  This is a concrete tableau statement, not a Specht-module branching theorem.
- `S05_Lem5_10_OneBoxDeletionIsUnitary.lean`: set-level one-box
  deletion/insertion equivalence and coordinate inner-product preservation
  through `S05_Lem5_10_deletionCoordinateMap_inner`.
- `S05_Lem5_11_OneBoxDeletionIntertwinesEarlierSwaps.lean`: basis-level
  content preservation under maximum-entry deletion and coordinate-level
  diagonal-content intertwining through
  `S05_Lem5_11_deletionCoordinateMap_diagonalContent_intertwines`.  The full
  Young-adjacent-operator intertwining statement remains open.
- `S05_Lem5_30_WeightZeroEntriesAreNeverAMajority.lean`: finite `zEven`
  certificate, with both the legacy `youngDim` theorem and the tableau-count
  theorem `S05_Lem5_30_tableau_weightZeroEntries_never_majority`.
- `S05_Lem5_32_EvenCertificate.lean`: finite even certificate, with both the
  legacy `hEven`/`youngDim` theorem and the tableau-count theorem
  `S05_Lem5_32_tableau_even_certificate`.
- `S05_Lem5_34_OddCertificate.lean`: finite odd certificate, with both the
  legacy `hOdd`/`youngDim` theorem and the tableau-count theorem
  `S05_Lem5_34_tableau_odd_certificate`.

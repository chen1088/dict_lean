# Proof Obligation Ledger

This ledger tracks mathematical obligations, not just the raw number of
`sorry`s.  A `sorry` is acceptable here only when the named declaration states a
precise external theorem or a precise internal theorem still intended for Lean.

Current classification:

- External standard inputs: Section 2 structural/stability theorems, explicit
  Specht dimension-branching hypotheses, and the representation-theoretic
  pieces of the Section 5 spectral bridge.
- Internal finite certificates: Lemmas 5.10, 5.12, and 5.14 are proved in Lean
  modulo the dimension branching inputs.
- Internal open finite certificates: none currently listed.

## Section 5 Paper/Lean Status Table

| Paper statement number | Paper label/title | Lean file | Lean theorem name | Status | Remaining assumption, if any |
| --- | --- | --- | --- | --- | --- |
| Lemma 5.1 | `lem:dimension-two-strip-recurrence`, Dimension recursion | `S05_Lem5_01_TwoStripDimensionRecursion.lean` | `youngDim_twoStrip_branching_input` | external standard input | `twoStripDimensionBranchingAssumption_from_specht_pieri`, from Specht/Pieri/Littlewood--Richardson branching |
| Lemma 5.2 | `lem:dimension-one-box-recurrence`, One-box dimension recursion | `S05_Lem5_02_OneBoxDimensionRecursion.lean` | `youngDim_oneBox_branching_input` | external standard input for `2 <= m`; small cases proved | `oneBoxDimensionBranchingPositiveAssumption_from_specht_branching`, ordinary Specht branching |
| Lemma 5.3 | `lem:matching-restriction-X`, Restriction to matching subgroup | `S05_Lem5_03_MatchingRestrictionPieri.lean` | `matchingRestriction_even_specht_pieri_input`, `matchingRestriction_odd_specht_pieri_input` | scalar shadow proven from finite certificates; full Specht statement external | full Specht/Pieri restriction to `A_M`, represented downstream by the spectral block model input |
| Lemma 5.4 | `lem:PM-character-projection`, Local truncation as character projection | `S05_Lem5_04_LocalTruncationCharacterProjection.lean` | `matchingLocalProjection_preserves_low_local_char`, `matchingLocalProjection_kills_high_local_char` | proven | none |
| Lemma 5.5 | `lem:PM-trace-young-block`, Trace of one local truncation | `S05_Lem5_05_TraceLocalTruncation.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | algebraic/scalar wrapper | full Young-block trace interpretation belongs to the spectral block model input |
| Lemma 5.6 | `lem:centralization-matchings`, Centralization over matchings | `S05_Lem5_06_CentralizationOverMatchings.lean` | `centralizationBridge_scalar_eq_trace_div_dimension`, `centralizationBridge_even_scalar_eq_hEven_div_dim`, `centralizationBridge_odd_scalar_eq_hOdd_div_dim` | trace-divided-by-dimension algebra proven | Young-block scalarity by Schur's lemma belongs to the spectral block model input |
| Lemma 5.8 | `lem:spectral-certificate`, Spectral bridge from finite certificate | `S05_Lem5_08_SpectralBridgeFromCertificates.lean` | `SpectralGapFromBlockScalarLowerBounds`, `L5_2_SpectralCertificate` | algebraic wrapper proven | `spectralBlockModelInput_even_from_specht_pieri_schur`, `spectralBlockModelInput_odd_from_specht_pieri_schur` |
| Lemma 5.10 | `lem:z-bound-app`, Weight-zero bound | `S05_Lem5_10_ZBoundCertificate.lean` | `L5_4_ZBoundApp` | proven modulo Lemma 5.1 | two-strip dimension branching |
| Lemma 5.12 | `lem:h-even-app`, Even certificate | `S05_Lem5_12_EvenHCertificate.lean` | `L5_5_HEvenApp` | proven modulo Lemma 5.1 and Lemma 5.10 | two-strip dimension branching |
| Lemma 5.14 | `lem:h-odd-app`, Odd certificate | `S05_Lem5_14_OddHCertificate.lean` | `L5_6_HOddApp` | proven modulo Lemma 5.2 and Lemma 5.12 | one-box dimension branching and two-strip dimension branching |

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

### Lemma 5.1 Two-Strip Dimension Branching

Paper statement: Lemma 5.1 (`lem:dimension-two-strip-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_01_TwoStripDimensionRecursion.lean`

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

### Lemma 5.2 One-Box Dimension Branching

Paper statement: Lemma 5.2 (`lem:dimension-one-box-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_02_OneBoxDimensionRecursion.lean`

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

### Lemma 5.8 Spectral Block Model Families

Paper statement: Lemma 5.8 spectral bridge, Young-block decomposition,
matching-average scalarity, and trace/scalar value.

Lean file: `DictatorshipTesting/Paper/S05_Lem5_08_SpectralBridgeFromCertificates.lean`

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

### Lemma 5.3 Full Matching-Restriction/Pieri Statement

Paper statement: Lemma 5.3 (`lem:matching-restriction-X`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_03_MatchingRestrictionPieri.lean`

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

Downstream dependencies: the trace/scalar-value inputs in Lemma 5.8.

## Proven Internal Components

- `S05_Lem5_04_LocalTruncationCharacterProjection.lean`: matching-cube
  character projection.
- `S05_Lem5_05_TraceLocalTruncation.lean`: local trace formula in the current
  scalar vocabulary, conditional on the scalar matching-restriction data.
- `S05_Lem5_06_CentralizationOverMatchings.lean`: trace-divided-by-dimension
  scalar algebra.
- `S05_Lem5_08_SpectralBridgeFromCertificates.lean`:
  `blockScalar_lower_bound_of_traceScalarFormula`,
  `traceScalarValue_of_blockTraceIdentity`,
  `matchingAverageScalarModel_of_blockTraceModel`,
  `SpectralGapFromBlockScalars`,
  `SpectralGapFromBlockScalarLowerBounds`,
  `evenSpectralBlockModelFamily_from_specht_pieri_schur`,
  `oddSpectralBlockModelFamily_from_specht_pieri_schur`,
  `EvenSpectralGapFromCertificates`,
  `OddSpectralGapFromCertificates`,
  `matchingSpectralGap_of_even_young_certificate`,
  `matchingSpectralGap_of_odd_young_certificate`, and
  `L5_2_SpectralCertificate` are proved from the explicit inputs above.
- `Aux_SpectralBridgeRepresentationInputs.lean`: compact interface definitions
  for the spectral-block model used by Lemma 5.8.
- `S05_Lem5_10_ZBoundCertificate.lean`: finite `zEven` certificate, proved
  modulo Lemma 5.1.
- `S05_Lem5_12_EvenHCertificate.lean`: finite `hEven` certificate, proved
  modulo Lemma 5.1 and Lemma 5.10.
- `S05_Lem5_14_OddHCertificate.lean`: finite `hOdd` certificate, proved
  modulo Lemma 5.2 and Lemma 5.12.

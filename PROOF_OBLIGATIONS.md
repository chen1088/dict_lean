# Proof Obligation Ledger

This ledger tracks mathematical obligations, not just the raw number of
`sorry`s.  A `sorry` is acceptable here only when the named declaration states a
precise external theorem or a precise internal theorem still intended for Lean.

Current classification:

- External standard inputs: Section 2 structural/stability theorems, Specht
  dimension branching, and the representation-theoretic pieces of the Section 5
  spectral bridge.
- Internal finite certificates: Lemmas 5.10, 5.12, and 5.14 are proved in Lean
  modulo the dimension branching inputs.
- Internal open finite certificates: none currently listed.

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

Citation target if external: Ellis--Friedgut--Pilpel / Filmus, especially
Filmus Theorem 2.8.

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

Citation target if external: Filmus's FKN theorem on `S_n`, especially the
balanced theorem implying the stated corollary.

Downstream dependencies: one-trial soundness and the main theorem.

### Lemma 5.1 Two-Strip Dimension Branching

Paper statement: Lemma 5.1 (`lem:dimension-two-strip-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_01_TwoStripDimensionRecursion.lean`

Lean theorem name: `youngDim_twoStrip_branching_input`

Current status: external input.

Mathematical content: for `lambda |- 2m`, the Young dimension satisfies the
two-strip recursion
`d_lambda = sum_{horizontal two-strip children} d_mu
          + sum_{vertical two-strip children} d_mu`.

Why it is external or why it should be proven: this is the dimension shadow of
Specht-module restriction via the two-strip Pieri/Littlewood--Richardson rule.
It should become internal only after a formal Specht-module/branching library is
available.

Citation target if external: standard Specht-module branching and
Pieri/Littlewood--Richardson rule, e.g. Sagan or James--Kerber.

Downstream dependencies: finite certificates `L5_4_ZBoundApp` and
`L5_5_HEvenApp`.

### Lemma 5.2 One-Box Dimension Branching

Paper statement: Lemma 5.2 (`lem:dimension-one-box-recurrence`).

Lean file: `DictatorshipTesting/Paper/S05_Lem5_02_OneBoxDimensionRecursion.lean`

Lean theorem name: `youngDim_oneBox_branching_positive_input`

Current status: external input for `2 <= m`; the `m = 0` and `m = 1` cases are
proved directly.

Mathematical content: for `lambda |- 2m+1`, the Young dimension is the sum of
the dimensions of the one-box children.

Why it is external or why it should be proven: this is the ordinary branching
rule for Specht modules.  The remaining positive-range proof needs formal
Specht-module infrastructure.

Citation target if external: ordinary Specht-module branching rule, e.g. Sagan
or James--Kerber.

Downstream dependencies: finite certificate `L5_6_HOddApp`.

## Paper-Level Obligations Without a Current `sorry`

### Lemma 5.8 Spectral Block Model Families

Paper statement: Lemma 5.8 spectral bridge, Young-block decomposition,
matching-average scalarity, and trace/scalar value.

Lean file: `DictatorshipTesting/Paper/S05_Lem5_08_SpectralBridgeFromCertificates.lean`

Lean names: `SpectralBlockModelInput`, `EvenSpectralBlockModelFamily`,
`OddSpectralBlockModelFamily`.

Current status: explicit theorem hypotheses, not `sorry` declarations.

Mathematical content: the regular representation decomposes `F` into
nonnegative Young-block energies whose non-`U_1` sum is `l2DistSqToU1 F`;
Schur's lemma gives matching-average scalars on those blocks; and the scalar
trace formula identifies those scalars as `hEven m lambda / d_lambda` in the
even case and `hOdd m lambda / d_lambda` in the odd case.

Why it is external or why it should be proven: hook/dimension positivity and
trace division are formalized, but the actual Young-block decomposition of
`L^2(S_n)`, compatibility of those energies with `U_1`, scalarity of the
matching-average operator, and the trace/scalar identification require the
unformalized Specht-block model, conjugation-invariance argument, Schur's
lemma, and matching-restriction theorem.

Citation target if external: local trace computation plus Schur's lemma and
the Specht/Pieri matching-restriction statement.

Downstream dependencies: `L5_2_SpectralCertificate`,
`Thm4_10_MatchingGap`, `Prop4_12_SquareEnergyControlsGlobalDegree`,
`L4_13_OneTrialSoundness`, and `Thm1_1_MainIntro`, which are now conditional
on the even and odd spectral block model families.

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
  `evenBlockTraceIdentity_from_local_trace_input`,
  `oddBlockTraceIdentity_from_local_trace_input`,
  `evenTraceScalarValue_from_trace_input`,
  `oddTraceScalarValue_from_trace_input`,
  `SpectralGapFromBlockScalars`,
  `EvenSpectralGapFromCertificates`,
  `OddSpectralGapFromCertificates`,
  `matchingSpectralGap_of_even_young_certificate`,
  `matchingSpectralGap_of_odd_young_certificate`, and
  `L5_2_SpectralCertificate` are proved from the explicit inputs above.
- `Aux_SpectralBridgeRepresentationInputs.lean`: `youngHookLength_pos_of_mem`,
  `youngHookProduct_pos`, `youngCells_card`,
  `youngHookProduct_le_factorial_input`, and
  `youngDimNat_positive_hookLength_input` are proved internally.  The
  hook-product proof bounds each hook by its row-major upper cell tail and then
  multiplies the tail sizes to get `n!`.
- `Aux_SpectralBridgeRepresentationInputs.lean` also proves
  `youngDim_positive_from_hookLength_input`,
  `blockTraceIdentity_of_height_div_youngDim`, and
  `blockTraceIdentity_of_traceScalarValue`.
- `S05_Lem5_10_ZBoundCertificate.lean`: finite `zEven` certificate, proved
  modulo Lemma 5.1.
- `S05_Lem5_12_EvenHCertificate.lean`: finite `hEven` certificate, proved
  modulo Lemma 5.1 and Lemma 5.10.
- `S05_Lem5_14_OddHCertificate.lean`: finite `hOdd` certificate, proved
  modulo Lemma 5.2 and Lemma 5.12.

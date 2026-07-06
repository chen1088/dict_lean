# DictatorshipTesting

Lean 4 + Mathlib scaffold for formalizing elementary and finite-dimensional
parts of a dictatorship-testing paper for Boolean functions on `S_n`.

The project is intentionally organized around the paper.  Numbered theorem,
lemma, proposition, and corollary files use the paper number in the filename,
for example `S01_Thm1_01_MainIntro.lean`, `S04_Lem4_13_OneTrialSoundness.lean`, and
`S04_Prop4_12_SquareEnergyControlsGlobalDegree.lean`.  Helper files that exist only
to support the Lean development use the prefix `Aux_`.

## Build

This checkout uses the Lean toolchain in `lean-toolchain`:

```text
leanprover/lean4:v4.32.0-rc1
```

To build the full library:

```bash
cd dict_lean
lake exe cache get
lake build DictatorshipTesting
```

The current full target builds successfully.

## Current Status

The scaffold contains real Lean proofs for the elementary Boolean-cube,
matching-cube, and averaging steps that have been formalized so far.  A small
number of hard results are intentionally isolated behind named declarations or
named external axioms.  The only remaining `sorry` declarations are the two
Section 2 literature inputs.

Current proof-status by mathematical obligation:

For a declaration-by-declaration ledger of every remaining `sorry` and
paper-level input, see `PROOF_OBLIGATIONS.md`.

For the current rewritten Section 5 statement-to-file map, see
`DictatorshipTesting/Paper/SECTION5_FILE_MAP.md`.  The checked paper source has
34 theorem-like Section 5 statements when remarks and Appendix A inputs are
excluded, and the Lean Section 5 paper-facing file count is also 34.  Appendix A
external representation-theoretic inputs are mapped separately in
`DictatorshipTesting/Paper/APPENDIX_A_FILE_MAP.md`.

Proven finite certificates:

- `S05_Lem5_30_WeightZeroEntriesAreNeverAMajority.lean` -- Lemma 5.30:
  finite `zEven` certificate.  The current tableau-count theorem
  `S05_Lem5_30_tableau_weightZeroEntries_never_majority` is proved against
  `tableauDim`; the older `youngDim` variant remains as an external
  Specht-dimension route.
- `S05_Lem5_32_EvenCertificate.lean` -- Lemma 5.32 (`lem:h-even-app`):
  finite even certificate.  The current tableau-count theorem
  `S05_Lem5_32_tableau_even_certificate` is proved using `hEvenTableau`; the
  older `hEven`/`youngDim` variant remains as an external Specht-dimension
  route.
- `S05_Lem5_34_OddCertificate.lean` -- Lemma 5.34 (`lem:h-odd-app`):
  finite odd certificate.  The current tableau-count theorem
  `S05_Lem5_34_tableau_odd_certificate` is proved using `hOddTableau`; the
  older `hOdd`/`youngDim` variant remains as an external Specht-dimension
  route.

Proven Lemma 5.1 coordinate Coxeter package:

- `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` -- Lemma 5.1
  (`lem:young-adjacent-matrices`): the concrete tableau-coordinate Young
  adjacent operators are defined and proved to have the same-row,
  same-column, and swappable two-by-two matrix behavior.  The swappable block
  has nonzero `+1` and `-1` eigenvectors.
- `Aux_YoungAdjacentAction.lean`: packages those adjacent operators as
  `YoungAdjacentActionModel`, defines adjacent words and their operators,
  proves invariance under cancellation, distant commutation, and braid
  Coxeter moves, defines the adjacent-word permutation shadow
  `adjacentWordPerm`, and descends both the operator and permutation shadow to
  the formal quotient `AdjacentCoxeterClass`.

Proven Lemma 5.2 diagonal content package:

- `S05_Lem5_02_DiagonalContentEigenspaces.lean` -- Lemma 5.2
  (`lem:jucys-murphy-eigenbasis`, rewritten Section 5 form): proves that
  content sequences determine standard tableaux, distinct tableaux differ in a
  content coordinate, and simultaneous eigenspaces of the explicit diagonal
  content operators are the tableau basis lines.  Appendix A.2 remains the
  external group-algebra Jucys--Murphy identification.

Proven Lemma 5.7 fixed two-step tableau branching package:

- `S05_Lem5_07_TwoBoxTableauBranching.lean` -- Lemma 5.7
  (`lem:two-box-tableau-branching`): exposes the concrete bijection between
  parent tableaux following a fixed two-step removable-row deletion pattern and
  tableaux of the resulting child diagram, plus iterated deletion preservation
  of content, row, and column coordinates.

Proven Lemma 5.10 coordinate one-box deletion package:

- `S05_Lem5_10_OneBoxDeletionIsUnitary.lean` -- Lemma 5.10
  (`lem:one-box-deletion-unitary`): proves the set-level deletion/insertion
  equivalence and that the induced coordinate map preserves the finite
  coordinate inner product.

Proven Lemma 5.11 deletion-fiber intertwining:

- `S05_Lem5_11_OneBoxDeletionIntertwinesEarlierSwaps.lean` -- Lemma 5.11
  (`lem:one-box-deletion-intertwines`): proves that deleting the maximum entry
  preserves the surviving content sequence, that one-box insertion preserves
  earlier-adjacent concrete Young-adjacent matrix coefficients, and that the
  one-box deletion coordinate map intertwines both the deletion-fiber
  Young-adjacent operator and the explicit diagonal content operators.

Proven Lemma 5.16 tableau-count size components:

- `S05_Lem5_16_SizesOfTheSignPatternMultisets.lean` -- Lemma 5.16
  (`lem:X-size`): exposes the assumption-free `tableauDim` two-strip and
  one-box size recurrences from Lemmas 5.14 and 5.15.  The older `youngDim`
  wrappers assume the named dimension-branching inputs.

Proven matching-cube components used near external Lemma 5.18:

- `S05_Lem5_18_MatchingSubgroupEigenbasis.lean` -- Lemma 5.18
  (`lem:matching-restriction-X`): exposes the concrete canonical matching-cube
  action as a fixed ordered product of commuting matching-edge operators and
  proves that selected edge signs multiply to the matching character.  It also
  proves that one-edge plus/minus projections preserve all other edge
  eigenvalues, packages the support-selected one-edge projection choice, and
  proves that iterating those choices gives a simultaneous matching-edge
  eigenvector.  The full Specht-module restriction theorem remains a
  representation-layer input.

Proven Definition 5.21 matching-idempotent components:

- `S05_Def5_21_MatchingIdempotents.lean` -- Definition 5.21
  (`def:matching-idempotents`): names the low and high matching idempotents and
  proves `S05_matchingLowIdempotent_idempotent` and
  `S05_matchingHighIdempotent_idempotent`, plus the complementary identities
  `S05_matchingLowIdempotent_high_eq_zero`,
  `S05_matchingHighIdempotent_low_eq_zero`, and
  `S05_matchingLow_add_matchingHigh`.

Proven finite-average components used near external Lemma 5.23:

- `S05_Lem5_23_CentralAveragedRejection.lean` -- Lemma 5.23
  (`lem:averaged-rejection-central`): proves that the local rejection error is
  the squared distance of the high matching idempotent from zero, and that the
  mean rejection is the average of those squared high-idempotent norms.  The
  operator centrality statement remains a representation-layer target.

Proven Lemma 5.26 trace-model-to-gap algebra:

- `S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean` -- Lemma 5.26
  (`lem:block-lower-bound-gap`): proves the weighted-sum spectral-gap algebra,
  including wrappers that start from scalarity, a block trace identity,
  dimension positivity, and a finite certificate.

Remaining Lemma 5.1 representation-theory boundary:

- The Lean development does not claim a classical Specht-module
  identification for the coordinate model, nor a full action of arbitrary
  `Equiv.Perm (Fin (n+1))` on `TableauSpace lam`.  The precise missing
  infrastructure is the type-A symmetric-group Coxeter presentation/Matsumoto
  theorem for adjacent words, or a usable mathlib `CoxeterSystem
  (CoxeterMatrix.A n) (Equiv.Perm (Fin (n+1)))` connecting the adjacent-word
  quotient to permutations.

External standard inputs:

- `S02_Thm2_01_BooleanU1Classification.lean` -- Theorem 2.1
  (`thm:boolean-u1`): external classification direction
  `boolFnToReal f ∈ U1 (Fin n) -> IsDictator f` for `3 <= n`.  The `n = 1`
  and `n = 2` cases, and the converse direction that dictators lie in `U1`,
  are proved directly.
- `S02_Thm2_02_FKNStability.lean` -- Theorem 2.2 (`thm:fkn-input`):
  external FKN/stability theorem on `S_n`, stated only for the `4 <= n`
  range used by the one-trial soundness proof.
- `S05_Lem5_14_TwoBoxDimensionRecursion.lean` -- Lemma 5.14
  (`lem:dimension-two-strip-recurrence`): the current paper route uses the
  proved `tableauDim` wrapper
  `S05_Lem5_14_tableauDim_twoStrip_branching_sized`.  The older `youngDim`
  wrapper remains only as an explicit external alternative requiring
  `[TwoStripDimensionBranchingAssumption]`; no axiom instance is registered.
- `S05_Lem5_15_OneBoxDimensionRecursion.lean` -- Lemma 5.15
  (`lem:dimension-one-box-recurrence`): the current paper route uses the
  proved `tableauDim` wrapper
  `S05_Lem5_15_tableauDim_oneBoxChildrenOdd_branching`.  The older `youngDim`
  wrapper remains only as an explicit external alternative requiring
  `[OneBoxDimensionBranchingPositiveAssumption]`; no axiom instance is
  registered.
- `S05_Lem5_18_MatchingSubgroupEigenbasis.lean` -- Lemma 5.18
  (`lem:matching-restriction-X`): the paper-level statement is the full
  Specht/Pieri restriction theorem.  The current Lean file formalizes only the
  concrete matching-operator and scalar-bound interfaces needed downstream.
  The full Specht/Pieri restriction theorem is external.
- Lemmas 5.26--5.28, especially `S05_Lem5_27_EvenSpectralBridge.lean` and
  `S05_Lem5_28_OddSpectralBridge.lean`: the external Specht/Pieri/Schur
  spectral bridge is exposed as the named axioms
  `spectralBlockModelInput_even_from_specht_pieri_schur` and
  `spectralBlockModelInput_odd_from_specht_pieri_schur`.  These axioms cite the
  regular Specht decomposition, Littlewood-Richardson restriction to Young
  subgroups, Pieri two-strip specializations, and Schur's lemma.

Internal bridge components proven:

- `S05_Lem5_19_LocalTruncationOnAMatchingCharacter.lean` -- Lemma 5.19
  (`lem:PM-character-projection`): proved matching-cube character projection.
- `S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean`: the purely algebraic bridge
  is proved with explicit spectral-block-model hypotheses in its statement. In
  particular,
  `SpectralGapFromBlockScalars`, `SpectralGapFromBlockScalarLowerBounds`,
  `EvenSpectralGapFromCertificates`, `OddSpectralGapFromCertificates`, and the
  dimension-parameterized `SpectralGapFromBlockModelWithDim` route are proved.
- `S05_Lem5_27_EvenSpectralBridge.lean` and
  `S05_Lem5_28_OddSpectralBridge.lean`: the standalone paper-level spectral
  bridges are unproven until the external spectral-block model is supplied.
- `Aux_SpectralBridgeDimensionParam.lean`: dimension-parameterized algebraic
  bridge.  It proves `blockScalar_lower_bound_of_traceScalarFormula_withDim`,
  `traceScalarValue_of_blockTraceIdentity_withDim`,
  `SpectralGapFromBlockScalarsWithDim`, and `SpectralGapFromBlockModelWithDim`
  for an arbitrary dimension function.
- `Aux_SpectralBridgeRepresentationInputs.lean`: the compact interface for the
  spectral-block model used by the spectral bridge.  It contains only the Young-block
  energy, `U_1` identification, scalarity, and trace/scalar-value predicates.

External or unproven bridge statements:

- `S05_Lem5_20_TraceOfOneLocalTruncationOnOneYoungBlock.lean` -- Lemma 5.20:
  external until the matching-character restriction data is supplied.
- `S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean` -- Lemma 5.25:
  external until scalarity and trace identity inputs are supplied.
- `S05_Lem5_27_EvenSpectralBridge.lean` and
  `S05_Lem5_28_OddSpectralBridge.lean`: unproven as standalone paper-level
  spectral bridges until the spectral-block model is supplied.

Remaining spectral-bridge representation-theory boundary:

There are no longer `sorry` declarations for the spectral bridge.  Instead, the
Section 5 spectral-bridge files make the missing representation theory explicit
as named axioms:
`spectralBlockModelInput_even_from_specht_pieri_schur` and
`spectralBlockModelInput_odd_from_specht_pieri_schur`, bundled downstream as
`EvenSpectralBlockModelFamily` and `OddSpectralBlockModelFamily`.

- The explicit spectral-block-model axioms supply the actual Young-block
  energies of `F`, the `U_1` energy identification, and the matching-average
  scalar model.  Theorem 4.10, Proposition 4.12, Lemma 4.13, and Theorem 1.1
  now use these named external inputs directly rather than taking anonymous
  model-family arguments.
- The active Theorem 4.10 path still uses the original `youngDim` spectral
  model, so Theorem 4.10 and the downstream wrappers carry
  `[TwoStripDimensionBranchingAssumption]` and
  `[OneBoxDimensionBranchingPositiveAssumption]` explicitly.  No instance is
  registered for those assumptions.
- The tableau-count bridge is ready at the algebraic level, but consuming it
  requires a `SpectralBlockModelInputWithDim` instance for `tableauDim` and the
  tableau-count heights `hEvenTableau`/`hOddTableau`.

Older theorem names such as `Thm2_1_BooleanU1`, `L5_4_ZBoundApp`,
`L5_5_HEvenApp`, and `L5_6_HOddApp` are preserved inside the corresponding
`Sxx_...` files, rather than living in separate wrapper modules.

## Layout

Root import indexes:

- `DictatorshipTesting.lean`: imports the whole project.
- `DictatorshipTesting/BasicFacts.lean`: imports elementary permutation facts.
- `DictatorshipTesting/SetFacts.lean`: finite set operations used in early
  algebraic identities.
- `DictatorshipTesting/AlgebraicProperty.lean`: imports the elementary
  row-dictator algebraic property files.
- `DictatorshipTesting/Paper.lean`: imports paper-numbered theorem files and
  their helper index.
- `DictatorshipTesting/PaperAux.lean`: imports helper-only paper modules so the
  full library build checks them.
- `DictatorshipTesting/PaperPlaceholders.lean`: imports the numbered paper
  files that are currently represented in the scaffold.

Core paper definitions:

- `DictatorshipTesting/Paper/Defs.lean`: shared definitions for Boolean
  functions on permutations, dictators, `U1`, distances, matching cubes,
  square-test quantities, local projections, near-perfect matchings, and the
  finite Young-diagram model used in Section 5.

Elementary files:

- `DictatorshipTesting/Basic.lean`: permutation conventions, transpositions,
  one-coset indicators, and row/column dictator indicators.
- `DictatorshipTesting/SetFacts.lean`: set difference and symmetric difference.
- `DictatorshipTesting/AlgebraicProperty/*.lean`: finite reindexing and the
  row-dictator algebraic-property identity.

Paper-numbered highlights:

- `S01_Thm1_01_MainIntro.lean`: main tester statement, currently routed through the
  abstract tester-amplification interface.
- `S02_Thm2_01_BooleanU1Classification.lean`: Boolean degree-one structural input.
- `S02_Thm2_02_FKNStability.lean`: FKN/stability input.
- `S02_Lem2_03_*`: cube-character orthonormality, Fourier expansion, and
  Parseval.
- `S03_Lem3_01_DictatorToJunta.lean` and `S03_Lem3_02_PerfectCompleteness.lean`: matching
  cube completeness side.
- `S04_Lem4_01` through `S04_Lem4_13`, plus `S04_Cor4_09`,
  `S04_Thm4_10`, and `S04_Prop4_12`: matching-cube soundness reductions up to
  the one-trial soundness bound.
- `S05_Lem5_01` through `S05_Lem5_34`: current Section 5 spectral bridge and
  finite certificate files.  Older Section 5 theorem names such as
  `L5_4_ZBoundApp` are declarations inside these numbered files, not separate
  wrapper modules.

## Naming Conventions

- `S##_ThmA_BB_...`, `S##_LemA_BB_...`, `S##_PropA_BB_...`,
  `S##_CorA_BB_...`: preferred paper-facing filenames with explicit section
  and paper statement number.
- `ThmA_B_...`, `LA_B_...`, `PropA_B_...`, `CorA_B_...`: older
  paper-facing filenames still used by earlier sections of the scaffold.
- `Aux_...`: Lean helper lemma, implementation detail, or isolated external
  input that is not itself the paper-facing statement.

Keep theorem names stable when possible.  If a theorem is paper-numbered, keep
the declaration in the paper-numbered file even when the hard proof is factored
into an aux file.

## Development Notes

Useful commands:

```bash
lake build DictatorshipTesting
lake build DictatorshipTesting.Paper.S05_Lem5_30_WeightZeroEntriesAreNeverAMajority
lake build DictatorshipTesting.Paper.S05_Lem5_32_EvenCertificate
lake build DictatorshipTesting.Paper.S05_Lem5_34_OddCertificate
rg "sorry" DictatorshipTesting
```

The project uses `sorry` only for deliberately isolated hard inputs.  When a
new `sorry` is needed, prefer making it a named theorem in an `Aux_...` file and
then proving the paper-numbered result by applying that named theorem.  This
keeps the dependency graph readable and makes the remaining mathematical
obligations easy to find.

Do not attempt to hide representation theory inside elementary files.  The
current boundary is:

- finite cube and matching identities are formalized directly;
- external stability and representation-theoretic statements are isolated;
- Section 5 finite Young-diagram inequalities are separated from the spectral
  bridge.

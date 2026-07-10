# DictatorshipTesting

Lean 4 + Mathlib scaffold for formalizing elementary and finite-dimensional
parts of a dictatorship-testing paper for Boolean functions on `S_n`.

The project is intentionally organized around the paper.  Numbered theorem,
lemma, proposition, and corollary files use the paper number in the filename,
for example `S01_Thm1_01_MainIntro.lean`, `S04_Lem4_11_OneTrialSoundness.lean`, and
`S04_Prop4_10_SquareEnergyControlsGlobalDegree.lean`.  Shared internal paper
infrastructure uses `S##_Int...` or `S##_IntDef...` filenames, so the paper
dependency graph does not expose `Aux_` nodes.

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

## Dependency Graph

A first static dependency browser lives in [`docs/`](docs/).  It is designed
for GitHub Pages and separates large paper-facing theorem nodes from smaller
internal support nodes.  Open [`docs/index.html`](docs/index.html), or enable
GitHub Pages from the repository `docs/` folder to publish the same view.  The
browser includes a compact paper-map tab and gives the numbered Section 5
definitions 5.1--5.30 clickable popovers, so broad shared-definition
dependencies do not obscure the proof structure.  Selected nodes show the
paper statement in LaTeX and link wrapper declarations to their Lean source
lines when available.

## Current Status

The scaffold contains real Lean proofs for the elementary Boolean-cube,
matching-cube, and averaging steps that have been formalized so far.  A small
number of hard results are intentionally isolated behind named declarations or
named external axioms.  There are no remaining `sorry` declarations.  The named
external axioms are the two Section 2 Filmus inputs, the three Appendix A
representation-theory ingredient markers A.1, A.2, and A.3, and the Section 5
matching-average scalarity bridge input
`S05_matchingAverageScalarity_from_young_model_input`.  Standard-tableaux swap
connectedness is proved internally as Lemma 5.3.  Lemma 5.19 is an assembly
theorem from the three Appendix inputs and the scalarity bridge input.  The theorem wrappers
consumed by the active Theorem 4.8 path are
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA`.

Current proof-status by mathematical obligation:

For a declaration-by-declaration ledger of every external axiom and paper-level
input, see `PROOF_OBLIGATIONS.md`.

For the current rewritten Section 5 statement-to-file map, see
`DictatorshipTesting/Paper/SECTION5_FILE_MAP.md`.  Section 5 now uses separate
counters: 30 numbered definitions (`Def 5.x`) and 27 numbered result statements
(`Lem 5.x` and theorem-like variants), for 57 paper-facing Section 5 Lean files.
Appendix A external representation-theoretic inputs are mapped separately in
`DictatorshipTesting/Paper/APPENDIX_A_FILE_MAP.md`.

For the earlier paper spine, see
`DictatorshipTesting/Paper/SECTION1_FILE_MAP.md` through
`DictatorshipTesting/Paper/SECTION4_FILE_MAP.md`.  These maps record the current
paper source `../dictatorship_testing_soda27_latest.tex`, the statement counts,
the matching Lean files, and whether each statement is internal,
definition/interface, or uses an external input.  Current Section 1--4 counts
are 1 result; 3 results plus 1 definition; 2 results; and 11 results plus 2
definitions respectively.  No paper revisions are currently proposed for
Sections 1--4; this is recorded in
`DictatorshipTesting/Paper/PAPER_REVISION_CANDIDATES.md`.

The active main-theorem spine is:

```text
Thm1_1_MainIntro
  -> exists_dimensionFreeTester_of_oneTrialSoundness
  -> L4_13_OneTrialSoundness
  -> Thm2_2_FKNInput + Prop4_12_SquareEnergyControlsGlobalDegree
  -> Thm4_10_MatchingGap
  -> tableauDim even/odd spectral bridges
  -> Appendix A tableauDim spectral model inputs
```

The Boolean `U1` classification theorem remains a Section 2 external structural
input, but it is not a direct dependency of this active Lean chain because the
FKN input is already stated in the distance-to-dictators form used by Lemma
4.13.

Proven finite certificates:

- `S05_Lem5_23_WeightZeroEntriesAreNeverAMajority.lean` -- Lemma 5.23:
  finite `zEven` certificate.  The current tableau-count theorem
  `S05_Lem5_23_tableau_weightZeroEntries_never_majority` is proved against
  `tableauDim`; the older `youngDim` variant remains as an external
  Specht-dimension route.
- `S05_Lem5_25_EvenCertificate.lean` -- Lemma 5.25 (`lem:h-even-app`):
  finite even certificate.  The current tableau-count theorem
  `S05_Lem5_25_tableau_even_certificate` is proved using `hEvenTableau`; the
  older `hEven`/`youngDim` variant remains as an external Specht-dimension
  route.
- `S05_Lem5_27_OddCertificate.lean` -- Lemma 5.27 (`lem:h-odd-app`):
  finite odd certificate.  The current tableau-count theorem
  `S05_Lem5_27_tableau_odd_certificate` is proved using `hOddTableau`; the
  older `hOdd`/`youngDim` variant remains as an external Specht-dimension
  route.

Proven Lemma 5.1 coordinate Coxeter package:

- `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` -- Lemma 5.1
  (`lem:young-adjacent-matrices`): the concrete tableau-coordinate Young
  adjacent operators are defined and proved to have the same-row,
  same-column, and swappable two-by-two matrix behavior.  The swappable block
  has nonzero `+1` and `-1` eigenvectors.  The same file now also packages
  those adjacent operators as `YoungAdjacentActionModel`, defines adjacent
  words and their operators, proves invariance under cancellation, distant
  commutation, and braid Coxeter moves, defines the adjacent-word permutation
  shadow `adjacentWordPerm`, and descends both the operator and permutation
  shadow to the formal quotient `AdjacentCoxeterClass`.

Proven Lemma 5.2 diagonal content package:

- `S05_Lem5_02_DiagonalContentEigenspaces.lean` -- Lemma 5.2
  (`lem:jucys-murphy-eigenbasis`, rewritten Section 5 form): proves that
  content sequences determine standard tableaux, distinct tableaux differ in a
  content coordinate, and simultaneous eigenspaces of the explicit diagonal
  content operators are the tableau basis lines.  Appendix A.2 remains the
  external group-algebra Jucys--Murphy identification.

Proven Lemma 5.3 standard-tableaux connectedness:

- `S05_Lem5_03_ConnectednessOfStandardTableaux.lean` -- Lemma 5.3
  (`lem:tableau-swap-connected`): proves finite linear-extension connectivity
  by explicit adjacent swaps of incomparable elements and transports the path
  to valid adjacent swaps of standard tableaux.

Proven Lemma 5.4 fixed two-step tableau branching package:

- `S05_Int_StandardYoungTableaux.lean`: the internal Section 5 layer for standard
  tableaux, entry locations, max-entry deletion, one-box insertion, and the
  deletion/child equivalence.
- `S05_Lem5_04_TwoBoxTableauBranching.lean` -- Lemma 5.4
  (`lem:two-box-tableau-branching`): exposes the concrete bijection between
  parent tableaux following a fixed two-step removable-row deletion pattern and
  tableaux of the resulting child diagram, plus iterated deletion preservation
  of content, row, and column coordinates.

Proven Lemma 5.6 coordinate one-box deletion package:

- `S05_Lem5_06_OneBoxDeletionIsUnitary.lean` -- Lemma 5.6
  (`lem:one-box-deletion-unitary`): proves the set-level deletion/insertion
  equivalence and that the induced coordinate map preserves the finite
  coordinate inner product.

Proven Lemma 5.7 deletion-fiber intertwining:

- `S05_Lem5_07_OneBoxDeletionIntertwinesEarlierSwaps.lean` -- Lemma 5.7
  (`lem:one-box-deletion-intertwines`): proves that deleting the maximum entry
  preserves the surviving content sequence, that one-box insertion preserves
  earlier-adjacent concrete Young-adjacent matrix coefficients, and that the
  one-box deletion coordinate map intertwines both the deletion-fiber
  Young-adjacent operator and the explicit diagonal content operators.

Proven Lemma 5.10 sign-pattern multiset semantics:

- `S05_Lem5_10_SizesOfTheSignPatternMultisets.lean` -- Lemma 5.10
  (`lem:X-size`): proves that the genuine recursive even and odd label
  multisets have cardinality `tableauDim`. It also identifies empty-label and
  high-label multiplicities with `zEven`, `hEvenTableau`, and `hOddTableau`,
  and converts a finite enumeration of either multiset into the high-label sum
  needed by Lemma 5.13. The older `youngDim` wrappers assume the named
  dimension-branching inputs.

Proven matching-cube components for Lemma 5.11:

- `S05_Int_YoungMatchingOperators.lean`: the internal Section 5 layer for
  canonical matching-edge operators, plus/minus projections, preservation of
  other edge eigenvalues, and simultaneous matching-sign projections.
- `S05_Lem5_11_MatchingSubgroupEigenbasis.lean` -- Lemma 5.11
  (`lem:matching-restriction-X`): exposes the concrete canonical matching-cube
  action as a fixed ordered product of commuting matching-edge operators and
  proves that selected edge signs multiply to the matching character.  It also
  proves that one-edge plus/minus projections preserve all other edge
  eigenvalues, packages the support-selected one-edge projection choice, and
  proves that iterating those choices gives a simultaneous matching-edge
  eigenvector. The file now also constructs explicit signed two-box child
  embeddings and proves isometry, the final-edge sign, earlier-edge
  intertwining, pairwise orthogonality, and joint spanning. Definitions
  5.13--5.14 contain the actual recursive label multisets and Lemma 5.10 proves
  their multiplicity semantics. The file now recursively constructs the
  canonical even matching basis from those signed-child embeddings, proves
  orthonormality and spanning, proves every canonical-edge eigenvalue, and
  identifies its labels literally, with multiplicity, with
  `S05_evenSignPatternMultiset`. It now also constructs the endpoint
  equivalence and conjugating permutation for every even matching, proves that
  represented permutations are invertible isometries, and transports the
  basis with exact labels to `M.toOrdered`. The same file now assembles the
  canonical odd basis from the one-box fibers, proving orthonormality, spanning,
  all canonical matching eigenvalues, and literal equality with
  `S05_oddSignPatternMultiset`. Remaining for the full Lemma 5.11 statement:
  transport this basis to arbitrary near-perfect matchings.

Proven Definition 5.22 matching-idempotent components:

- `S05_Def5_22_MatchingIdempotents.lean` -- Definition 5.22
  (`def:matching-idempotents`): names the low and high matching idempotents and
  proves `S05_matchingLowIdempotent_idempotent` and
  `S05_matchingHighIdempotent_idempotent`, plus the complementary identities
  `S05_matchingLowIdempotent_high_eq_zero`,
  `S05_matchingHighIdempotent_low_eq_zero`, and
  `S05_matchingLow_add_matchingHigh`.

Finite-average components used by Lemma 5.15:

- `S05_Lem5_15_CentralAveragedRejection.lean` -- Lemma 5.15
  (`lem:averaged-rejection-central`): proves that the local rejection error is
  the squared distance of the high matching idempotent from zero, and that the
  mean rejection is the average of those squared high-idempotent norms.
- `S05_Def5_29_AveragedHighMatchingElement.lean` constructs the corresponding
  group-algebra coefficient function `q`, proves fixed-matching conjugation
  covariance and coefficient centrality of its matching average, and proves
  that right convolution by `q` is the uniform average of the existing high
  matching idempotents.

Generic commutant infrastructure for Lemma 5.16:

- `S05_Lem5_16_YoungBasisScalarCommutant.lean` now defines the concrete
  single-block interface `YoungModelOperatorCommutationData` and proves
  `S05_Lem5_16_youngModelOperator_scalar_on_basis`: any linear operator on one
  tableau-coordinate Young block that commutes with every explicit diagonal
  content operator and every adjacent Young operator is scalar on the tableau
  basis, using the internally proved Lemma 5.3 connectedness statement.  The
  remaining gap is not this generic commutant theorem; it is instantiating the
  averaged matching rejection operator as such a block operator and proving the
  required commutation data.
- `S05_Lem5_17a_AveragedRejectionYoungOperator.lean` now names that
  instantiation target as `AveragedRejectionYoungOperatorData`.  This is still
  only an operator interface: it packages the one-block operator, linearity, and
  adjacent/content commutation fields, and proves
  `averagedRejectionYoungOperator_scalar_on_basis` by applying Lemma 5.16.  It
  does not define the group-algebra operator `rho_lambda(q)`.
- `S05_Def5_28_GroupAlgebraAction.lean` adds the next interface layer:
  finite group-algebra coefficient functions, right convolution,
  representation action `rho(a)`, coefficient-level centrality predicates, and
  `YoungRepresentationActionData`.  It proves by finite conjugation reindexing
  that a coefficient-central element commutes with every represented group
  element and every represented group-algebra element.
- `S05_Def5_29_AveragedHighMatchingElement.lean` instantiates this interface
  with the actual averaged high matching element.  For every supplied
  `YoungRepresentationActionData`, it constructs `rho_lambda(q)`, proves its
  adjacent/content commutation, packages `AveragedRejectionYoungOperatorData`,
  and obtains one-block scalarity from Lemmas 5.16 and 5.3.  It now also defines
  each actual matching-character Fourier idempotent and proves, from cube
  character orthogonality, that the represented idempotent selects its
  matching eigenspace and that the represented high element acts by `1` on
  high characters and `0` on low characters.
- `AppA_DefA_01_YoungOrthogonalActionData.lean` and
  `AppA_DefA_02_JucysMurphyContentActionData.lean` now state the faithful A.1
  representation action and A.2 Jucys--Murphy/content action interfaces without
  energy, trace, or scalarity fields.  Their internal adapter constructs the
  `YoungRepresentationActionData` used by Definition 5.29.  The A.1 interface
  is tied to the literal adjacent transposition `(a,a+1)`, not an arbitrary
  named permutation.
- `S05_Def5_30_TableauOperatorTrace.lean` defines the basis trace, proves
  that it agrees with Mathlib's basis-independent linear-map trace, proves
  `trace = tableauDim * scalar`, proves scalar equals trace divided by nonzero
  tableau dimension, and proves that the concrete averaged-operator trace is
  the average of the represented fixed-matching traces.  It also proves that a
  fixed trace is the sum of its high-character idempotent traces, and that in
  any supplied matching eigenbasis it equals the number of high labels.  Right
  action on the full matrix-coordinate block contributes the factor
  `tableauDim` from the free left tableau index.

The existing A.1/A.2 axiom declarations still have their old numerical-shadow
types.  They were not silently changed: replacing them now would break the
active Theorem 4.8 route because the repository does not yet construct the
regular Young-block energy decomposition.  Lemma 5.13 now identifies the trace
of the concrete fixed-matching operator with `hEvenTableau` or `hOddTableau`
  from the labeled matching eigenbasis in its paper statement. The positive-size
  even trace and full Young-block trace are now instantiated unconditionally
  from the arbitrary-perfect-matching basis. The canonical odd labeled basis is
  proved; the remaining Lemma 5.11 and trace obligation is its transport to
  arbitrary near-perfect matchings. The
  final global weighted scalarity axiom therefore remains.

Proven Lemma 5.18 trace-model-to-gap algebra:

- `S05_Lem5_18_BlockLowerBoundImpliesTheGap.lean` -- Lemma 5.18
  (`lem:block-lower-bound-gap`): proves the weighted-sum spectral-gap algebra,
  including wrappers that start from scalarity, a block trace identity,
  dimension positivity, and a finite certificate.

Appendix A representation-theory boundary for Lemma 5.1:

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
  `boolFnToReal f ∈ U1 (Fin n) -> IsDictator f` for `3 <= n`, exposed as the
  named axiom `booleanU1_dictator_classification_input`.  The `n = 1` and
  `n = 2` cases, and the converse direction that dictators lie in `U1`, are
  proved directly.  No active downstream Lean proof currently invokes this
  wrapper directly; it records the paper's structural classification input.
- `S02_Thm2_02_FKNStability.lean` -- Theorem 2.2 (`thm:fkn-input`):
  external FKN/stability theorem on `S_n`, stated only for the `4 <= n`
  range used by the one-trial soundness proof, exposed as the named axiom
  `fknStability_input`.  It is consumed by `L4_13_OneTrialSoundness`, and then
  by the main theorem wrapper.
- `S05_Lem5_08_TwoBoxDimensionRecursion.lean` -- Lemma 5.8
  (`lem:dimension-two-strip-recurrence`): the current paper route uses the
  proved `tableauDim` wrapper
  `S05_Lem5_08_tableauDim_twoStrip_branching_sized`.  The older `youngDim`
  wrapper remains only as an explicit external alternative requiring
  `[TwoStripDimensionBranchingAssumption]`; no axiom instance is registered.
- `S05_Lem5_09_OneBoxDimensionRecursion.lean` -- Lemma 5.9
  (`lem:dimension-one-box-recurrence`): the current paper route uses the
  proved `tableauDim` wrapper
  `S05_Lem5_09_tableauDim_oneBoxChildrenOdd_branching`.  The older `youngDim`
  wrapper remains only as an explicit external alternative requiring
  `[OneBoxDimensionBranchingPositiveAssumption]`; no axiom instance is
  registered.
- `S05_Lem5_11_MatchingSubgroupEigenbasis.lean` -- Lemma 5.11
  (`lem:matching-restriction-X`): the paper-level statement is the full
  labeled matching eigenbasis theorem. The current Lean file proves the
  concrete matching-operator and sign-projection algebra, proves the complete
  signed-child orthogonal decomposition, constructs the canonical even
  matching basis recursively, proves its simultaneous eigenvalue equations,
  and proves exact label-multiset equality with
  `S05_evenSignPatternMultiset`. Arbitrary-perfect-matching transport is also
  proved by an explicit endpoint permutation and represented isometry. The odd
  near-perfect matching basis remains.
- Lemmas 5.18--5.21, especially
  `S05_Lem5_19_RegularYoungBlockDecomposition.lean`,
  `S05_Lem5_20_EvenSpectralBridge.lean`, and
  `S05_Lem5_21_OddSpectralBridge.lean`: the external Specht/Pieri/Schur
  spectral bridge is consumed through Lemma 5.19 theorem wrappers
  `spectralBlockModelInputWithDim_even_from_appendixA` and
  `spectralBlockModelInputWithDim_odd_from_appendixA`.  Those wrappers are
  produced by Lemma 5.19 from the explicit A.1/A.2/A.3 marker axioms and
  `S05_matchingAverageScalarity_from_young_model_input`, citing the regular
  Specht decomposition, Littlewood-Richardson restriction to Young subgroups,
  Pieri two-strip specializations, and Schur's lemma for the tableauDim
  spectral model.

Internal bridge components proven:

- `S05_Lem5_12_LocalTruncationOnAMatchingCharacter.lean` -- Lemma 5.12
  (`lem:PM-character-projection`): proved matching-cube character projection.
- `S05_Lem5_18_BlockLowerBoundImpliesTheGap.lean`: the purely algebraic bridge
  is proved with explicit spectral-block-model hypotheses in its statement. In
  particular,
  `SpectralGapFromBlockScalars`, `SpectralGapFromBlockScalarLowerBounds`,
  `EvenSpectralGapFromCertificates`, `OddSpectralGapFromCertificates`, and the
  dimension-parameterized `SpectralGapFromBlockModelWithDim` route are proved.
- `S05_Lem5_19_RegularYoungBlockDecomposition.lean`: the main-text assembly
  lemma turning the external Appendix A.1/A.2/A.3 inputs and
  `S05_matchingAverageScalarity_from_young_model_input` into
  the even and odd `SpectralBlockModelInputWithDim` theorem wrappers consumed
  by Theorem 4.8.
- `S05_Lem5_20_EvenSpectralBridge.lean` and
  `S05_Lem5_21_OddSpectralBridge.lean`: the tableau-count spectral bridges are
  proved from explicit `SpectralBlockModelInputWithDim` hypotheses; Lemma 5.19
  supplies those spectral model inputs for the paper application.
- `S05_Int_SpectralBridgeAlgebra.lean`: dimension-parameterized algebraic
  bridge.  It proves `blockScalar_lower_bound_of_traceScalarFormula_withDim`,
  `traceScalarValue_of_blockTraceIdentity_withDim`,
  `SpectralGapFromBlockScalarsWithDim`, and `SpectralGapFromBlockModelWithDim`
  for an arbitrary dimension function.
- `S05_Int_SpectralBridgeRepresentationInputs.lean`: the compact interface for the
  spectral-block model used by the spectral bridge.  It contains only the Young-block
  energy, `U_1` identification, scalarity, and trace/scalar-value predicates.

Remaining bridge boundary:

- `S05_Lem5_13_TraceOfOneLocalTruncationOnOneYoungBlock.lean` -- Lemma 5.13:
  the actual fixed-matching tableau and full-block trace formulas from the
  explicit labeled matching eigenbasis in the paper statement; the even formulas
  are now instantiated unconditionally for every positive-size perfect matching.
- `S05_Lem5_17_BlockScalarOfTheAveragedRejection.lean` -- Lemma 5.17:
  trace-divided-by-dimension algebra from explicit scalarity and trace identity
  inputs; those inputs are bundled into the spectral-block model boundary.
- `S05_Lem5_20_EvenSpectralBridge.lean` and
  `S05_Lem5_21_OddSpectralBridge.lean`: proven algebraic bridges from explicit
  `SpectralBlockModelInputWithDim` / spectral block model input; Lemma 5.19
  supplies that input for the paper application.

Remaining spectral-bridge representation-theory boundary:

There are no longer `sorry` declarations for the spectral bridge.  Instead, the
Section 5 spectral-bridge files make the missing representation theory explicit
through Lemma 5.19 theorem wrappers:
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA`.  The remaining axiom
declarations used by this bridge are the Appendix A.1/A.2/A.3 marker inputs and
`S05_matchingAverageScalarity_from_young_model_input`; Lemma 5.19 consumes them
through assembly theorems.

- The explicit spectral-block-model theorem wrappers supply the actual Young-block
  energies of `F`, the `U_1` energy identification, and the matching-average
  scalar model.  Theorem 4.8, Proposition 4.10, Lemma 4.11, and Theorem 1.1
  now use these named external inputs through the tableauDim spectral bridge.
- The active Theorem 4.8 path uses the tableauDim bridges in Lemmas 5.20 and
  5.21 with the finite certificates in Lemmas 5.25 and 5.27; it no longer
  carries the older `youngDim` dimension-branching typeclass hypotheses.

Older theorem names such as `Thm2_1_BooleanU1`, `L5_4_ZBoundApp`,
`L5_5_HEvenApp`, and `L5_6_HOddApp` are preserved inside the corresponding
`Sxx_...` files, rather than living in separate wrapper modules.

## Layout

Root import files:

- `DictatorshipTesting.lean`: imports the whole project directly, including the
  represented paper-numbered files and Appendix A external-input files.
- `DictatorshipTesting/BasicFacts.lean`: imports elementary permutation facts.
- `DictatorshipTesting/SetFacts.lean`: finite set operations used in early
  algebraic identities.
- `DictatorshipTesting/AlgebraicProperty.lean`: imports the elementary
  row-dictator algebraic property files.

Core paper definitions:

- `DictatorshipTesting/Paper/Defs/`: split definition files.  The individual
  `S01_Def*`, `S02_Def*`, `S03_Def*`, and `S05_Def*` files carry the reusable
  definitions and should be imported directly.
- `DictatorshipTesting/Paper/Defs/S05_Def5_24_TableauEvenHeight.lean` and
  `DictatorshipTesting/Paper/Defs/S05_Def5_25_TableauOddHeight.lean`: neutral
  `hEvenTableau`/`hOddTableau` height definitions shared by Appendix A.2 and
  the finite certificate proofs, so Appendix A does not import certificate
  proof files just to mention those functions.
- `DictatorshipTesting/Paper/Defs/S05_Def5_26_CertificateSpecialDiagrams.lean` and
  `DictatorshipTesting/Paper/Defs/S05_Def5_27_CertificateExceptionalPredicates.lean`:
  canonical finite-certificate diagrams and exceptional-shape predicates used
  by Lemmas 5.23--5.27.

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
- `S04_Lem4_01` through `S04_Lem4_11`, plus `S04_Cor4_07`,
  `S04_Thm4_08`, and `S04_Prop4_10`: matching-cube soundness reductions up to
  the one-trial soundness bound, using the separate result counter for Section 4.
- `S05_Def5_01` through `S05_Lem5_17`: current Section 5 spectral bridge and
  finite certificate files.  Older Section 5 theorem names such as
  `L5_4_ZBoundApp` are declarations inside these numbered files, not separate
  wrapper modules.

## Naming Conventions

- `S##_ThmA_BB_...`, `S##_LemA_BB_...`, `S##_PropA_BB_...`,
  `S##_CorA_BB_...`: preferred paper-facing filenames with explicit section
  and paper statement number.
- `ThmA_B_...`, `LA_B_...`, `PropA_B_...`, `CorA_B_...`: older
  paper-facing filenames still used by earlier sections of the scaffold.
- `S##_Int_...`, `S##_IntDef_...`, `S##_IntInst_...`: shared internal paper
  infrastructure, definition fragments, and instances that are not themselves
  paper-facing numbered statements.
- `Aux_...`: older non-paper helper modules outside the paper-facing layer.

Keep theorem names stable when possible.  If a theorem is paper-numbered, keep
the declaration in the paper-numbered file even when the hard proof is factored
into an aux file.

## Development Notes

Useful commands:

```bash
lake build DictatorshipTesting
lake build DictatorshipTesting.Paper.S05_Lem5_23_WeightZeroEntriesAreNeverAMajority
lake build DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate
lake build DictatorshipTesting.Paper.S05_Lem5_27_OddCertificate
rg "sorry|axiom|opaque|unsafe" DictatorshipTesting
```

The project should have no `sorry` declarations.  Deliberately isolated hard
inputs are represented as named external axioms in the relevant paper-facing or
Appendix A files, with citations and downstream dependencies recorded in
`PROOF_OBLIGATIONS.md`.

Do not attempt to hide representation theory inside elementary files.  The
current boundary is:

- finite cube and matching identities are formalized directly;
- external stability and representation-theoretic statements are isolated;
- Section 5 finite Young-diagram inequalities are separated from the spectral
  bridge.

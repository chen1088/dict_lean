# Section 5 Progress

Source checked: `../dictatorship_testing_soda27_latest.tex`.

## Spine Status

- Section 5 now has 40 theorem-like numbered statements when counting only
  `definition`, `lemma`, `proposition`, `theorem`, and `corollary`
  environments, including the five numbered tableau-preliminary definitions
  5.1--5.5.
- Appendix A has 4 numbered external-input statements.
- The Section 5 paper-facing Lean file count is 40.
- The Appendix A Lean-facing file count is 4.
- The regular Young-block decomposition assembly lemma is now in Section 5:
  `S05_Lem5_32_RegularYoungBlockDecomposition.lean`.
- The degree-one Young-block input is in Appendix A:
  `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean`.

Detailed maps:

- `SECTION5_FILE_MAP.md`
- `APPENDIX_A_FILE_MAP.md`

## Latest Checkpoint

- Lemma 5.16 coordinate-level deletion-fiber intertwining is proved:
  `S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines`.
- Lemma 5.23 now has proved matching eigenvalue preservation under one-edge
  projections, support-selected one-edge projections, and simultaneous
  matching sign projections.
- Definition 5.26 now has proved low/high matching idempotent identities,
  zero cross-compositions, and the low-plus-high decomposition identity.
- The remaining main representation-theoretic frontier is the spectral-block
  model input supplied by Appendix A.
- Appendix A now exposes explicit marker axioms for A.1, A.2, A.3, and A.4.
  Lemma 5.32 consumes those markers to produce the even/odd
  spectral-model theorem wrappers
  `spectralBlockModelInputWithDim_even_from_appendixA` and
  `spectralBlockModelInputWithDim_odd_from_appendixA`.
- Theorem 4.10 is a proved Section 4 theorem whose active proof path uses the
  tableauDim bridge exposed by Lemmas 5.31--5.34 and these
  dimension-parameterized Lemma 5.32 spectral model wrappers.

## Internal Progress

- Definitions 5.1--5.5 expose the numbered tableau-preliminary interfaces:
  Young diagrams and boxes, removable corners and one-box removals, standard
  tableaux, tableau coordinate spaces, and contents/adjacent operators.
- The dependency graph now exposes the substantial helper layer
  `Aux_StandardYoungTableaux.lean`, which contains the concrete max-entry
  deletion, one-box insertion, and deletion/child equivalence API used by
  Lemmas 5.12 and 5.14--5.16.
- Lemma 5.6 exposes the concrete tableau-coordinate Coxeter model through
  `S05_Lem5_06_adjacentTranspositionsInYoungsBasis_coxeterModel`.
- Lemma 5.7 is proved internally for explicit diagonal content operators:
  `S05_Lem5_07_tableauContentSequence_injective` proves content-sequence
  injectivity, `S05_Lem5_07_diagonalContent_commonEigen_support` separates
  distinct tableaux by a content coordinate, and
  `S05_Lem5_07_diagonalContentEigenspaces` proves that the common eigenspaces
  are the tableau basis lines.
- Lemma 5.12 now exposes the concrete fixed two-step tableau branching
  equivalence `S05_Lem5_12_twoStepDeletionTableauxEquivChildTableaux`, together
  with the iterated deletion content/row/column preservation wrappers.
- Lemma 5.15 now proves the concrete coordinate form of one-box deletion
  unitarity: `S05_Lem5_15_deletionCoordinateMap_inner` shows that the deletion
  equivalence preserves the finite coordinate inner product.
- Lemma 5.16 now proves the deletion/content compatibility needed by the
  rewritten spine and the earlier-adjacent coefficient preservation needed for
  the next operator step: `S05_Lem5_16_insertMax_youngAdjacentMatrixCoeff`
  preserves the full concrete Young-adjacent matrix coefficient under one-box
  insertion for earlier adjacent pairs, and
  `S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines` proves
  the corresponding coordinate-level intertwining for the deletion-fiber
  operator, while
  `S05_Lem5_16_deletionCoordinateMap_diagonalContent_intertwines` shows that
  the one-box deletion coordinate map intertwines the explicit diagonal content
  operators on surviving entries.
- Lemma 5.21 now exposes the assumption-free `tableauDim` size components
  `S05_Lem5_21_tableauDim_twoStrip_size` and
  `S05_Lem5_21_tableauDim_oneBox_size`, while the older `youngDim`
  wrappers state the named dimension-branching inputs they require.
- Lemma 5.23 exposes more of the concrete matching-cube action:
  `S05_Lem5_23_canonicalMatchingCubeOperatorEven_eq_indexedProduct` gives the
  fixed ordered-product form, and
  `S05_Lem5_23_matchingEdgeSign_finRange_product_eq_matchingCharacter` turns
  the selected edge-sign product into the matching character.  The one-edge
  projection lemmas now also prove preservation of all other edge eigenvalues,
  for example
  `S05_Lem5_23_matchingEdgePlusProjectionEven_preserves_otherEigen`; the
  support-selected one-edge projection wrappers such as
  `S05_Lem5_23_matchingEdgeSignProjectionEven_isMatchingEigen` package the
  plus/minus choice by character support, and
  `S05_Lem5_23_matchingSignProjectionEven_isMatchingEigenvector` / odd prove
  that iterating those choices over `List.finRange m` yields a simultaneous
  matching-edge eigenvector.  The dependency graph now exposes this support as
  the helper layer `Aux_YoungMatchingOperators.lean`.
- Definition 5.26 now proves that the named low and high matching idempotents
  are genuinely idempotent through
  `S05_matchingLowIdempotent_idempotent` and
  `S05_matchingHighIdempotent_idempotent`; it also proves the complementary
  identities `S05_matchingLowIdempotent_high_eq_zero`,
  `S05_matchingHighIdempotent_low_eq_zero`, and
  `S05_matchingLow_add_matchingHigh`.
- Lemma 5.28 now proves the finite-average/high-idempotent part of central
  averaged rejection: `S05_Lem5_28_matchingMeanProjectionError_eq_high_idempotent_average`
  rewrites the mean local rejection as the average of squared high-idempotent
  norms.  Operator centrality on Young blocks remains a representation-layer
  target.
- Lemmas 5.25, 5.28, 5.29, and 5.30 are documented as interface/algebraic
  layers around the spectral-block model boundary rather than as standalone
  internal formalizations of the Young-block trace, centrality, or scalar
  commutant representation theory.
- Lemma 5.31 now exposes trace-model-to-gap algebra:
  `S05_Lem5_31_spectralGapFromBlockTraceModel` and
  `S05_Lem5_31_spectralGapFromBlockTraceModelWithDim` derive the spectral-gap
  inequality directly from scalarity, a block trace identity, dimension
  positivity, and the finite certificate.
- Lemma 5.36 has a tableau-count z-bound theorem
  `S05_Lem5_36_tableau_weightZeroEntries_never_majority`.
- Lemma 5.38 has a tableau-count even certificate theorem
  `S05_Lem5_38_tableau_even_certificate`.
- Lemma 5.40 has a tableau-count odd certificate theorem
  `S05_Lem5_40_tableau_odd_certificate`.
- Lemmas 5.31--5.34 expose the algebraic spectral bridge from explicit
  spectral-block-model inputs.

## Appendix A Boundary

The following remain external inputs rather than Lean-proved representation
theorems:

- A.1 Young orthogonal realization.
- A.2 Jucys--Murphy content spectrum.
- A.3 Degree-one Young-block identification.
- A.4 Connectedness of standard tableaux.

The Appendix A files add only the A.1/A.2/A.3/A.4 external marker axioms.
Lemma 5.32 has no standalone external input; it is proved by assembling those
markers into the spectral model wrappers.  The current Section 5 tableau-count
dimension route also no longer registers the older `youngDim`
dimension-branching instances.

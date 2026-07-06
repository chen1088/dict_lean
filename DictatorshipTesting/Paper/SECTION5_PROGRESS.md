# Section 5 Progress

Source checked: `../dictatorship_testing_soda27_latest.tex`.

## Spine Status

- Section 5 now has 34 theorem-like numbered statements when counting only
  `definition`, `lemma`, `proposition`, `theorem`, and `corollary`
  environments.
- Appendix A has 5 numbered external-input statements.
- The Section 5 paper-facing Lean file count is 34.
- The Appendix A Lean-facing file count is 5.
- The old Section 5 regular Young-block file moved to
  `AppA_ThmA_03_RegularYoungBlockDecomposition.lean`.
- The old Section 5 degree-one Young-block file moved to
  `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean`.

Detailed maps:

- `SECTION5_FILE_MAP.md`
- `APPENDIX_A_FILE_MAP.md`

## Internal Progress

- Lemma 5.1 exposes the concrete tableau-coordinate Coxeter model through
  `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel`.
- Lemma 5.2 is proved internally for explicit diagonal content operators:
  `S05_Lem5_02_tableauContentSequence_injective` proves content-sequence
  injectivity, `S05_Lem5_02_diagonalContent_commonEigen_support` separates
  distinct tableaux by a content coordinate, and
  `S05_Lem5_02_diagonalContentEigenspaces` proves that the common eigenspaces
  are the tableau basis lines.
- Lemma 5.7 now exposes the concrete fixed two-step tableau branching
  equivalence `S05_Lem5_07_twoStepDeletionTableauxEquivChildTableaux`, together
  with the iterated deletion content/row/column preservation wrappers.
- Lemma 5.10 now proves the concrete coordinate form of one-box deletion
  unitarity: `S05_Lem5_10_deletionCoordinateMap_inner` shows that the deletion
  equivalence preserves the finite coordinate inner product.
- Lemma 5.11 now proves the deletion/content compatibility needed by the
  rewritten spine and the earlier-adjacent coefficient preservation needed for
  the next operator step: `S05_Lem5_11_insertMax_youngAdjacentMatrixCoeff`
  preserves the full concrete Young-adjacent matrix coefficient under one-box
  insertion for earlier adjacent pairs, and
  `S05_Lem5_11_deletionCoordinateMap_diagonalContent_intertwines` shows that
  the one-box deletion coordinate map intertwines the explicit diagonal content
  operators on surviving entries.  The full coordinate-level Young-adjacent
  operator intertwining remains future work.
- Lemma 5.16 now exposes the assumption-free `tableauDim` size components
  `S05_Lem5_16_tableauDim_twoStrip_size` and
  `S05_Lem5_16_tableauDim_oneBox_size`, while the older `youngDim`
  wrappers state the named dimension-branching inputs they require.
- Lemma 5.18 exposes more of the concrete matching-cube action:
  `S05_Lem5_18_canonicalMatchingCubeOperatorEven_eq_indexedProduct` gives the
  fixed ordered-product form, and
  `S05_Lem5_18_matchingEdgeSign_finRange_product_eq_matchingCharacter` turns
  the selected edge-sign product into the matching character.
- Lemma 5.23 now proves the finite-average/high-idempotent part of central
  averaged rejection: `S05_Lem5_23_matchingMeanProjectionError_eq_high_idempotent_average`
  rewrites the mean local rejection as the average of squared high-idempotent
  norms.  Operator centrality on Young blocks remains a representation-layer
  target.
- Lemma 5.26 now exposes trace-model-to-gap algebra:
  `S05_Lem5_26_spectralGapFromBlockTraceModel` and
  `S05_Lem5_26_spectralGapFromBlockTraceModelWithDim` derive the spectral-gap
  inequality directly from scalarity, a block trace identity, dimension
  positivity, and the finite certificate.
- Lemma 5.18 still does not claim the full Specht-module matching-restriction
  theorem; that remains a representation-layer input.
- Lemma 5.30 has a tableau-count z-bound theorem
  `S05_Lem5_30_tableau_weightZeroEntries_never_majority`.
- Lemma 5.32 has a tableau-count even certificate theorem
  `S05_Lem5_32_tableau_even_certificate`.
- Lemma 5.34 has a tableau-count odd certificate theorem
  `S05_Lem5_34_tableau_odd_certificate`.
- Lemmas 5.26--5.28 expose the algebraic spectral bridge from explicit
  spectral-block-model inputs.

## Appendix A Boundary

The following remain external inputs rather than Lean-proved representation
theorems:

- A.1 Young orthogonal realization.
- A.2 Jucys--Murphy content spectrum.
- A.3 Regular Young-block decomposition.
- A.4 Degree-one Young-block identification.
- A.5 Connectedness of standard tableaux.

The Appendix A files do not add axioms.  The current Section 5 tableau-count
dimension route also no longer registers the older `youngDim`
dimension-branching instances.  The remaining named axioms are the
spectral-block-model inputs tracked in `PROOF_OBLIGATIONS.md`.

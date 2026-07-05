# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`).  Remarks are not represented as
paper-facing Lean files.

Section 5 statement count: 36.
Section 5 paper-facing Lean file count: 36.

Lemma 5.1 is aligned with the rewritten paper statement: the Lean file proves
the explicit tableau Coxeter model.  It does not claim the external classical
Specht-module identification.

| Paper stmt | Environment | Paper title | Lean file | Main wrappers | Status |
| --- | --- | --- | --- | --- | --- |
| 5.1 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel` | proved |
| 5.2 | lemma | Jucys--Murphy eigenbasis | `S05_Lem5_02_JucysMurphyEigenbasis.lean` | `S05_Lem5_02_jucysMurphyDiagonalOperator_basis_eigen` | documented external theorem |
| 5.3 | definition | Young block | `S05_Def5_03_YoungBlock.lean` | `S05_YoungBlock`, `S05_Def5_03_SpectralBlockModelInput` | definition only |
| 5.4 | lemma | Regular Young blocks | `S05_Lem5_04_RegularYoungBlocks.lean` | `S05_Lem5_04_YoungBlockDecompositionInput`, `S05_Lem5_04_U1YoungBlockIdentificationInput` | documented external theorem |
| 5.5 | definition | Two-box removals | `S05_Def5_05_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | definition only |
| 5.6 | definition | Signed two-box removals | `S05_Def5_06_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | definition only |
| 5.7 | definition | One-box removals | `S05_Def5_07_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | definition only |
| 5.8 | lemma | Two-box tableau branching | `S05_Lem5_08_TwoBoxTableauBranching.lean` | `S05_Lem5_08_deleteFirstMaxAsTableau`, `S05_Lem5_08_iterated_deletion_tableauContentSequence` | conditional |
| 5.9 | definition | One-box deletion spaces | `S05_Def5_09_OneBoxDeletionSpaces.lean` | `S05_Def5_09_OneBoxDeletionTableaux`, `S05_Def5_09_existsUnique_tableauMaxAt` | definition only |
| 5.10 | lemma | One-box corner decomposition | `S05_Lem5_10_OneBoxCornerDecomposition.lean` | `S05_Lem5_10_row_form`, `S05_Lem5_10_removable_corner`, `S05_Lem5_10_tableau_unique_removable_corner` | proved |
| 5.11 | lemma | One-box deletion is unitary | `S05_Lem5_11_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_11_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow` | conditional |
| 5.12 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_12_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_12_deleteMax_tableauContentSequence` | conditional |
| 5.13 | definition | Even sign-pattern multiset | `S05_Def5_13_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | definition only |
| 5.14 | definition | Odd sign-pattern multiset | `S05_Def5_14_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | definition only |
| 5.15 | lemma | Two-box dimension recursion | `S05_Lem5_15_TwoBoxDimensionRecursion.lean` | `youngDim_twoStrip_branching_input`, `S05_Lem5_15_tableauDim_twoStrip_branching_sized` | legacy axiom dependency |
| 5.16 | lemma | One-box dimension recursion | `S05_Lem5_16_OneBoxDimensionRecursion.lean` | `youngDim_oneBox_branching_input`, `S05_Lem5_16_tableauDim_oneBoxChildrenOdd_branching` | legacy axiom dependency |
| 5.17 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_17_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_17_youngDim_twoStrip_size`, `S05_Lem5_17_youngDim_oneBox_size` | conditional |
| 5.18 | definition | Matching characters | `S05_Def5_18_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | definition only |
| 5.19 | lemma | Matching subgroup eigenbasis | `S05_Lem5_19_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_19_canonicalMatchingYoungOperatorEven_involutive`, `S05_Lem5_19_matchingEdge_sameRow_eigen_even` | documented external theorem |
| 5.20 | lemma | Local truncation on a matching character | `S05_Lem5_20_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_20_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_20_matchingLocalProjection_kills_high_matchingCharacter` | proved |
| 5.21 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_21_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | conditional |
| 5.22 | definition | Matching idempotents | `S05_Def5_22_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent` | definition only |
| 5.23 | lemma | Local truncation as convolution | `S05_Lem5_23_LocalTruncationAsConvolution.lean` | `S05_Lem5_23_local_truncation_as_convolution` | proved |
| 5.24 | lemma | Central averaged rejection | `S05_Lem5_24_CentralAveragedRejection.lean` | `S05_Lem5_24_matchingMeanProjectionError_eq_average` | conditional |
| 5.25 | lemma | Young-basis scalar commutant | `S05_Lem5_25_YoungBasisScalarCommutant.lean` | `S05_Lem5_25_YoungBasisScalarCommutantInput`, `S05_Lem5_25_matchingAverageScalarity_eq_sum` | documented external theorem |
| 5.26 | lemma | Block scalar of the averaged rejection | `S05_Lem5_26_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_26_scalar_eq_trace_div_dimension`, `S05_Lem5_26_even_scalar_eq_hEven_div_dim` | conditional |
| 5.27 | lemma | The degree-one space as Young blocks | `S05_Lem5_27_TheDegreeOneSpaceAsYoungBlocks.lean` | `S05_Lem5_27_l2DistSqToU1_eq_nonU1_sum` | documented external theorem |
| 5.28 | lemma | Block lower bound implies the gap | `S05_Lem5_28_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_28_spectralGapFromBlockScalars`, `S05_Lem5_28_spectralGapFromBlockModelWithDim` | proved |
| 5.29 | lemma | Even spectral bridge | `S05_Lem5_29_EvenSpectralBridge.lean` | `S05_Lem5_29_evenSpectralGapFromCertificates`, `S05_Lem5_29_tableauDim_evenSpectralGapFromCertificates` | legacy axiom dependency |
| 5.30 | lemma | Odd spectral bridge | `S05_Lem5_30_OddSpectralBridge.lean` | `S05_Lem5_30_oddSpectralGapFromCertificates`, `S05_Lem5_30_tableauDim_oddSpectralGapFromCertificates` | legacy axiom dependency |
| 5.31 | lemma | Counting one more matching edge | `S05_Lem5_31_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_31_counting_one_more_matching_edge` | proved |
| 5.32 | lemma | Weight-zero entries are never a majority | `S05_Lem5_32_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_32_weightZeroEntries_never_majority`, `S05_Lem5_32_tableau_weightZeroEntries_never_majority` | legacy axiom dependency |
| 5.33 | lemma | Where the induction can fail | `S05_Lem5_33_WhereTheInductionCanFail.lean` | `S05_Lem5_33_where_the_induction_can_fail` | proved |
| 5.34 | lemma | Even certificate | `S05_Lem5_34_EvenCertificate.lean` | `S05_Lem5_34_even_certificate`, `S05_Lem5_34_tableau_even_certificate` | legacy axiom dependency |
| 5.35 | lemma | Odd exceptional children | `S05_Lem5_35_OddExceptionalChildren.lean` | `S05_Lem5_35_odd_exceptional_children` | proved |
| 5.36 | lemma | Odd certificate | `S05_Lem5_36_OddCertificate.lean` | `S05_Lem5_36_odd_certificate`, `S05_Lem5_36_tableau_odd_certificate` | legacy axiom dependency |

Notes:

- For Lemma 5.1, `proved` means the explicit tableau-coordinate Coxeter model
  is proved in Lean.  The standard identification with the classical Specht
  module/Young orthogonal representation remains a cited representation-theory
  boundary, not a Lean theorem in this repository.
- `legacy axiom dependency` means a legacy `youngDim` or spectral-block-model
  theorem still uses an explicit named axiom, while a tableau-count variant may
  already be proved internally.
- `conditional` means the file proves the recorded wrapper from explicit
  hypotheses/interfaces, but not every representation-layer interpretation
  appearing in the prose paper.

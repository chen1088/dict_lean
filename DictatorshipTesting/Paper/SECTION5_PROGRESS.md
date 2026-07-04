# Section 5 Progress

## This Run

Completed commits:
- `6ba8505` Add adjacent value swap for Lemma 5.1
- `d796ef7` Add swapped-tableau case for Lemma 5.1
- `0d0d35c` Add content API for Lemma 5.2
- `0721c63` Track cells under adjacent tableau swap
- `bc88b48` Add content-sequence API for Lemma 5.2
- `7e7b8a8` Clarify Young block interface files
- `132a1b3` Add row combinatorics for strip removals
- `ba0eb24` Start basis-level two-box tableau branching
- `e8adde1` Expose sign-pattern size interfaces
- `d167717` Expand matching character and idempotent interfaces
- `b450942` Expose averaged rejection definitions
- `c648518` Clarify spectral bridge paper-facing wrappers
- `43450b8` Add paper-numbered finite certificate aliases
- `f6729d5` Extend deletion content-sequence compatibility
- `c702f90` Expose one-box deletion corner interfaces
- `c12c502` Expose one-box deletion cell equivalence facts

Files changed:
- `DictatorshipTesting/Paper/Aux_YoungAdjacentEntries.lean`
- `DictatorshipTesting/Paper/Aux_YoungDiagramCorners.lean`
- `DictatorshipTesting/Paper/S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean`
- `DictatorshipTesting/Paper/S05_Lem5_02_JucysMurphyEigenbasis.lean`
- `DictatorshipTesting/Paper/S05_Def5_03_YoungBlock.lean`
- `DictatorshipTesting/Paper/S05_Lem5_04_RegularYoungBlocks.lean`
- `DictatorshipTesting/Paper/S05_Def5_05_TwoBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Def5_06_SignedTwoBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Def5_07_OneBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Lem5_08_TwoBoxTableauBranching.lean`
- `DictatorshipTesting/Paper/S05_Def5_13_EvenSignPatternMultiset.lean`
- `DictatorshipTesting/Paper/S05_Def5_14_OddSignPatternMultiset.lean`
- `DictatorshipTesting/Paper/S05_Lem5_17_SizesOfTheSignPatternMultisets.lean`
- `DictatorshipTesting/Paper/S05_Def5_18_MatchingCharacters.lean`
- `DictatorshipTesting/Paper/S05_Lem5_20_LocalTruncationOnAMatchingCharacter.lean`
- `DictatorshipTesting/Paper/S05_Def5_22_MatchingIdempotents.lean`
- `DictatorshipTesting/Paper/S05_Lem5_23_LocalTruncationAsConvolution.lean`
- `DictatorshipTesting/Paper/S05_Lem5_24_CentralAveragedRejection.lean`
- `DictatorshipTesting/Paper/S05_Lem5_25_YoungBasisScalarCommutant.lean`
- `DictatorshipTesting/Paper/S05_Lem5_26_BlockScalarOfTheAveragedRejection.lean`
- `DictatorshipTesting/Paper/S05_Lem5_27_TheDegreeOneSpaceAsYoungBlocks.lean`
- `DictatorshipTesting/Paper/S05_Lem5_28_BlockLowerBoundImpliesTheGap.lean`
- `DictatorshipTesting/Paper/S05_Lem5_29_EvenSpectralBridge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_30_OddSpectralBridge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_31_CountingOneMoreMatchingEdge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_32_WeightZeroEntriesAreNeverAMajority.lean`
- `DictatorshipTesting/Paper/S05_Lem5_34_EvenCertificate.lean`
- `DictatorshipTesting/Paper/S05_Lem5_36_OddCertificate.lean`
- `DictatorshipTesting/Paper/S05_Def5_09_OneBoxDeletionSpaces.lean`
- `DictatorshipTesting/Paper/S05_Lem5_11_OneBoxDeletionIsUnitary.lean`
- `DictatorshipTesting/Paper/S05_Lem5_12_OneBoxDeletionIntertwinesEarlierSwaps.lean`

Main names added:
- `adjacentSwapValue`, `adjacentSwapEntry`
- `adjacentSwapEntry_loCell`, `adjacentSwapEntry_hiCell`
- `adjacentSwapEntry_of_ne_lo_hi`, `adjacentSwapEntry_involutive`
- `adjacentSwapEntry_bijective`
- `adjacentSwapValue_lt_of_lt_of_not_adjacent_pair`
- `adjacentSwapTableau`
- `adjacentSwapTableau_cell_lo`, `adjacentSwapTableau_cell_hi`
- `adjacentSwapTableau_cell_of_ne_lo_hi`
- `adjacentSwapTableau_entryContent_lo`
- `adjacentSwapTableau_entryContent_hi`
- `adjacentSwapTableau_entryContent_of_ne_lo_hi`
- `S05_Lem5_01_adjacentSwapEntry_loCell`
- `S05_Lem5_01_adjacentSwapEntry_hiCell`
- `S05_Lem5_01_adjacentSwapEntry_bijective`
- `S05_Lem5_01_adjacentSwapTableau`
- `S05_Lem5_01_adjacentSwapTableau_cell_lo`
- `S05_Lem5_01_adjacentSwapTableau_cell_hi`
- `S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_lo`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_hi`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_of_ne_lo_hi`
- `tableauContentSequence`
- `tableauContentSequence_adjacentSwap_lo`
- `tableauContentSequence_adjacentSwap_hi`
- `tableauContentSequence_adjacentSwap_of_ne_lo_hi`
- `S05_Lem5_02_cellContent`, `S05_Lem5_02_entryContent`
- `S05_Lem5_02_tableauContentSequence`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_lo`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_hi`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_of_ne_lo_hi`
- `S05_Lem5_02_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow`
- `S05_Lem5_02_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol`
- `S05_Lem5_02_entryContent_adjacent_lo_eq_hi_sub_one_of_sameRow`
- `S05_Lem5_02_entryContent_adjacent_lo_eq_hi_add_one_of_sameCol`
- `S05_Def5_03_YoungBlockEnergyModel`
- `S05_Def5_03_MatchingAverageScalarModel`
- `S05_Def5_03_SpectralBlockModelInput`
- `S05_Lem5_04_YoungBlockDecompositionInput`
- `S05_Lem5_04_U1YoungBlockIdentificationInput`
- `S05_Lem5_04_blockEnergy_nonnegative`
- `S05_Lem5_04_u1_identification`
- `youngRow_sum_range_add_two`
- `sum_row_diff_of_twoBoxSubdiagram`
- `sum_row_diff_of_horizontalTwoStripChild`
- `sum_row_diff_of_verticalTwoStripChild`
- `row_le_parent_of_twoBoxSubdiagram`
- `row_le_parent_of_horizontalTwoStripChild`
- `row_le_parent_of_verticalTwoStripChild`
- `next_parent_row_le_child_row_of_horizontalTwoStripChild`
- `parent_row_le_child_row_add_one_of_verticalTwoStripChild`
- `row_diff_le_one_of_verticalTwoStripChild`
- `S05_Def5_05_sum_row_diff_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_sum_row_diff_of_verticalTwoBoxRemoval`
- `S05_Def5_05_row_le_parent_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_row_le_parent_of_verticalTwoBoxRemoval`
- `S05_Def5_05_next_parent_row_le_child_row_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_parent_row_le_child_row_add_one_of_verticalTwoBoxRemoval`
- `S05_Def5_05_row_diff_le_one_of_verticalTwoBoxRemoval`
- `S05_PositiveSignedTwoBoxRemoval`
- `S05_NegativeSignedTwoBoxRemoval`
- `S05_Def5_06_sum_row_diff_of_positiveSignedTwoBoxRemoval`
- `S05_Def5_06_sum_row_diff_of_negativeSignedTwoBoxRemoval`
- `S05_Def5_07_existsUnique_row_of_oneBoxRemoval`
- `S05_Def5_07_exists_removableRow_of_oneBoxRemoval`
- `S05_Lem5_08_deleteFirstMaxAsTableau`
- `S05_Lem5_08_first_deleted_cell_removable_corner`
- `S05_Lem5_08_after_first_deletion_unique_second_corner`
- `S05_Lem5_08_second_deleted_cell_removable_corner`
- `S05_evenZeroSignPatternCount_zero`
- `S05_evenZeroSignPatternCount_succ`
- `S05_evenHighSignPatternCount_zero`
- `S05_evenHighSignPatternCount_succ`
- `S05_oddHighSignPatternCount_eq_evenHigh_sum`
- `S05_Lem5_17_evenZeroSignPatternCount_succ`
- `S05_Lem5_17_evenHighSignPatternCount_succ`
- `S05_Lem5_17_oddHighSignPatternCount_eq_evenHigh_sum`
- `S05_Lem5_17_youngDim_twoStrip_size`
- `S05_Lem5_17_youngDim_oneBox_size`
- `S05_matchingCharacterWeight`
- `S05_matchingCharacterLow`, `S05_matchingCharacterHigh`
- `S05_matchingCharacter_empty`
- `S05_matchingCharacterWeight_empty`
- `S05_matchingCharacterLow_empty`
- `S05_matchingCharacterWeight_singleton`
- `S05_matchingCharacterLow_singleton`
- `S05_not_low_and_high`
- `S05_matchingCharacter_low_or_high`
- `S05_Lem5_20_cubeLowDegreeOnePart_matchingCharacter_of_low`
- `S05_Lem5_20_cubeLowDegreeOnePart_matchingCharacter_of_high`
- `S05_Lem5_20_matchingLocalProjection_preserves_low_matchingCharacter`
- `S05_Lem5_20_matchingLocalProjection_kills_high_matchingCharacter`
- `S05_matchingLowCharacterSet`, `S05_matchingHighCharacterSet`
- `S05_mem_matchingLowCharacterSet_iff`
- `S05_mem_matchingHighCharacterSet_iff`
- `S05_matchingLowIdempotent_apply`
- `S05_matchingHighIdempotent_apply`
- `S05_Lem5_23_local_truncation_eq_low_idempotent`
- `S05_Lem5_23_residual_eq_high_idempotent`
- `S05_Lem5_24_matchingLocalProjectionError_eq_l2DistSq`
- `S05_Lem5_24_matchingMeanProjectionError_eq_average`
- `S05_Lem5_25_YoungBasisScalarCommutantInput`
- `S05_Lem5_25_matchingAverageScalarity_eq_sum`
- `S05_Lem5_26_scalar_eq_trace_div_dimension`
- `S05_Lem5_26_even_scalar_eq_hEven_div_dim`
- `S05_Lem5_26_odd_scalar_eq_hOdd_div_dim`
- `S05_nonU1YoungBlocks`
- `S05_mem_nonU1YoungBlocks_iff`
- `S05_Lem5_27_l2DistSqToU1_eq_nonU1_sum`
- `S05_Lem5_28_spectralGapFromBlockScalars`
- `S05_Lem5_28_blockScalar_lower_bound_of_traceScalarFormula`
- `S05_Lem5_28_traceScalarValue_of_blockTraceIdentity`
- `S05_Lem5_29_evenSpectralGapFromCertificates`
- `S05_Lem5_30_oddSpectralGapFromCertificates`
- `S05_Lem5_31_counting_one_more_matching_edge`
- `S05_Lem5_32_weightZeroEntries_never_majority`
- `S05_Lem5_32_zEven_le_youngDim`
- `S05_Lem5_34_even_certificate`
- `S05_Lem5_36_odd_certificate`
- `S05_Def5_09_existsUnique_tableauMaxAt`
- `S05_Lem5_11_deletedCornerCell_row`
- `S05_Lem5_11_deletedCornerCell_col`
- `S05_Lem5_11_insertMax_entry_deletedCorner`
- `S05_Lem5_11_insertMax_entry_ne_deletedCorner`
- `S05_Lem5_11_youngCellExceptEquivChild_to_row`
- `S05_Lem5_11_youngCellExceptEquivChild_to_col`
- `S05_Lem5_11_youngCellExceptEquivChild_symm_row`
- `S05_Lem5_11_youngCellExceptEquivChild_symm_col`
- `S05_Lem5_11_insertMax_entry_lt_last_of_ne_deletedCorner`
- `S05_Lem5_12_deleteMax_tableauContentSequence`

## Next Blocker

The remaining early Section 5 claims about Young's orthogonal matrices, the
operator-level Jucys--Murphy eigenbasis, Specht restriction, Young-block
scalarity, and Schur-lemma centrality are representation-layer statements.  No
new representation-theory input was introduced in this batch.

## Next Recommended Milestone

Run the self-extension scan for remaining axiom-free improvements.  The most
likely useful next target is basis-level tableau deletion compatibility in
Lemmas 5.8--5.12; representation-layer owner files should only receive precise
interfaces or comments, not new mathematical claims.

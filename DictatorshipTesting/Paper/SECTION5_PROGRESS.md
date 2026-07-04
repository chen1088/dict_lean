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

## Next Blocker

The remaining Lemma 5.1 and Lemma 5.2 claims are the future
representation-layer statements about Young's orthogonal matrices and the
operator-level Jucys--Murphy eigenbasis.  No new representation-theory input was
introduced in this batch.

## Next Recommended Milestone

Start Lemma 5.8 with basis-level two-box tableau branching statements phrased
as iterated one-box deletion facts.  Do not formalize Specht modules or
operator branching in that file.

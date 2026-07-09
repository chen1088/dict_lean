# Section 4 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: definitions and theorem-like results use separate counters.
Remarks, examples, equations, proofs, and later-section statements are not
represented here.

Section 4 count: 2 definitions and 11 theorem-like results.

| Status | Paper item | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | Lem 4.1 | lemma | Square test detects Fourier weight at least two | `S04_Lem4_01_CubeSquare.lean` | `L4_1_CubeSquare` | Boolean-cube square-test Fourier identity. |
| definition/interface | Def 4.1 | definition | Local degree-one space | `Defs/S03_Def3_15_IsMatchingLocalDegreeOne.lean`; `Defs/S03_Def3_16_MatchingLocalHighDegreeEnergy.lean` | `IsMatchingLocalDegreeOne`, `matchingLocalHighDegreeEnergy` | Matching-cube local degree-one vocabulary. |
| definition/interface | Def 4.2 | definition | Matching-local truncation | `Defs/S03_Def3_17_MatchingLocalProjection.lean`; `Defs/S03_Def3_18_MatchingLocalProjectionError.lean` | `matchingLocalProjection`, `matchingLocalProjectionError` | Local projection and error vocabulary. |
| proven | Lem 4.2 | lemma | The definition of `P_M` is independent of representatives | `S04_Lem4_02_PMIndependentOfRepresentatives.lean` | `L4_4_PMIndependentOfRepresentatives` | Representative-change invariance of the local truncation. |
| proven | Lem 4.3 | lemma | `P_M` keeps exactly the local degree-one functions | `S04_Lem4_03_PMFixesLocal.lean` | `L4_5_PMFixesLocal` | Characterizes fixed points of the matching-local projection. |
| proven | Lem 4.4 | lemma | Local high-degree error formula | `S04_Lem4_04_LocalHighDegreeErrorFormula.lean` | `L4_6_LocalHighDegreeErrorFormula` | Identifies local projection error with average high-degree cube energy. |
| proven | Lem 4.5 | lemma | High local degrees have zero inner product with local degree one | `S04_Lem4_05_PMPerpendicular.lean` | `L4_7_PMPerpendicular` | Orthogonality of local high-degree residuals to the local degree-one space. |
| proven | Lem 4.6 | lemma | A basic indicator has local degree at most one | `S04_Lem4_06_TijLocalDegree.lean` | `L4_8_TijLocalDegree` | Each one-coset indicator restricts to local degree at most one. |
| proven | Cor 4.7 | corollary | `U_1` is contained in every local degree-one space | `S04_Cor4_07_U1Local.lean` | `Cor4_9_U1Local` | Follows from Lemmas 4.3 and 4.6. |
| proven | Thm 4.8 | theorem | Matching-cube spectral gap | `S04_Thm4_08_MatchingGap.lean` | `Thm4_10_MatchingGap` | Proved through the tableauDim Section 5 bridge. Lemma 5.18 assembles the Appendix A representation-theoretic inputs into the dimension-parameterized spectral model; the active route no longer carries the older `youngDim` dimension-branching typeclass hypotheses. |
| proven | Lem 4.9 | lemma | One trial in cube coordinates | `S04_Lem4_09_TrialCubeCoordinates.lean` | `L4_11_TrialCubeCoordinates` | Rewrites one sampled group trial as the matching-cube square expression. |
| proven | Prop 4.10 | proposition | Square energy controls global degree | `S04_Prop4_10_SquareEnergyControlsGlobalDegree.lean` | `Prop4_12_SquareEnergyControlsGlobalDegree` | Reduction from Theorem 4.8 to the one-trial square-energy lower bound. |
| proven | Lem 4.11 | lemma | One-trial soundness | `S04_Lem4_11_OneTrialSoundness.lean` | `L4_13_OneTrialSoundness` | Combines Proposition 4.10 with the external Theorem 2.2 stability input and the rejection-probability lower bound. |

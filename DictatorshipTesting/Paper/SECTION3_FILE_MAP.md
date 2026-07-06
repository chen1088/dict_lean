# Section 3 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`). Remarks, examples, equations, proofs,
and later-section statements are not represented here.

Section 3 statement count: 2.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | 3.1 | lemma | Completeness on matching cubes | `S03_Lem3_01_DictatorToJunta.lean` | `L3_1_DictatorToJunta`, `L3_1_ImageDictatorToJunta` | Dictators restrict to one-juntas on every matching cube. |
| proven | 3.2 | lemma | Perfect completeness | `S03_Lem3_02_PerfectCompleteness.lean` | `L3_2_PerfectCompleteness`, `cubeOneJunta_square_zero` | The square test accepts dictator restrictions with probability one. |


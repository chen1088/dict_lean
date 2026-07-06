# Section 2 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`). Remarks, examples, equations, proofs,
and later-section statements are not represented here.

Section 2 statement count: 4.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: Filmus Boolean degree-one classification | 2.1 | theorem | Structural input: Boolean degree-one functions on `S_n` | `S02_Thm2_01_BooleanU1Classification.lean` | `Thm2_1_BooleanU1`, `booleanU1_dictator_classification_input` | The dictator-to-`U1` direction and the `n = 1, 2` cases are proved. The nontrivial classification direction for `3 <= n` is the precise named external axiom, cited to Filmus, Discrete Analysis 2021:25, Theorem 2.8. No active downstream Lean proof currently invokes `Thm2_1_BooleanU1`; it remains the paper's structural classification input. |
| external: Filmus FKN/stability theorem | 2.2 | theorem | FKN/stability input on `S_n` | `S02_Thm2_02_FKNStability.lean` | `Thm2_2_FKNInput`, `fknStability_input` | This is the named external axiom for the literature FKN/stability input in the `4 <= n` range, cited to Filmus, Discrete Analysis 2021:25, Theorem 1.5 plus the Boolean classification input. It is consumed by `L4_13_OneTrialSoundness`, hence by `Thm1_1_MainIntro`. |
| proven | 2.3 | lemma | Orthonormality and Parseval on the cube | `S02_Lem2_03_CubeParseval.lean` plus component files | `L2_3_CubeParseval`, `L2_3_cubeChar_orthonormality`, `L2_3_cubeFourier_expansion`, `L2_3_cubeParseval_identity` | The cube-character orthonormality, Fourier expansion, and Parseval identity are proved internally. These facts feed the cube and matching-local Fourier calculations in Sections 3 and 4. |
| definition/interface | 2.4 | definition | Low-degree truncation on one cube | `Defs.lean` | `cubeLowDegreeOnePart`, `cubeHighDegreeEnergy` | Core Boolean-cube Fourier vocabulary used by the Section 4 local projection and high-degree error files. |

# Paper Numbering Map

This index records the numbering used by the current compiled paper. Detailed
file mappings live in the section maps under `DictatorshipTesting/Paper/`.
Definition counters are independent from theorem-like counters. A definition
split across several Lean modules uses letter suffixes without creating extra
paper numbers.

| Section | Numbered definitions | Theorem-like statements | Detailed map |
| --- | ---: | ---: | --- |
| 1 | 0 | 1 | `DictatorshipTesting/Paper/SECTION1_FILE_MAP.md` |
| 2 | 2 | 3 | `DictatorshipTesting/Paper/SECTION2_FILE_MAP.md` |
| 3 | 0 | 2 | `DictatorshipTesting/Paper/SECTION3_FILE_MAP.md` |
| 4 | 1 | 7 | `DictatorshipTesting/Paper/SECTION4_FILE_MAP.md` |
| 5 | 12 | 20 | `DictatorshipTesting/Paper/SECTION5_FILE_MAP.md` |

Totals: 15 numbered definitions and 33 theorem-like statements.

The complete grouped-definition module map is
`DictatorshipTesting/Paper/DEFINITION_FILE_MAP.md`. Internal modules named
`SXX_Int_*`, `SXX_IntDef_*`, or `SXX_IntInst_*` do not create paper numbers.

The three representation-theory results are part of the Section 5 sequence:

| Current statement | Lean file |
| --- | --- |
| Theorem 5.2, Young orthogonal action | `S05_Thm5_02_YoungOrthogonalAction.lean` |
| Theorem 5.3, Jucys--Murphy content action | `S05_Thm5_03_JucysMurphyContentAction.lean` |
| Lemma 5.9, degree-one Young-block identification | `S05_Lem5_09_DegreeOneYoungBlockIdentification.lean` |

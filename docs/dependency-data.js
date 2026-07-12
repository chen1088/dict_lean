window.DICT_DEPENDENCY_DATA = {
  "repoUrl": "https://github.com/chen1088/dict_lean",
  "nodes": [
    {
      "id": "S01_T01",
      "label": "Thm 1.1",
      "title": "Main theorem",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S01_Thm1_01_MainIntro.lean",
      "wrappers": [
        "S01_Thm1_01_MainIntro"
      ],
      "deps": [
        "S02_D01",
        "S03_L02",
        "S04_L11"
      ],
      "summary": "Thm 1.1: Main theorem.",
      "statement": "Thm 1.1: Main theorem.",
      "terms": [
        {
          "text": "Perfect completeness",
          "target": "S03_L02"
        },
        {
          "text": "One-trial soundness",
          "target": "S04_L11"
        }
      ],
      "paperLabel": "thm:main-intro",
      "paperEnv": "theorem",
      "paperStatementLatex": "There is a nonadaptive one-sided oracle tester which, given\n$f:S_n\\to\\{0,1\\}$ and $0<\\epsilon<1$, accepts every $f\\in\\mathcal D$ and rejects\nevery $f$ with $\\dist(f,\\mathcal D)\\ge\\epsilon$ with probability at least $2/3$.\nThe tester uses $O(\\epsilon^{-2})$ queries.",
      "leanLinks": [
        {
          "name": "S01_Thm1_01_MainIntro",
          "file": "DictatorshipTesting/Paper/S01_Thm1_01_MainIntro.lean",
          "line": 477
        }
      ]
    },
    {
      "id": "S02_D01",
      "label": "Def 2.1",
      "title": "Finite-seed nonadaptive oracle tester",
      "section": "Section 2 definitions",
      "kind": "definition",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S02_Def2_01_FiniteSeedTester.lean",
      "wrappers": [
        "OracleTester",
        "OracleTester.run",
        "OracleTester.acceptanceProbability",
        "OracleTester.rejectionProbability",
        "OracleTester.oneSided"
      ],
      "deps": [],
      "summary": "Def 2.1: Operational finite-seed nonadaptive oracle tester.",
      "statement": "Def 2.1: Operational finite-seed nonadaptive oracle tester.",
      "terms": [],
      "paperLabel": "def:finite-seed-tester",
      "paperEnv": "definition",
      "paperStatementLatex": "A finite-seed tester for functions $f:S_n\\to\\{0,1\\}$ consists of a finite nonempty seed set $\\Omega$, a query count $Q$, a query schedule $q:\\Omega\\times[Q]\\to S_n$, and a Boolean decision rule $D:\\Omega\\times\\{0,1\\}^{Q}\\to\\{\\mathrm{accept},\\mathrm{reject}\\}$. On seed $\\omega$, the tester reads the answer vector $(f(q(\\omega,1)),\\ldots,f(q(\\omega,Q)))$ and applies $D$. The seed is uniform. This model is nonadaptive because the entire query schedule depends only on the seed. It is one-sided for a property $\\mathcal P$ if every $f\\in\\mathcal P$ is accepted for every seed. Acceptance and rejection probabilities are the corresponding uniform fractions of seeds.",
      "leanLinks": [
        {
          "name": "OracleTester",
          "file": "DictatorshipTesting/Paper/Defs/S02_Def2_01_FiniteSeedTester.lean",
          "line": 22
        },
        {
          "name": "OracleTester.run",
          "file": "DictatorshipTesting/Paper/Defs/S02_Def2_01_FiniteSeedTester.lean",
          "line": 34
        }
      ]
    },
    {
      "id": "S02_N01",
      "label": "Notation",
      "title": "Dictators, 1-cosets, and the degree-one space",
      "section": "Section 2 notation",
      "kind": "notation",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_U1.lean",
      "wrappers": [
        "IsDictator",
        "oneCosetReal",
        "U1"
      ],
      "deps": [],
      "summary": "The dictator class, 1-coset indicators, and their linear span U1.",
      "statement": "The dictator class, 1-coset indicators, and their linear span U1.",
      "terms": [],
      "paperStatementLatex": "For $i,j\\in[n]$, let $\\mathcal T_{ij}:=\\{\\pi\\in S_n:\\pi(i)=j\\}$ and $t_{ij}:=\\mathbf 1_{\\mathcal T_{ij}}$. The degree-one space is $U_1=\\spanop\\{t_{ij}:i,j\\in[n]\\}\\subseteq L^2(S_n)$. The dictator class $\\D$ consists of the Boolean functions depending only on one value $\\pi(i)$ or one inverse value $\\pi^{-1}(j)$, including the constants.",
      "leanLinks": [
        {
          "name": "U1",
          "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_U1.lean",
          "line": 20
        },
        {
          "name": "oneCosetReal",
          "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_OneCosetReal.lean",
          "line": 19
        },
        {
          "name": "IsDictator",
          "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_IsDictator.lean",
          "line": 21
        }
      ]
    },
    {
      "id": "S02_N02",
      "label": "Notation",
      "title": "Boolean-cube Fourier notation",
      "section": "Section 2 notation",
      "kind": "notation",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_CubeChar.lean",
      "wrappers": [
        "cubeChar",
        "cubeFourierCoeff"
      ],
      "deps": [],
      "summary": "Boolean-cube characters and Fourier coefficients.",
      "statement": "Boolean-cube characters and Fourier coefficients.",
      "terms": [],
      "paperStatementLatex": "For $S\\subseteq[m]$, define $\\chi_S(x)=(-1)^{\\sum_{r\\in S}x_r}$. For $g:\\{0,1\\}^m\\to\\mathbb R$, define $\\widehat g(S)=\\E_x g(x)\\chi_S(x)$.",
      "leanLinks": [
        {
          "name": "cubeChar",
          "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_CubeChar.lean",
          "line": 21
        },
        {
          "name": "cubeFourierCoeff",
          "file": "DictatorshipTesting/Paper/Defs/S02_IntDef_CubeFourierCoeff.lean",
          "line": 20
        }
      ]
    },
    {
      "id": "S02_D02",
      "label": "Def 2.2",
      "title": "Low-degree truncation on one cube",
      "section": "Section 2 definitions",
      "kind": "definition",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S02_Def2_02a_CubeLowDegreeOnePart.lean",
      "wrappers": [
        "cubeLowDegreeOnePart",
        "cubeHighDegreeEnergy"
      ],
      "deps": [
        "S02_L03"
      ],
      "summary": "Def 2.2: Degree-at-most-one Fourier truncation and high-degree energy.",
      "statement": "Def 2.2: Degree-at-most-one Fourier truncation and high-degree energy.",
      "terms": [
        {
          "text": "Boolean-cube Fourier notation",
          "target": "S02_N02"
        }
      ],
      "paperLabel": "def:cube-low-degree-truncation",
      "paperEnv": "definition",
      "paperStatementLatex": "For $g:\\{0,1\\}^m\\to\\mathbb R$, define $P_{\\le 1}g(x)=\\sum_{S\\subseteq[m],\\ |S|\\le1}\\widehat g(S)\\chi_S(x)$. Thus $P_{\\le1}g$ keeps only the constant Fourier coefficient and the level-one coefficients, and $\\|g-P_{\\le1}g\\|^2=\\sum_{S\\subseteq[m],\\ |S|\\ge2}\\widehat g(S)^2$.",
      "leanLinks": [
        {
          "name": "cubeLowDegreeOnePart",
          "file": "DictatorshipTesting/Paper/Defs/S02_Def2_02a_CubeLowDegreeOnePart.lean",
          "line": 21
        },
        {
          "name": "cubeHighDegreeEnergy",
          "file": "DictatorshipTesting/Paper/Defs/S02_Def2_02b_CubeHighDegreeEnergy.lean",
          "line": 21
        }
      ]
    },
    {
      "id": "S02_T01",
      "label": "Thm 2.1",
      "title": "Boolean U1 classification",
      "section": "External inputs",
      "kind": "paper",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean",
      "wrappers": [
        "S02_Thm2_01_BooleanU1Classification",
        "booleanU1_dictator_classification_input"
      ],
      "deps": [],
      "summary": "Thm 2.1: Boolean U1 classification.",
      "statement": "Thm 2.1: Boolean U1 classification.",
      "terms": [
        {
          "text": "U1",
          "target": "S02_N01"
        }
      ],
      "paperLabel": "thm:boolean-u1",
      "paperEnv": "theorem",
      "paperStatementLatex": "If $f:S_n\\to\\{0,1\\}$ lies in $U_1$, then $f\\in\\D$.  Conversely, every\n$f\\in\\D$ lies in $U_1$.",
      "leanLinks": [
        {
          "name": "S02_Thm2_01_BooleanU1Classification",
          "file": "DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean",
          "line": 164
        },
        {
          "name": "booleanU1_dictator_classification_input",
          "file": "DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean",
          "line": 157
        }
      ]
    },
    {
      "id": "S02_T02",
      "label": "Thm 2.2",
      "title": "FKN/stability input",
      "section": "External inputs",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean",
      "wrappers": [
        "S02_Thm2_02_FKNStability",
        "fknStability_input"
      ],
      "deps": [],
      "summary": "Thm 2.2: FKN/stability input.",
      "statement": "Thm 2.2: FKN/stability input.",
      "terms": [],
      "paperLabel": "thm:fkn-input",
      "paperEnv": "theorem",
      "paperStatementLatex": "There is an absolute constant $c_{\\mathrm{FKN}}>0$ such that every Boolean\n$f:S_n\\to\\{0,1\\}$ satisfies\n\\[\n  \\norm{f-P_{U_1}f}^2\n  \\ge c_{\\mathrm{FKN}}\\,\\dist(f,\\D)^2.\n\\]",
      "leanLinks": [
        {
          "name": "S02_Thm2_02_FKNStability",
          "file": "DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean",
          "line": 40
        },
        {
          "name": "fknStability_input",
          "file": "DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean",
          "line": 32
        }
      ]
    },
    {
      "id": "S02_L03",
      "label": "Lem 2.3",
      "title": "Cube Fourier facts",
      "section": "Section 2",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S02_Lem2_03_CubeParseval.lean",
      "wrappers": [
        "S02_Lem2_03_CubeParseval"
      ],
      "deps": [],
      "summary": "Lem 2.3: Cube Fourier facts.",
      "statement": "Lem 2.3: Cube Fourier facts.",
      "terms": [],
      "paperLabel": "lem:cube-parseval",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $S,T\\subseteq[m]$,\n\\begin{equation}\\label{eq:cube-character-orthonormality}\n  \\E_x\\chi_S(x)\\chi_T(x)\n  =\n  \\begin{cases}\n    1, & S=T,\\\\\n    0, & S\\ne T.\n  \\end{cases}\n\\end{equation}\nConsequently, every $g:\\{0,1\\}^m\\to\\mathbb R$ has the expansion\n\\begin{equation}\\label{eq:cube-fourier-expansion}\n  g(x)=\\sum_{S\\subseteq[m]}\\widehat g(S)\\chi_S(x),\n\\end{equation}\nand Parseval's identity holds:\n\\begin{equation}\\label{eq:cube-parseval-identity}\n  \\E_x[g(x)^2]=\\sum_{S\\subseteq[m]}\\widehat g(S)^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S02_Lem2_03_CubeParseval",
          "file": "DictatorshipTesting/Paper/S02_Lem2_03_CubeParseval.lean",
          "line": 25
        }
      ]
    },
    {
      "id": "S03_L01",
      "label": "Lem 3.1",
      "title": "Completeness on matching cubes",
      "section": "Section 3",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S03_Lem3_01_DictatorToJunta.lean",
      "wrappers": [
        "S03_Lem3_01_DictatorToJunta",
        "S03_Lem3_01_ImageDictatorToJunta"
      ],
      "deps": [],
      "summary": "Lem 3.1: Completeness on matching cubes.",
      "statement": "Lem 3.1: Completeness on matching cubes.",
      "terms": [],
      "paperLabel": "lem:dictator-to-junta",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $f\\in\\D$, then for every base point $\\pi$ and every near-perfect matching\n$M$, the restriction $g_{\\pi,M}$ is a Boolean $1$-junta.",
      "leanLinks": [
        {
          "name": "S03_Lem3_01_DictatorToJunta",
          "file": "DictatorshipTesting/Paper/S03_Lem3_01_DictatorToJunta.lean",
          "line": 53
        },
        {
          "name": "S03_Lem3_01_ImageDictatorToJunta",
          "file": "DictatorshipTesting/Paper/S03_Lem3_01_DictatorToJunta.lean",
          "line": 21
        }
      ]
    },
    {
      "id": "S03_L02",
      "label": "Lem 3.2",
      "title": "Perfect completeness",
      "section": "Section 3",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S03_Lem3_02_PerfectCompleteness.lean",
      "wrappers": [
        "S03_Lem3_02_PerfectCompleteness",
        "cubeOneJunta_square_zero"
      ],
      "deps": [
        "S03_L01"
      ],
      "summary": "Lem 3.2: Perfect completeness.",
      "statement": "Lem 3.2: Perfect completeness.",
      "terms": [
        {
          "text": "Completeness on matching cubes",
          "target": "S03_L01"
        }
      ],
      "paperLabel": "lem:perfect-completeness",
      "paperEnv": "lemma",
      "paperStatementLatex": "Every $f\\in\\D$ is accepted by \\cref{alg:matching-trial} with probability $1$.",
      "leanLinks": [
        {
          "name": "S03_Lem3_02_PerfectCompleteness",
          "file": "DictatorshipTesting/Paper/S03_Lem3_02_PerfectCompleteness.lean",
          "line": 73
        },
        {
          "name": "cubeOneJunta_square_zero",
          "file": "DictatorshipTesting/Paper/S03_Lem3_02_PerfectCompleteness.lean",
          "line": 22
        }
      ]
    },
    {
      "id": "S04_D01",
      "label": "Def 4.1",
      "title": "Local degree-one space",
      "section": "Section 4 definitions",
      "kind": "definition",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S04_Def4_01a_IsMatchingLocalDegreeOne.lean",
      "wrappers": [
        "IsMatchingLocalDegreeOne",
        "matchingLocalHighDegreeEnergy"
      ],
      "deps": [
        "S02_L03"
      ],
      "summary": "Def 4.1: Matching-local degree-one space and high-degree energy.",
      "statement": "Def 4.1: Matching-local degree-one space and high-degree energy.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "def:local-degree-one-space",
      "paperEnv": "definition",
      "paperStatementLatex": "For a fixed matching $M$, let $\\mathcal W_M\\subseteq L^2(S_n)$ be the set of functions $F:S_n\\to\\mathbb R$ such that, on every coset $C$, the cube function $F_{C,M}(x):=F(\\rho_C\\tau_x)$ has Fourier coefficients only at weights $0$ and $1$. Equivalently, every coefficient indexed by $S\\subseteq[m]$ with $|S|\\ge2$ is zero.",
      "leanLinks": [
        {
          "name": "IsMatchingLocalDegreeOne",
          "file": "DictatorshipTesting/Paper/Defs/S04_Def4_01a_IsMatchingLocalDegreeOne.lean",
          "line": 21
        },
        {
          "name": "matchingLocalHighDegreeEnergy",
          "file": "DictatorshipTesting/Paper/Defs/S04_Def4_01b_MatchingLocalHighDegreeEnergy.lean",
          "line": 20
        }
      ]
    },
    {
      "id": "S04_D02",
      "label": "Def 4.2",
      "title": "Matching-local truncation",
      "section": "Section 4 definitions",
      "kind": "definition",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S04_Def4_02a_MatchingLocalProjection.lean",
      "wrappers": [
        "matchingLocalProjection",
        "matchingLocalProjectionError"
      ],
      "deps": [
        "S02_L03",
        "S04_D01"
      ],
      "summary": "Def 4.2: Matching-local Fourier truncation and its squared error.",
      "statement": "Def 4.2: Matching-local Fourier truncation and its squared error.",
      "terms": [
        {
          "text": "Local degree-one space",
          "target": "S04_D01"
        },
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "def:PM-local-truncation",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\omega\\in S_n$, define the matching-local truncation by $(P_M f)(\\omega)=\\sum_{S\\subseteq[m],\\ |S|\\le1}\\widehat f_{C_M(\\omega),M}(S)\\,\\chi_S(x_{C_M(\\omega)}(\\omega))$. Equivalently, on a fixed coset $C$, $(P_Mf)(\\rho_C\\tau_x)=\\sum_{S\\subseteq[m],\\ |S|\\le1}\\widehat f_{C,M}(S)\\chi_S(x)$. Thus $P_M$ keeps exactly the constant and singleton Fourier coefficients on each matching cube.",
      "leanLinks": [
        {
          "name": "matchingLocalProjection",
          "file": "DictatorshipTesting/Paper/Defs/S04_Def4_02a_MatchingLocalProjection.lean",
          "line": 24
        },
        {
          "name": "matchingLocalProjectionError",
          "file": "DictatorshipTesting/Paper/Defs/S04_Def4_02b_MatchingLocalProjectionError.lean",
          "line": 22
        }
      ]
    },
    {
      "id": "S04_L01",
      "label": "Lem 4.1",
      "title": "Cube square test",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_01_CubeSquare.lean",
      "wrappers": [
        "S04_Lem4_01_CubeSquare"
      ],
      "deps": [
        "S02_L03",
        "S02_D02"
      ],
      "summary": "Lem 4.1: Cube square test.",
      "statement": "Lem 4.1: Cube square test.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "lem:cube-square",
      "paperEnv": "lemma",
      "paperStatementLatex": "Choose $u,v\\in\\{0,1\\}^m$ by the following coordinate-by-coordinate rule: independently for each $r\\in[m]$, the pair $(u_r,v_r)$ is uniformly distributed over $(0,0),(1,0),(0,1)$. Then, for\nevery $g:\\{0,1\\}^m\\to\\mathbb R$,\n\\[\n  \\E_{x,u,v}\\bigl[\\Delta_{u,v}g(x)^2\\bigr]\n  \\ge \\frac{32}{9}\\norm{g-P_{\\le1}g}^2.\n\\]",
      "leanLinks": [
        {
          "name": "S04_Lem4_01_CubeSquare",
          "file": "DictatorshipTesting/Paper/S04_Lem4_01_CubeSquare.lean",
          "line": 509
        }
      ]
    },
    {
      "id": "S04_L02",
      "label": "Lem 4.2",
      "title": "P_M independent of representatives",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_02_PMIndependentOfRepresentatives.lean",
      "wrappers": [
        "S04_Lem4_02_PMIndependentOfRepresentatives"
      ],
      "deps": [
        "S02_L03",
        "S04_D02"
      ],
      "summary": "Lem 4.2: P_M independent of representatives.",
      "statement": "Lem 4.2: P_M independent of representatives.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "lem:PM-independent-representatives",
      "paperEnv": "lemma",
      "paperStatementLatex": "The value in \\eqref{eq:PM-formula} does not depend on the chosen representative\nof the coset containing $\\omega$.",
      "leanLinks": [
        {
          "name": "S04_Lem4_02_PMIndependentOfRepresentatives",
          "file": "DictatorshipTesting/Paper/S04_Lem4_02_PMIndependentOfRepresentatives.lean",
          "line": 20
        }
      ]
    },
    {
      "id": "S04_L03",
      "label": "Lem 4.3",
      "title": "P_M fixes local degree one",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_03_PMFixesLocal.lean",
      "wrappers": [
        "S04_Lem4_03_PMFixesLocal"
      ],
      "deps": [
        "S04_L02",
        "S04_D01",
        "S04_D02"
      ],
      "summary": "Lem 4.3: P_M fixes local degree one.",
      "statement": "Lem 4.3: P_M fixes local degree one.",
      "terms": [
        {
          "text": "P_M independent of representatives",
          "target": "S04_L02"
        }
      ],
      "paperLabel": "lem:PM-fixes-local",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $f:S_n\\to\\mathbb R$, the function $P_M f$ belongs to $\\mathcal W_M$.\nMoreover, if $H\\in\\mathcal W_M$, then $P_MH=H$.",
      "leanLinks": [
        {
          "name": "S04_Lem4_03_PMFixesLocal",
          "file": "DictatorshipTesting/Paper/S04_Lem4_03_PMFixesLocal.lean",
          "line": 20
        }
      ]
    },
    {
      "id": "S04_L04",
      "label": "Lem 4.4",
      "title": "Local high-degree error formula",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_04_LocalHighDegreeErrorFormula.lean",
      "wrappers": [
        "S04_Lem4_04_LocalHighDegreeErrorFormula"
      ],
      "deps": [
        "S04_L02",
        "S02_L03",
        "S04_D02"
      ],
      "summary": "Lem 4.4: Local high-degree error formula.",
      "statement": "Lem 4.4: Local high-degree error formula.",
      "terms": [
        {
          "text": "P_M independent of representatives",
          "target": "S04_L02"
        },
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "lem:local-high-degree-error-formula",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $f:S_n\\to\\mathbb R$,\n\\begin{equation}\\label{eq:PM-error-formula}\n  \\norm{(I-P_M)f}^2\n  =\\E_{C\\sim\\cC_M}\n      \\sum_{\\substack{S\\subseteq[m]\\\\ |S|\\ge2}}\n      \\widehat f_{C,M}(S)^2\n  =\\E_{C\\sim\\cC_M}\n      \\norm{g_{C,M}-P_{\\le1}g_{C,M}}^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Lem4_04_LocalHighDegreeErrorFormula",
          "file": "DictatorshipTesting/Paper/S04_Lem4_04_LocalHighDegreeErrorFormula.lean",
          "line": 22
        }
      ]
    },
    {
      "id": "S04_L05",
      "label": "Lem 4.5",
      "title": "P_M perpendicular",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_05_PMPerpendicular.lean",
      "wrappers": [
        "S04_Lem4_05_PMPerpendicular"
      ],
      "deps": [
        "S04_L03",
        "S02_L03",
        "S04_D01",
        "S04_D02"
      ],
      "summary": "Lem 4.5: P_M perpendicular.",
      "statement": "Lem 4.5: P_M perpendicular.",
      "terms": [
        {
          "text": "P_M fixes local degree one",
          "target": "S04_L03"
        },
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "lem:PM-perpendicular",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $f:S_n\\to\\mathbb R$ and every $H\\in\\mathcal W_M$,\n\\[\n  \\ip{f-P_M f}{H}=0.\n\\]\nConsequently,\n\\begin{equation}\\label{eq:PM-inner-equals-error}\n  \\ip{f}{(I-P_M)f}=\\norm{(I-P_M)f}^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Lem4_05_PMPerpendicular",
          "file": "DictatorshipTesting/Paper/S04_Lem4_05_PMPerpendicular.lean",
          "line": 112
        }
      ]
    },
    {
      "id": "S04_L06",
      "label": "Lem 4.6",
      "title": "Basic indicators have local degree at most one",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_06_TijLocalDegree.lean",
      "wrappers": [
        "S04_Lem4_06_TijLocalDegree"
      ],
      "deps": [
        "S03_L01",
        "S02_L03",
        "S04_D01"
      ],
      "summary": "Lem 4.6: Basic indicators have local degree at most one.",
      "statement": "Lem 4.6: Basic indicators have local degree at most one.",
      "terms": [
        {
          "text": "Completeness on matching cubes",
          "target": "S03_L01"
        },
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        }
      ],
      "paperLabel": "lem:tij-local-degree",
      "paperEnv": "lemma",
      "paperStatementLatex": "Fix a matching $M=\\{e_1,\\ldots,e_m\\}$, a coset $C\\in\\cC_M$, and a representative\n$\\rho_C\\in C$.  For every $i,j\\in[n]$, define\n\\begin{equation*}\n  g_{ij,C,M}(x):=t_{ij}(\\rho_C\\tau_x),\n  \\qquad x\\in\\{0,1\\}^m.\n\\end{equation*}\nThen $g_{ij,C,M}$ has Fourier coefficients only at weights $0$ and $1$.",
      "leanLinks": [
        {
          "name": "S04_Lem4_06_TijLocalDegree",
          "file": "DictatorshipTesting/Paper/S04_Lem4_06_TijLocalDegree.lean",
          "line": 100
        }
      ]
    },
    {
      "id": "S04_C07",
      "label": "Cor 4.7",
      "title": "U_1 is local",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Cor4_07_U1Local.lean",
      "wrappers": [
        "S04_Cor4_07_U1Local"
      ],
      "deps": [
        "S04_L03",
        "S04_L06",
        "S04_D01",
        "S04_D02"
      ],
      "summary": "Cor 4.7: U_1 is local.",
      "statement": "Cor 4.7: U_1 is local.",
      "terms": [
        {
          "text": "P_M fixes local degree one",
          "target": "S04_L03"
        },
        {
          "text": "Basic indicators have local degree at most one",
          "target": "S04_L06"
        }
      ],
      "paperLabel": "cor:U1-local",
      "paperEnv": "corollary",
      "paperStatementLatex": "For every matching $M$, we have\n\\begin{equation}\\label{eq:U1-contained-local-space}\n  U_1\\subseteq\\mathcal W_M.\n\\end{equation}\nConsequently,\n\\begin{equation}\\label{eq:PM-fixes-U1}\n  P_Mh=h\n  \\qquad\\text{for every }h\\in U_1.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Cor4_07_U1Local",
          "file": "DictatorshipTesting/Paper/S04_Cor4_07_U1Local.lean",
          "line": 54
        }
      ]
    },
    {
      "id": "S04_T08",
      "label": "Thm 4.8",
      "title": "Matching-cube spectral gap",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Thm4_08_MatchingGap.lean",
      "wrappers": [
        "S04_Thm4_08_MatchingGap"
      ],
      "deps": [
        "S05_L28",
        "S05_L29",
        "S04_D02"
      ],
      "summary": "Thm 4.8: Matching-cube spectral gap.",
      "statement": "Thm 4.8: Matching-cube spectral gap.",
      "terms": [
        {
          "text": "Even spectral bridge",
          "target": "S05_L28"
        },
        {
          "text": "Odd spectral bridge",
          "target": "S05_L29"
        },
        {
          "text": "even spectral bridge",
          "target": "S05_L28"
        },
        {
          "text": "odd spectral bridge",
          "target": "S05_L29"
        },
        {
          "text": "Section 5 spectral-model inputs",
          "target": "S05_L11"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        }
      ],
      "paperLabel": "thm:matching-gap",
      "paperEnv": "theorem",
      "paperStatementLatex": "For every $n\\ge4$ and every $f:S_n\\to\\mathbb R$,\n\\begin{equation}\\label{eq:matching-gap-statement}\n  \\E_M\\norm{(I-P_M)f}^2\n  \\ge \\frac16\\norm{f-P_{U_1}f}^2,\n\\end{equation}\nwhere $M$ is a uniformly random near-perfect matching.  If $n$ is even, the\nconstant $1/6$ in \\eqref{eq:matching-gap-statement} can be replaced by $1/5$.",
      "leanLinks": [
        {
          "name": "S04_Thm4_08_MatchingGap",
          "file": "DictatorshipTesting/Paper/S04_Thm4_08_MatchingGap.lean",
          "line": 40
        }
      ]
    },
    {
      "id": "S04_L09",
      "label": "Lem 4.9",
      "title": "Trial cube coordinates",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_09_TrialCubeCoordinates.lean",
      "wrappers": [
        "S04_Lem4_09_TrialCubeCoordinates"
      ],
      "deps": [
        "S04_L01"
      ],
      "summary": "Lem 4.9: Trial cube coordinates.",
      "statement": "Lem 4.9: Trial cube coordinates.",
      "terms": [
        {
          "text": "Cube square test",
          "target": "S04_L01"
        }
      ],
      "paperLabel": "lem:trial-cube-coordinates",
      "paperEnv": "lemma",
      "paperStatementLatex": "One execution of \\cref{alg:matching-trial} can be described equivalently as\nfollows.  First sample $M$ uniformly.  Then sample a coset $C\\in\\cC_M$ uniformly,\na cube point $x\\in\\{0,1\\}^m$ uniformly, and directions $u,v\\in\\{0,1\\}^m$ by the\ncoordinate-by-coordinate rule of \\Cref{lem:cube-square}.  If\n\\begin{equation*}\n  g_{C,M}(y)=f(\\rho_C\\tau_y),\n  \\qquad y\\in\\{0,1\\}^m,\n\\end{equation*}\nthen the four queried values are\n\\begin{equation}\\label{eq:trial-four-cube-values}\n  g_{C,M}(x),\\qquad g_{C,M}(x+u),\\qquad\n  g_{C,M}(x+v),\\qquad g_{C,M}(x+u+v),\n\\end{equation}\nand the algorithm rejects exactly when\n\\begin{equation}\\label{eq:trial-rejects-iff-delta-nonzero}\n  \\Delta_{u,v}g_{C,M}(x)\\neq0.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Lem4_09_TrialCubeCoordinates",
          "file": "DictatorshipTesting/Paper/S04_Lem4_09_TrialCubeCoordinates.lean",
          "line": 19
        }
      ]
    },
    {
      "id": "S04_P10",
      "label": "Prop 4.10",
      "title": "Square energy controls global degree",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Prop4_10_SquareEnergyControlsGlobalDegree.lean",
      "wrappers": [
        "S04_Prop4_10_SquareEnergyControlsGlobalDegree"
      ],
      "deps": [
        "S04_L01",
        "S04_L04",
        "S04_L09",
        "S04_T08",
        "S04_D02"
      ],
      "summary": "Prop 4.10: Square energy controls global degree.",
      "statement": "Prop 4.10: Square energy controls global degree.",
      "terms": [
        {
          "text": "Cube square test",
          "target": "S04_L01"
        },
        {
          "text": "Local high-degree error formula",
          "target": "S04_L04"
        },
        {
          "text": "Trial cube coordinates",
          "target": "S04_L09"
        },
        {
          "text": "Matching-cube spectral gap",
          "target": "S04_T08"
        },
        {
          "text": "U1",
          "target": "S02_N01"
        }
      ],
      "paperLabel": "prop:square-energy-controls-global-degree",
      "paperEnv": "proposition",
      "paperStatementLatex": "Let $\\Delta$ denote the alternating sum of the four queried values in one\nexecution of \\cref{alg:matching-trial}.  Then for every $f:S_n\\to\\mathbb R$,\n\\begin{equation}\\label{eq:square-energy-global-bound}\n  \\E[\\Delta^2]\n  \\ge\n  \\frac{16}{27}\\norm{f-P_{U_1}f}^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Prop4_10_SquareEnergyControlsGlobalDegree",
          "file": "DictatorshipTesting/Paper/S04_Prop4_10_SquareEnergyControlsGlobalDegree.lean",
          "line": 156
        }
      ]
    },
    {
      "id": "S04_L11",
      "label": "Lem 4.11",
      "title": "One-trial soundness",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_11_OneTrialSoundness.lean",
      "wrappers": [
        "S04_Lem4_11_OneTrialSoundness"
      ],
      "deps": [
        "S02_T02",
        "S04_P10"
      ],
      "summary": "Lem 4.11: One-trial soundness.",
      "statement": "Lem 4.11: One-trial soundness.",
      "terms": [
        {
          "text": "FKN/stability input",
          "target": "S02_T02"
        },
        {
          "text": "Square energy controls global degree",
          "target": "S04_P10"
        }
      ],
      "paperLabel": "lem:one-trial-soundness",
      "paperEnv": "lemma",
      "paperStatementLatex": "There is an absolute constant $c_0>0$ such that one execution of\n\\cref{alg:matching-trial} rejects every Boolean $f:S_n\\to\\{0,1\\}$ with\nprobability at least\n\\begin{equation}\\label{eq:one-trial-soundness-bound}\n  c_0\\,\\dist(f,\\D)^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S04_Lem4_11_OneTrialSoundness",
          "file": "DictatorshipTesting/Paper/S04_Lem4_11_OneTrialSoundness.lean",
          "line": 155
        }
      ]
    },
    {
      "id": "S04_L12",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "Let a one-sided finite-seed tester make $Q$ queries and reject a fixed function\nwith probability $p$.  Repeating it independently $k$ times and rejecting if\nany copy rejects gives a one-sided nonadaptive tester with $kQ$ queries and\nrejection probability\n\\begin{equation}\\label{eq:repetition-rejection-formula}\n  1-(1-p)^k.\n\\end{equation}\nMoreover, for $0\\le p\\le1$,\n\\begin{equation}\\label{eq:reciprocal-amplification-bound}\n  (1-p)^k\\le \\frac{1}{1+kp}.\n\\end{equation}\nConsequently, if $kp\\ge2$, the repeated tester rejects with probability at\nleast $2/3$.",
      "label": "Lem 4.12",
      "title": "Independent repetition and amplification",
      "file": "DictatorshipTesting/Paper/S04_Lem4_12_IndependentRepetitionAndAmplification.lean",
      "wrappers": [
        "S04_Lem4_12_repetition_rejection_probability",
        "S04_Lem4_12_dimension_free_amplification"
      ],
      "deps": [
        "S04_L11",
        "S03_L02"
      ],
      "summary": "Lem 4.12: Independent repetition and amplification.",
      "statement": "Lem 4.12: Independent repetition and amplification.",
      "leanLinks": [
        {
          "name": "S04_Lem4_12_repetition_rejection_probability",
          "file": "DictatorshipTesting/Paper/S04_Lem4_12_IndependentRepetitionAndAmplification.lean",
          "line": 14
        },
        {
          "name": "S04_Lem4_12_dimension_free_amplification",
          "file": "DictatorshipTesting/Paper/S04_Lem4_12_IndependentRepetitionAndAmplification.lean",
          "line": 21
        }
      ],
      "paperLabel": "lem:independent-repetition",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_D01",
      "label": "Def 5.1",
      "title": "Young diagrams and boxes",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean",
      "wrappers": [
        "S05_Def5_01_YoungDiagram",
        "S05_Def5_01_youngRow",
        "S05_Def5_01_youngCells"
      ],
      "deps": [],
      "summary": "Def 5.1: Young diagrams and boxes.",
      "statement": "Def 5.1: Young diagrams and boxes.",
      "terms": [],
      "paperLabel": "def:young-diagrams-boxes",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda=(\\lambda_1,\\ldots,\\lambda_\\ell)\\vdash N$.  We identify\n$\\lambda$ with its Young diagram\n\\begin{equation*}\n  [\\lambda]:=\\{(r,c):1\\le r\\le \\ell,\\ 1\\le c\\le \\lambda_r\\},\n\\end{equation*}\nwhere rows and columns are numbered from $1$.  A \\emph{box} of $\\lambda$ is an\nordered pair $u=(r,c)\\in[\\lambda]$; write $\\row(u)=r$ and $\\col(u)=c$.",
      "leanLinks": [
        {
          "name": "S05_Def5_01_YoungDiagram",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean",
          "line": 22
        },
        {
          "name": "S05_Def5_01_youngRow",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean",
          "line": 25
        },
        {
          "name": "S05_Def5_01_youngCells",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean",
          "line": 29
        }
      ]
    },
    {
      "id": "S05_L01",
      "label": "Lem 5.1",
      "title": "Tableau Coxeter model for adjacent transpositions",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean",
      "wrappers": [
        "S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel"
      ],
      "deps": [
        "S05_D05"
      ],
      "summary": "Lem 5.1: Tableau Coxeter model for adjacent transpositions.",
      "statement": "Lem 5.1: Tableau Coxeter model for adjacent transpositions.",
      "terms": [
        {
          "text": "Contents and adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Young adjacent operators",
          "target": "S05_D05"
        }
      ],
      "paperLabel": "lem:young-adjacent-matrices",
      "paperEnv": "lemma",
      "paperStatementLatex": "The operators $S_k^\\lambda$ have the displayed same-row, same-column, and\n$2\\times2$ Young-orthogonal local form.  Moreover they satisfy the type-$A$\nCoxeter relations\n\\begin{equation}\\label{eq:young-coxeter-relations}\n  (S_i^\\lambda)^2=I,\\qquad\n  S_i^\\lambda S_j^\\lambda=S_j^\\lambda S_i^\\lambda\\quad(|i-j|>1),\n  \\qquad\n  S_i^\\lambda S_{i+1}^\\lambda S_i^\\lambda\n  =S_{i+1}^\\lambda S_i^\\lambda S_{i+1}^\\lambda .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel",
          "file": "DictatorshipTesting/Paper/S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean",
          "line": 1600
        }
      ]
    },
    {
      "id": "S05_D02",
      "label": "Def 5.2",
      "title": "Removable corners and one-box removals",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_02_RemovableCorners.lean",
      "wrappers": [
        "S05_Def5_02_IsYoungSubdiagram",
        "S05_Def5_02_IsOneBoxChild",
        "S05_Def5_02_oneBoxChildren",
        "S05_Def5_02_IsRemovableRow"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Def 5.2: Removable corners and one-box removals.",
      "statement": "Def 5.2: Removable corners and one-box removals.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "one-box removals",
          "target": "S05_D07"
        }
      ],
      "paperLabel": "def:removable-corners",
      "paperEnv": "definition",
      "paperStatementLatex": "A box $u$ of a Young diagram $\\lambda$ is a \\emph{removable corner} if\n$[\\lambda]\\setminus\\{u\\}$ is again the Young diagram of a partition.  In\ncoordinates this means $u=(r,\\lambda_r)$ and $\\lambda_r>\\lambda_{r+1}$, with\nthe convention $\\lambda_{\\ell+1}=0$.  We write $\\Rem(\\lambda)$ for the set of\nremovable corners.  If $[\\mu]\\subseteq[\\lambda]$, then $\\lambda\\setminus\\mu$\ndenotes the set of boxes $[\\lambda]\\setminus[\\mu]$.  If $u\\in\\Rem(\\lambda)$,\nthen $\\lambda\\setminus\\{u\\}$ denotes the partition whose Young diagram is\n$[\\lambda]\\setminus\\{u\\}$.",
      "leanLinks": [
        {
          "name": "S05_Def5_02_IsYoungSubdiagram",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_02_RemovableCorners.lean",
          "line": 23
        },
        {
          "name": "S05_Def5_02_IsOneBoxChild",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_02_RemovableCorners.lean",
          "line": 28
        },
        {
          "name": "S05_Def5_02_oneBoxChildren",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_02_RemovableCorners.lean",
          "line": 33
        },
        {
          "name": "S05_Def5_02_IsRemovableRow",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_02_RemovableCorners.lean",
          "line": 37
        }
      ]
    },
    {
      "id": "S05_L02",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "Let words in the generators $s_1,\\ldots,s_{N-1}$ be identified under the\nrelations $s_i^2=1$, $s_is_j=s_js_i$ for $|i-j|>1$, and\n$s_is_{i+1}s_i=s_{i+1}s_is_{i+1}$.  Two adjacent words represent the same\npermutation in $S_N$ if and only if they are equivalent under these relations.",
      "label": "Lem 5.2",
      "title": "Type-A adjacent-word presentation",
      "file": "DictatorshipTesting/Paper/S05_Lem5_02_TypeAAdjacentWordPresentation.lean",
      "wrappers": [
        "S05_Lem5_02_typeA_adjacentWord_presentation"
      ],
      "deps": [
        "S05_L01"
      ],
      "summary": "Lem 5.2: Type-A adjacent-word presentation.",
      "statement": "Lem 5.2: Type-A adjacent-word presentation.",
      "leanLinks": [
        {
          "name": "S05_Lem5_02_typeA_adjacentWord_presentation",
          "file": "DictatorshipTesting/Paper/S05_Lem5_02_TypeAAdjacentWordPresentation.lean",
          "line": 16
        }
      ],
      "paperLabel": "lem:type-A-adjacent-word-presentation",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_D03",
      "label": "Def 5.3",
      "title": "Standard Young tableaux and occupation notation",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_03_StandardTableaux.lean",
      "wrappers": [
        "S05_Def5_03_StandardYoungTableau",
        "S05_Def5_03_cellOfEntry",
        "S05_Def5_03_TableauMaxAt"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Def 5.3: Standard Young tableaux and occupation notation.",
      "statement": "Def 5.3: Standard Young tableaux and occupation notation.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        }
      ],
      "paperLabel": "def:standard-tableaux",
      "paperEnv": "definition",
      "paperStatementLatex": "A \\emph{standard Young tableau} of shape $\\lambda$ is a bijection\n$T:[\\lambda]\\to[N]$ such that entries strictly increase along rows and columns:\n\\begin{equation*}\n  T(r,c)<T(r,c+1),\\qquad T(r,c)<T(r+1,c)\n\\end{equation*}\nwhenever the displayed boxes lie in $[\\lambda]$.  Let $\\SYT(\\lambda)$ denote the\nset of standard Young tableaux of shape $\\lambda$.  If $T(u)=a$, we say that\n$a$ occupies the box $u$ and write $u_T(a)=u$.",
      "leanLinks": [
        {
          "name": "S05_Def5_03_StandardYoungTableau",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_03_StandardTableaux.lean",
          "line": 22
        },
        {
          "name": "S05_Def5_03_cellOfEntry",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_03_StandardTableaux.lean",
          "line": 26
        },
        {
          "name": "S05_Def5_03_TableauMaxAt",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_03_StandardTableaux.lean",
          "line": 31
        }
      ]
    },
    {
      "id": "S05_T03",
      "label": "Thm 5.3",
      "title": "Young orthogonal action",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Thm5_03_YoungOrthogonalAction.lean",
      "wrappers": [
        "S05_Thm5_03_youngOrthogonalAction"
      ],
      "deps": [
        "S05_L02"
      ],
      "summary": "Thm 5.3: Young orthogonal action.",
      "statement": "Thm 5.3: Young orthogonal action.",
      "terms": [],
      "paperLabel": "thm:young-orthogonal-action",
      "paperEnv": "theorem",
      "paperStatementLatex": "For every $\\lambda\\vdash N$, there is an orthogonal representation\n\\[\n  \\rho^\\lambda:S_N\\to\\operatorname{GL}(V^\\lambda)\n\\]\nsuch that $\\rho^\\lambda(s_i)=S_i^\\lambda$ for every adjacent transposition.",
      "leanLinks": [
        {
          "name": "S05_Thm5_03_youngOrthogonalAction",
          "file": "DictatorshipTesting/Paper/S05_Thm5_03_YoungOrthogonalAction.lean",
          "line": 34
        }
      ]
    },
    {
      "id": "S05_D04",
      "label": "Def 5.4",
      "title": "Tableau coordinate space",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_04_TableauCoordinateSpace.lean",
      "wrappers": [
        "S05_Def5_04_tableauDim",
        "S05_Def5_04_TableauSpace",
        "S05_Def5_04_tableauBasisVec"
      ],
      "deps": [
        "S05_D03"
      ],
      "summary": "Def 5.4: Tableau coordinate space.",
      "statement": "Def 5.4: Tableau coordinate space.",
      "terms": [
        {
          "text": "Standard tableaux and occupation",
          "target": "S05_D03"
        },
        {
          "text": "Young adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        }
      ],
      "paperLabel": "def:tableau-coordinate-space",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash N$, set\n\\begin{equation*}\n  d_\\lambda:=|\\SYT(\\lambda)|.\n\\end{equation*}\nLet $V^\\lambda$ be the vector space with orthonormal basis\n$\\{e_T:T\\in\\SYT(\\lambda)\\}$.  We write\n\\begin{equation*}\n  s_k=(k,k+1),\\qquad 1\\le k<N.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Def5_04_tableauDim",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_04_TableauCoordinateSpace.lean",
          "line": 24
        },
        {
          "name": "S05_Def5_04_TableauSpace",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_04_TableauCoordinateSpace.lean",
          "line": 28
        },
        {
          "name": "S05_Def5_04_tableauBasisVec",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_04_TableauCoordinateSpace.lean",
          "line": 32
        }
      ]
    },
    {
      "id": "S05_L04",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "Let $J_1=0$ and $J_k=\\sum_{i<k}(i,k)$ for $2\\le k\\le N$.  Then\n\\begin{equation}\\label{eq:jucys-murphy-recurrence}\n  J_{k+1}=s_kJ_ks_k+s_k.\n\\end{equation}\nThe tableau content operators satisfy the matching recurrence\n\\begin{equation}\\label{eq:tableau-content-recurrence}\n  C_{k+1}^\\lambda\n  =S_k^\\lambda C_k^\\lambda S_k^\\lambda+S_k^\\lambda.\n\\end{equation}",
      "label": "Lem 5.4",
      "title": "Jucys--Murphy recurrences",
      "file": "DictatorshipTesting/Paper/S05_Lem5_04_JucysMurphyRecurrences.lean",
      "wrappers": [
        "S05_Lem5_04_jucysMurphyElement_succ_recurrence",
        "S05_Lem5_04_tableauContent_succ_recurrence"
      ],
      "deps": [
        "S05_L01",
        "S05_T03"
      ],
      "summary": "Lem 5.4: Jucys--Murphy recurrences.",
      "statement": "Lem 5.4: Jucys--Murphy recurrences.",
      "leanLinks": [
        {
          "name": "S05_Lem5_04_jucysMurphyElement_succ_recurrence",
          "file": "DictatorshipTesting/Paper/S05_Lem5_04_JucysMurphyRecurrences.lean",
          "line": 15
        },
        {
          "name": "S05_Lem5_04_tableauContent_succ_recurrence",
          "file": "DictatorshipTesting/Paper/S05_Lem5_04_JucysMurphyRecurrences.lean",
          "line": 24
        }
      ],
      "paperLabel": "lem:jucys-murphy-recurrence",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_D05",
      "label": "Def 5.5",
      "title": "Contents and adjacent operators",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_05_ContentAndAdjacentOperators.lean",
      "wrappers": [
        "S05_Def5_05_cellContent",
        "S05_Def5_05_entryContent",
        "S05_Def5_05_youngAdjacentOperator",
        "S05_Def5_05_diagonalContentOperator"
      ],
      "deps": [
        "S05_D04"
      ],
      "summary": "Def 5.5: Contents and adjacent operators.",
      "statement": "Def 5.5: Contents and adjacent operators.",
      "terms": [
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        }
      ],
      "paperLabel": "def:content-adjacent-operators",
      "paperEnv": "definition",
      "paperStatementLatex": "For a box $u$, set $c(u)=\\col(u)-\\row(u)$.  If $T\\in\\SYT(\\lambda)$ and\n$a\\in[N]$, set $c_T(a):=c(u_T(a))$.\n\nFor each adjacent index $k$, define a concrete operator\n$S_k^\\lambda\\in\\End(V^\\lambda)$ as follows.  If $k$ and $k+1$ lie in the same\nrow of $T$, set $S_k^\\lambda e_T=e_T$.  If they lie in the same column, set\n$S_k^\\lambda e_T=-e_T$.  Otherwise let $T'=s_kT$ be the tableau obtained by\nswapping the entries $k$ and $k+1$; in this case $T'$ is standard.  On the span\nof $e_T$ and $e_{T'}$, set\n\\begin{equation}\\label{eq:young-orthogonal-two-by-two}\n  S_k^\\lambda\\big|_{\\spanop\\{e_T,e_{T'}\\}}\n  =\n  \\begin{pmatrix}\n    a & b\\\\\n    b & -a\n  \\end{pmatrix},\n  \\qquad\n  a=\\frac{1}{c_T(k+1)-c_T(k)},\n  \\qquad\n  b=\\sqrt{1-a^2},\n\\end{equation}\nwith respect to the ordered basis $(e_T,e_{T'})$.  The formula is independent\nof the choice of representative of the unordered pair $\\{T,T'\\}$, since the\naxial distance changes sign after the swap.\n\nFor $1\\le k\\le N$, define the diagonal content operator\n$C_k^\\lambda\\in\\End(V^\\lambda)$ by\n\\begin{equation}\\label{eq:content-diagonal-operator}\n  C_k^\\lambda e_T=c_T(k)e_T.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Def5_05_cellContent",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_05_ContentAndAdjacentOperators.lean",
          "line": 23
        },
        {
          "name": "S05_Def5_05_entryContent",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_05_ContentAndAdjacentOperators.lean",
          "line": 28
        },
        {
          "name": "S05_Def5_05_youngAdjacentOperator",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_05_ContentAndAdjacentOperators.lean",
          "line": 33
        },
        {
          "name": "S05_Def5_05_diagonalContentOperator",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_05_ContentAndAdjacentOperators.lean",
          "line": 38
        }
      ]
    },
    {
      "id": "S05_T05",
      "label": "Thm 5.5",
      "title": "Jucys--Murphy content action",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Thm5_05_JucysMurphyContentAction.lean",
      "wrappers": [
        "S05_Thm5_05_jucysMurphyContentAction"
      ],
      "deps": [
        "S05_T03",
        "S05_L04"
      ],
      "summary": "Thm 5.5: Jucys--Murphy content action.",
      "statement": "Thm 5.5: Jucys--Murphy content action.",
      "terms": [],
      "paperLabel": "thm:jucys-murphy-content",
      "paperEnv": "theorem",
      "paperStatementLatex": "For every $\\lambda\\vdash N$, every $1\\le k\\le N$, and every\n$T\\in\\SYT(\\lambda)$,\n\\begin{equation}\\label{eq:jucys-murphy-diagonal}\n  \\rho^\\lambda(J_k)e_T=C_k^\\lambda e_T=c_T(k)e_T.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Thm5_05_jucysMurphyContentAction",
          "file": "DictatorshipTesting/Paper/S05_Thm5_05_JucysMurphyContentAction.lean",
          "line": 33
        }
      ]
    },
    {
      "id": "S05_D06",
      "label": "Def 5.6",
      "title": "Young matrix coefficients, blocks, and energies",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_06a_YoungBlock.lean",
      "wrappers": [],
      "deps": [
        "S05_T03"
      ],
      "summary": "Def 5.6: Young matrix coefficients, blocks, and energies.",
      "statement": "Def 5.6: Young matrix coefficients, blocks, and energies.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        },
        {
          "text": "Young-block energy profile",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "def:young-block",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash n$ and $S,T\\in\\SYT(\\lambda)$, define\n\\[\n  \\Phi_{S,T}^\\lambda(\\pi)\n  :=\\langle e_S,\\rho^\\lambda(\\pi)e_T\\rangle.\n\\]\nThe Young matrix-coefficient block is\n\\begin{equation}\\label{eq:regular-young-decomposition}\n  \\mathcal H_\\lambda\n  :=\\spanop\\{\\Phi_{S,T}^\\lambda:S,T\\in\\SYT(\\lambda)\\}\n  \\subseteq L^2(S_n;\\mathbb C).\n\\end{equation}\nLet $F_\\lambda$ denote the orthogonal projection of $F$ onto\n$\\mathcal H_\\lambda$, and set\n\\[\n  E_F(\\lambda):=\\|F_\\lambda\\|_2^2.\n\\]",
      "leanLinks": []
    },
    {
      "id": "S05_L06",
      "label": "Lem 5.6",
      "title": "Diagonal content eigenspaces",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_06_DiagonalContentEigenspaces.lean",
      "wrappers": [
        "S05_Lem5_06_diagonalContentEigenspaces"
      ],
      "deps": [
        "S05_D05",
        "S05_T05"
      ],
      "summary": "Lem 5.6: Diagonal content eigenspaces.",
      "statement": "Lem 5.6: Diagonal content eigenspaces.",
      "terms": [
        {
          "text": "Contents and adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "S05_T05"
        }
      ],
      "paperLabel": "lem:jucys-murphy-eigenbasis",
      "paperEnv": "lemma",
      "paperStatementLatex": "The common eigenspaces of $C_1^\\lambda,\\ldots,C_N^\\lambda$ are exactly\nthe lines $\\mathbb C e_T$, $T\\in\\SYT(\\lambda)$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_06_diagonalContentEigenspaces",
          "file": "DictatorshipTesting/Paper/S05_Lem5_06_DiagonalContentEigenspaces.lean",
          "line": 648
        }
      ]
    },
    {
      "id": "S05_D07",
      "label": "Def 5.7",
      "title": "Branching data",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_07a_TwoBoxRemovals.lean",
      "wrappers": [],
      "deps": [
        "S05_D02"
      ],
      "summary": "Def 5.7: Branching data.",
      "statement": "Def 5.7: Branching data.",
      "terms": [
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        },
        {
          "text": "Two-box removals",
          "target": "S05_D07"
        },
        {
          "text": "two-box removals",
          "target": "S05_D07"
        },
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        },
        {
          "text": "one-box children",
          "target": "S05_D02"
        }
      ],
      "paperLabel": "def:branching-data",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda\\vdash N$.\n\\begin{enumerate}[label=(\\alph*)]\n\\item\\label[definition]{def:two-box-removals}\nIf $N\\ge2$, define\n\\begin{align*}\n  \\mathsf H_2(\\lambda)\n  &:=\\{\\mu\\vdash N-2:\\lambda\\setminus\\mu\n      \\text{ has two boxes and no two lie in the same column}\\},\\\\\n  \\mathsf V_2(\\lambda)\n  &:=\\{\\mu\\vdash N-2:\\lambda\\setminus\\mu\n      \\text{ has two boxes and no two lie in the same row}\\}.\n\\end{align*}\nA disconnected two-box removal belongs to both sets.\n\n\\item\\label[definition]{def:signed-two-box-removals}\nSet\n\\[\n  \\mathsf B_2(\\lambda)\n  :=\\{(\\mu,+):\\mu\\in\\mathsf H_2(\\lambda)\\}\n    \\uplus\n    \\{(\\mu,-):\\mu\\in\\mathsf V_2(\\lambda)\\},\n  \\qquad\n  \\varepsilon_+=1,\n  \\quad\n  \\varepsilon_-=-1.\n\\]\nThe union is a disjoint union of signed occurrences, so a disconnected removal\nappears once with each sign.\n\n\\item\\label[definition]{def:one-box-removals}\nFor $\\mu\\vdash N-1$, write $\\mu\\nearrow\\lambda$ when\n$[\\mu]=[\\lambda]\\setminus\\{u\\}$ for some $u\\in\\Rem(\\lambda)$.\n\\end{enumerate}",
      "leanLinks": []
    },
    {
      "id": "S05_L07",
      "label": "Lem 5.7",
      "title": "Connectedness of standard tableaux",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_07_ConnectednessOfStandardTableaux.lean",
      "wrappers": [
        "S05_Lem5_07_standardTableauxSwapConnectedness"
      ],
      "deps": [
        "S05_D03"
      ],
      "summary": "Lem 5.7: Connectedness of standard tableaux.",
      "statement": "Lem 5.7: Connectedness of standard tableaux.",
      "terms": [
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        }
      ],
      "paperLabel": "lem:tableau-swap-connected",
      "paperEnv": "lemma",
      "paperStatementLatex": "For a fixed Young diagram $\\lambda$, the graph on $\\SYT(\\lambda)$ in which\n$T$ is adjacent to $s_iT$ whenever $s_iT$ is again standard is connected.",
      "leanLinks": [
        {
          "name": "S05_Lem5_07_standardTableauxSwapConnectedness",
          "file": "DictatorshipTesting/Paper/S05_Lem5_07_ConnectednessOfStandardTableaux.lean",
          "line": 549
        }
      ]
    },
    {
      "id": "S05_D08",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "terms": [],
      "paperStatementLatex": "Fix $(\\mu,\\sigma)\\in\\mathsf B_2(\\lambda)$ and write\n$B=[\\lambda]\\setminus[\\mu]$.  For $U\\in\\SYT(\\mu)$, let $E_U$ be the span of\nthe standard extensions obtained by placing $N-1,N$ in $B$.  If $B$ lies in\none row or one column, let $\\eta_{U,\\sigma}$ be the unique unit extension with\nthe corresponding sign.  If the two boxes are in different rows and columns,\nlet $\\eta_{U,+}$ and $\\eta_{U,-}$ be the normalized $+1$ and $-1$\neigenvectors of $S_{N-1}^\\lambda$ in the two-dimensional space $E_U$.\nDefine\n\\[\n  W_{\\mu,\\sigma}\n  :=\\spanop\\{\\eta_{U,\\sigma}:U\\in\\SYT(\\mu)\\},\n  \\qquad\n  D_{\\mu,\\sigma}(\\eta_{U,\\sigma}):=e_U.\n\\]",
      "label": "Def 5.8",
      "title": "Signed two-box extension spaces",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_08_SignedTwoBoxExtensionSpaces.lean",
      "wrappers": [
        "S05_Def5_08_signedTwoBoxExtensionBasisVector"
      ],
      "deps": [
        "S05_D07"
      ],
      "summary": "Def 5.8: Signed two-box extension spaces.",
      "statement": "Def 5.8: Signed two-box extension spaces.",
      "leanLinks": [
        {
          "name": "S05_Def5_08_signedTwoBoxExtensionBasisVector",
          "file": "DictatorshipTesting/Paper/Defs/S05_Def5_08_SignedTwoBoxExtensionSpaces.lean",
          "line": 18
        }
      ],
      "paperLabel": "def:signed-two-box-extension-spaces",
      "paperEnv": "definition"
    },
    {
      "id": "S05_L08",
      "label": "Lem 5.8",
      "title": "Young-basis scalar commutant",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_08_YoungBasisScalarCommutant.lean",
      "wrappers": [
        "S05_Lem5_08_youngModelOperator_scalar_on_basis"
      ],
      "deps": [
        "S05_L06",
        "S05_L07"
      ],
      "summary": "Lem 5.8: Young-basis scalar commutant.",
      "statement": "Lem 5.8: Young-basis scalar commutant.",
      "terms": [
        {
          "text": "Central averaged rejection",
          "target": "S05_L24"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "S05_L07"
        },
        {
          "text": "Diagonal content eigenspaces",
          "target": "S05_L06"
        }
      ],
      "paperLabel": "lem:young-basis-scalar-commutant",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $B\\in\\End(V^\\lambda)$.  If $B$ commutes with every content operator\n$C_k^\\lambda$ and every adjacent operator $S_i^\\lambda$, then\n\\[\n  B=\\frac{\\operatorname{tr}B}{d_\\lambda}I.\n\\]",
      "leanLinks": [
        {
          "name": "S05_Lem5_08_youngModelOperator_scalar_on_basis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_08_YoungBasisScalarCommutant.lean",
          "line": 145
        }
      ]
    },
    {
      "id": "S05_D09",
      "label": "Def 5.9",
      "title": "One-box deletion spaces",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_09_OneBoxDeletionSpaces.lean",
      "wrappers": [],
      "deps": [
        "S05_D02",
        "S05_D03"
      ],
      "summary": "Def 5.9: One-box deletion spaces.",
      "statement": "Def 5.9: One-box deletion spaces.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D07"
        },
        {
          "text": "coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L15"
        }
      ],
      "paperLabel": "def:one-box-deletion-spaces",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda\\vdash N$ and $u\\in\\Rem(\\lambda)$.  Put\n\\begin{equation*}\n  \\mu_u:=\\lambda\\setminus\\{u\\},\n  \\qquad\n  W_u:=\\spanop\\{e_T:T\\in\\SYT(\\lambda),\\ T(u)=N\\}\\subseteq V^\\lambda .\n\\end{equation*}\nDefine the deletion map $D_u:W_u\\rightarrow V^{\\mu_u}$ on basis vectors by\n\\begin{equation*}\n  D_u(e_T):=e_{T|_{[\\mu_u]}} .\n\\end{equation*}",
      "leanLinks": []
    },
    {
      "id": "S05_L09",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "For partitions $\\lambda,\\mu\\vdash n$ and tableaux of the indicated shapes,\n\\begin{equation}\\label{eq:young-matrix-coefficient-orthogonality}\n  \\left\\langle\\Phi_{S,T}^\\lambda,\\Phi_{U,V}^\\mu\\right\\rangle\n  =\\begin{cases}\n    d_\\lambda^{-1},&\\lambda=\\mu,\\ S=U,\\ T=V,\\\\\n    0,&\\text{otherwise}.\n  \\end{cases}\n\\end{equation}",
      "label": "Lem 5.9",
      "title": "Orthogonality of Young matrix coefficients",
      "file": "DictatorshipTesting/Paper/S05_Lem5_09_YoungMatrixCoefficientOrthogonality.lean",
      "wrappers": [
        "S05_Lem5_09_same_shape",
        "S05_Lem5_09_distinct_shapes"
      ],
      "deps": [
        "S05_L08",
        "S05_T05",
        "S05_D06"
      ],
      "summary": "Lem 5.9: Orthogonality of Young matrix coefficients.",
      "statement": "Lem 5.9: Orthogonality of Young matrix coefficients.",
      "leanLinks": [
        {
          "name": "S05_Lem5_09_same_shape",
          "file": "DictatorshipTesting/Paper/S05_Lem5_09_YoungMatrixCoefficientOrthogonality.lean",
          "line": 22
        },
        {
          "name": "S05_Lem5_09_distinct_shapes",
          "file": "DictatorshipTesting/Paper/S05_Lem5_09_YoungMatrixCoefficientOrthogonality.lean",
          "line": 33
        }
      ],
      "paperLabel": "lem:young-matrix-coefficient-orthogonality",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_D10",
      "label": "Def 5.10",
      "title": "Matching sign-pattern multisets and heights",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_10a_EvenSignPatternMultiset.lean",
      "wrappers": [],
      "deps": [
        "S05_D07"
      ],
      "summary": "Def 5.10: Matching sign-pattern multisets and heights.",
      "statement": "Def 5.10: Matching sign-pattern multisets and heights.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D07"
        },
        {
          "text": "One-box removals",
          "target": "S05_D07"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D10"
        },
        {
          "text": "Tableau even height",
          "target": "S05_D10"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D10"
        }
      ],
      "paperLabel": "def:matching-sign-patterns",
      "paperEnv": "definition",
      "paperStatementLatex": "\\begin{enumerate}[label=(\\alph*)]\n\\item\\label[definition]{def:even-sign-patterns}\nFor $\\lambda\\vdash2m$, define a multiset $\\mathsf X_m(\\lambda)$ of subsets of\n$[m]$ by\n\\[\n  \\mathsf X_1((2))=\\{\\emptyset\\},\n  \\qquad\n  \\mathsf X_1((1,1))=\\{\\{1\\}\\},\n\\]\nand, for $m\\ge2$,\n\\begin{equation}\\label{eq:X-recursion-even}\n\\begin{aligned}\n  \\mathsf X_m(\\lambda)\n  :=&\\biguplus_{\\mu\\in\\mathsf H_2(\\lambda)}\n      \\{R:R\\in\\mathsf X_{m-1}(\\mu)\\}\\\\\n   &\\uplus\n     \\biguplus_{\\mu\\in\\mathsf V_2(\\lambda)}\n      \\{R\\cup\\{m\\}:R\\in\\mathsf X_{m-1}(\\mu)\\}.\n\\end{aligned}\n\\end{equation}\nSet\n\\[\n  z_m(\\lambda):=\\#\\{R\\in\\mathsf X_m(\\lambda):R=\\emptyset\\},\n  \\qquad\n  h_m(\\lambda):=\\#\\{R\\in\\mathsf X_m(\\lambda):|R|\\ge2\\}.\n\\]\n\n\\item\\label[definition]{def:odd-sign-patterns}\nFor $\\lambda\\vdash2m+1$, define\n\\begin{equation}\\label{eq:X-recursion-odd}\n  \\mathsf X_m^{\\mathrm{odd}}(\\lambda)\n  :=\\biguplus_{\\mu\\nearrow\\lambda}\\mathsf X_m(\\mu),\n\\end{equation}\nand\n\\[\n  h_m^{\\mathrm{odd}}(\\lambda)\n  :=\\#\\{R\\in\\mathsf X_m^{\\mathrm{odd}}(\\lambda):|R|\\ge2\\}.\n\\]\n\\end{enumerate}\nAll unions are multiset unions; repeated child shapes retain their\nmultiplicity.",
      "leanLinks": []
    },
    {
      "id": "S05_L10",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "For every $n\\ge0$,\n\\begin{equation}\\label{eq:young-tableau-sum-of-squares}\n  \\sum_{\\lambda\\vdash n}d_\\lambda^2=n!.\n\\end{equation}",
      "label": "Lem 5.10",
      "title": "Young-lattice sum of squares",
      "file": "DictatorshipTesting/Paper/S05_Lem5_10_YoungTableauSumOfSquares.lean",
      "wrappers": [
        "S05_Lem5_10_youngTableau_sum_of_squares"
      ],
      "deps": [
        "S05_D07"
      ],
      "summary": "Lem 5.10: Young-lattice sum of squares.",
      "statement": "Lem 5.10: Young-lattice sum of squares.",
      "leanLinks": [
        {
          "name": "S05_Lem5_10_youngTableau_sum_of_squares",
          "file": "DictatorshipTesting/Paper/S05_Lem5_10_YoungTableauSumOfSquares.lean",
          "line": 14
        }
      ],
      "paperLabel": "lem:young-tableau-sum-of-squares",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_D11",
      "label": "Def 5.11",
      "title": "Matching characters and eigenvectors",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_11a_MatchingCharacters.lean",
      "wrappers": [],
      "deps": [
        "S05_D05",
        "S05_D10"
      ],
      "summary": "Def 5.11: Matching characters and eigenvectors.",
      "statement": "Def 5.11: Matching characters and eigenvectors.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "S02_L03"
        },
        {
          "text": "Matching operators",
          "target": "S05_L01"
        },
        {
          "text": "Matching operators",
          "target": "S05_L01"
        }
      ],
      "paperLabel": "def:matching-characters-and-eigenvectors",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $M=(\\tau_1,\\ldots,\\tau_m)$ be an ordered matching and put\n\\[\n  A_M:=\\{\\tau_x:x\\in\\{0,1\\}^m\\},\n  \\qquad\n  \\tau_x:=\\prod_{r:x_r=1}\\tau_r,\n  \\qquad\n  \\chi_R(\\tau_x):=(-1)^{\\sum_{r\\in R}x_r}.\n\\]\nThe product is order-independent because the edge transpositions commute.\nA vector $v\\in V^\\lambda$ is an $M$-matching eigenvector with label\n$R\\subseteq[m]$ when\n\\begin{equation}\\label{eq:matching-eigenbasis-definition}\n  \\rho^\\lambda(\\tau_x)v=\\chi_R(\\tau_x)v\n  \\qquad(x\\in\\{0,1\\}^m).\n\\end{equation}\nFor a perfect matching on $[2m]$ this is the even case, and for a near-perfect\nmatching on $[2m+1]$ it is the odd case.",
      "leanLinks": []
    },
    {
      "id": "S05_L11",
      "label": "Lem 5.11",
      "title": "Regular Young-block decomposition",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_11_RegularYoungBlockDecomposition.lean",
      "wrappers": [
        "S05_Lem5_11_globalYoungMatrixCoefficient_linearIndependent",
        "S05_Lem5_11_globalYoungMatrixCoefficient_span_all",
        "S05_Lem5_11_parseval"
      ],
      "deps": [
        "S05_L09",
        "S05_L10",
        "S05_D06"
      ],
      "summary": "Lem 5.11: Regular Young-block decomposition.",
      "statement": "Lem 5.11: Regular Young-block decomposition.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D06"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D06"
        },
        {
          "text": "Young orthogonal realization",
          "target": "S05_T03"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "S05_T05"
        },
        {
          "text": "Degree-one Young-block identification",
          "target": "S05_L12"
        },
        {
          "text": "Block scalar of averaged rejection",
          "target": "S05_L25"
        },
        {
          "text": "Diagonal content eigenspaces",
          "target": "S05_L06"
        }
      ],
      "paperLabel": "lem:regular-young-block-decomposition",
      "paperEnv": "lemma",
      "paperStatementLatex": "The functions\n\\[\n  \\sqrt{d_\\lambda}\\,\\Phi_{S,T}^\\lambda,\n  \\qquad\n  \\lambda\\vdash n,\\quad S,T\\in\\SYT(\\lambda),\n\\]\nform an orthonormal basis of $L^2(S_n;\\mathbb C)$.  Consequently,\n\\begin{equation}\\label{eq:regular-young-orthogonal-sum}\n  L^2(S_n;\\mathbb C)\n  =\\bigoplus_{\\lambda\\vdash n}\\mathcal H_\\lambda,\n  \\qquad\n  \\dim\\mathcal H_\\lambda=d_\\lambda^2,\n\\end{equation}\nand every $F$ has a unique orthogonal decomposition\n$F=\\sum_{\\lambda\\vdash n}F_\\lambda$ with\n$F_\\lambda\\in\\mathcal H_\\lambda$ and\n\\begin{equation}\\label{eq:young-block-parseval}\n  \\|F\\|_2^2=\\sum_{\\lambda\\vdash n}E_F(\\lambda).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_11_globalYoungMatrixCoefficient_linearIndependent",
          "file": "DictatorshipTesting/Paper/S05_Lem5_11_RegularYoungBlockDecomposition.lean",
          "line": 14
        },
        {
          "name": "S05_Lem5_11_globalYoungMatrixCoefficient_span_all",
          "file": "DictatorshipTesting/Paper/S05_Lem5_11_RegularYoungBlockDecomposition.lean",
          "line": 22
        },
        {
          "name": "S05_Lem5_11_parseval",
          "file": "DictatorshipTesting/Paper/S05_Lem5_11_RegularYoungBlockDecomposition.lean",
          "line": 40
        }
      ]
    },
    {
      "id": "S05_D12",
      "label": "Def 5.12",
      "title": "Matching idempotents and averaged rejection",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_12a_MatchingIdempotents.lean",
      "wrappers": [],
      "deps": [
        "S05_D11",
        "S04_D02"
      ],
      "summary": "Def 5.12: Matching idempotents and averaged rejection.",
      "statement": "Def 5.12: Matching idempotents and averaged rejection.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D11"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D12"
        },
        {
          "text": "Group-algebra action",
          "target": "S05_D12"
        },
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L08"
        },
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "Averaged high-matching element",
          "target": "S05_D12"
        }
      ],
      "paperLabel": "def:matching-idempotents",
      "paperEnv": "definition",
      "paperStatementLatex": "For an ordered matching $M$ with $m$ edges, define\n\\[\n  e_R^M:=2^{-m}\\sum_{x\\in\\{0,1\\}^m}\\chi_R(\\tau_x)\\tau_x,\n  \\qquad\n  p_M:=\\sum_{|R|\\le1}e_R^M,\n  \\qquad\n  q_M:=1-p_M.\n\\]\nFor $a\\in\\mathbb C[S_n]$, let $C_a$ denote right convolution by $a$.  With $M$\nuniform over perfect or near-perfect matchings according to the parity of $n$,\nset\n\\begin{equation}\\label{eq:averaged-high-element-and-operator}\n  q:=\\E_M q_M,\n  \\qquad\n  \\cA:=\\E_M(I-P_M).\n\\end{equation}",
      "leanLinks": []
    },
    {
      "id": "S05_L12",
      "label": "Lem 5.12",
      "title": "Degree-one Young-block identification",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_12_DegreeOneYoungBlockIdentification.lean",
      "wrappers": [
        "S05_Lem5_12_degreeOneYoungBlockIdentification"
      ],
      "deps": [
        "S05_T03",
        "S05_L11"
      ],
      "summary": "Lem 5.12: Degree-one Young-block identification.",
      "statement": "Lem 5.12: Degree-one Young-block identification.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "lem:degree-one-young-blocks",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $n\\ge2$, after complexification,\n\\begin{equation}\\label{eq:U1-young-blocks}\n  U_1\\otimes_{\\mathbb R}\\mathbb C\n  =\\mathcal H_{(n)}\\oplus\\mathcal H_{(n-1,1)}.\n\\end{equation}\nEquivalently, for real-valued $F$,\n\\begin{equation}\\label{eq:U1-complement-young-blocks}\n  \\|F-P_{U_1}F\\|_2^2\n  =\\sum_{\\lambda\\notin\\{(n),(n-1,1)\\}}E_F(\\lambda).\n\\end{equation}\nFor $n=1$, only the one-row block occurs.",
      "leanLinks": [
        {
          "name": "S05_Lem5_12_degreeOneYoungBlockIdentification",
          "file": "DictatorshipTesting/Paper/S05_Lem5_12_DegreeOneYoungBlockIdentification.lean",
          "line": 34
        }
      ]
    },
    {
      "id": "S05_D13",
      "label": "Def 5.13",
      "title": "Certificate vocabulary",
      "section": "Section 5 definitions",
      "kind": "definition",
      "importance": "minor",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_13a_CertificateSpecialDiagrams.lean",
      "wrappers": [],
      "deps": [
        "S05_D01",
        "S05_D10"
      ],
      "summary": "Def 5.13: Certificate vocabulary.",
      "statement": "Def 5.13: Certificate vocabulary.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "Two-box removals",
          "target": "S05_D07"
        },
        {
          "text": "One-box removals",
          "target": "S05_D07"
        }
      ],
      "paperLabel": "def:certificate-vocabulary",
      "paperEnv": "definition",
      "paperStatementLatex": "\\begin{enumerate}[label=(\\alph*)]\n\\item\\label{def:certificate-special-diagrams}\nWe use the canonical shapes\n\\[\n\\begin{gathered}\n  (2m),\\ (2m-1,1),\\ (2m-2,2),\\ (2m-2,1,1),\n  (2m-3,3),\\ (2m-3,2,1),\\\\\n  (1,1,1,1),\\ (2m-1,2),\\ (2m-1,1,1).\n\\end{gathered}\n\\]\n\n\\item\\label{def:certificate-exceptional-predicates}\nFor $\\lambda\\vdash2m$, say that $\\lambda$ has a one-row horizontal child, a\none-row vertical child, or a standard horizontal child according as\n$(2m-2)$ lies in $\\mathsf H_2(\\lambda)$, in $\\mathsf V_2(\\lambda)$, or\n$(2m-3,1)$ lies in $\\mathsf H_2(\\lambda)$.  Set\n\\[\n  \\mathsf E_m^{\\mathrm{even}}(\\lambda)\n  \\Longleftrightarrow\n  \\lambda\\in\\{(2m-2,2),(2m-2,1,1),(2m-3,3),(2m-3,2,1)\\}.\n\\]\nFor $\\lambda\\vdash2m+1$, define the analogous one-row and standard one-box\nchild conditions, and set\n\\[\n  \\mathsf E_m^{\\mathrm{odd}}(\\lambda)\n  \\Longleftrightarrow\n  \\lambda\\in\\{(2m-1,2),(2m-1,1,1)\\}.\n\\]\n\\end{enumerate}",
      "leanLinks": []
    },
    {
      "id": "S05_L13",
      "label": "Lem 5.13",
      "title": "Signed two-box orthogonal branching",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_13_SignedTwoBoxOrthogonalBranching.lean",
      "wrappers": [
        "S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux"
      ],
      "deps": [
        "S05_D07",
        "S05_D03"
      ],
      "summary": "Lem 5.13: Signed two-box orthogonal branching.",
      "statement": "Lem 5.13: Signed two-box orthogonal branching.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D07"
        },
        {
          "text": "Standard-tableau deletion API",
          "target": "S05_D03"
        }
      ],
      "paperLabel": "lem:two-box-tableau-branching",
      "paperEnv": "lemma",
      "paperStatementLatex": "The maps $D_{\\mu,\\sigma}:W_{\\mu,\\sigma}\\to V^\\mu$ are unitary, the signed\nchild spaces are mutually orthogonal, and\n\\begin{equation}\\label{eq:two-box-orthogonal-sum}\n  V^\\lambda\n  =\\bigoplus_{(\\mu,\\sigma)\\in\\mathsf B_2(\\lambda)}W_{\\mu,\\sigma}.\n\\end{equation}\nFor $w\\in W_{\\mu,\\sigma}$,\n\\begin{equation}\\label{eq:two-box-last-transposition}\n  S_{N-1}^\\lambda w=\\varepsilon_\\sigma w,\n\\end{equation}\nand for $1\\le i\\le N-3$,\n\\begin{equation}\\label{eq:two-box-intertwining}\n  D_{\\mu,\\sigma}(S_i^\\lambda w)=S_i^\\mu D_{\\mu,\\sigma}(w).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux",
          "file": "DictatorshipTesting/Paper/S05_Lem5_13_SignedTwoBoxOrthogonalBranching.lean",
          "line": 434
        }
      ]
    },
    {
      "id": "S05_L14",
      "label": "Lem 5.14",
      "title": "One-box corner decomposition",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_14_OneBoxCornerDecomposition.lean",
      "wrappers": [
        "S05_Lem5_14_row_form",
        "S05_Lem5_14_removable_corner"
      ],
      "deps": [
        "S05_D07"
      ],
      "summary": "Lem 5.14: One-box corner decomposition.",
      "statement": "Lem 5.14: One-box corner decomposition.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D07"
        },
        {
          "text": "one-box children",
          "target": "S05_D02"
        }
      ],
      "paperLabel": "lem:one-box-corner-decomposition",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $\\lambda\\vdash N$,\n\\begin{equation}\\label{eq:one-box-corner-decomposition}\n  V^\\lambda=\\bigoplus_{u\\in\\Rem(\\lambda)} W_u .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_14_row_form",
          "file": "DictatorshipTesting/Paper/S05_Lem5_14_OneBoxCornerDecomposition.lean",
          "line": 77
        },
        {
          "name": "S05_Lem5_14_removable_corner",
          "file": "DictatorshipTesting/Paper/S05_Lem5_14_OneBoxCornerDecomposition.lean",
          "line": 105
        }
      ]
    },
    {
      "id": "S05_L15",
      "label": "Lem 5.15",
      "title": "One-box deletion is unitary",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_15_OneBoxDeletionIsUnitary.lean",
      "wrappers": [
        "S05_Lem5_15_deletionCoordinateMap_inner"
      ],
      "deps": [
        "S05_D09",
        "S05_L14"
      ],
      "summary": "Lem 5.15: One-box deletion is unitary.",
      "statement": "Lem 5.15: One-box deletion is unitary.",
      "terms": [
        {
          "text": "One-box deletion spaces",
          "target": "S05_D09"
        },
        {
          "text": "One-box corner decomposition",
          "target": "S05_L14"
        },
        {
          "text": "coordinate space",
          "target": "S05_D04"
        }
      ],
      "paperLabel": "lem:one-box-deletion-unitary",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $\\lambda\\vdash N$ and $u\\in\\Rem(\\lambda)$.  The map\n\\begin{equation*}\n  D_u:W_u\\rightarrow V^{\\mu_u}\n\\end{equation*}\nis unitary.",
      "leanLinks": [
        {
          "name": "S05_Lem5_15_deletionCoordinateMap_inner",
          "file": "DictatorshipTesting/Paper/S05_Lem5_15_OneBoxDeletionIsUnitary.lean",
          "line": 354
        }
      ]
    },
    {
      "id": "S05_L16",
      "label": "Lem 5.16",
      "title": "One-box deletion intertwines earlier swaps",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps.lean",
      "wrappers": [
        "S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines"
      ],
      "deps": [
        "S05_L15",
        "S05_L01"
      ],
      "summary": "Lem 5.16: One-box deletion intertwines earlier swaps.",
      "statement": "Lem 5.16: One-box deletion intertwines earlier swaps.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L15"
        },
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L15"
        }
      ],
      "paperLabel": "lem:one-box-deletion-intertwines",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $\\lambda\\vdash N$, let $u\\in\\Rem(\\lambda)$, and let $1\\le i\\le N-2$.\nFor every $w\\in W_u$,\n\\begin{equation}\\label{eq:one-box-intertwining}\n  D_u\\bigl(S_i^\\lambda w\\bigr)=S_i^{\\mu_u}D_u(w).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines",
          "file": "DictatorshipTesting/Paper/S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps.lean",
          "line": 677
        }
      ]
    },
    {
      "id": "S05_L17",
      "label": "Lem 5.17",
      "title": "Two-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_17_TwoBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_17_tableauDim_twoStrip_branching_sized"
      ],
      "deps": [
        "S05_L13"
      ],
      "summary": "Lem 5.17: Two-box dimension recursion.",
      "statement": "Lem 5.17: Two-box dimension recursion.",
      "terms": [
        {
          "text": "Two-box tableau branching",
          "target": "S05_L13"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "two-box removals",
          "target": "S05_D07"
        }
      ],
      "paperLabel": "lem:dimension-two-strip-recurrence",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every partition $\\lambda\\vdash 2m$ with $m\\ge2$,\n\\begin{equation}\\label{eq:dimension-two-strip-recurrence}\n  d_\\lambda\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}d_\\mu\n   +\\sum_{\\mu\\in\\mathsf V_2(\\lambda)}d_\\mu .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_17_tableauDim_twoStrip_branching_sized",
          "file": "DictatorshipTesting/Paper/S05_Lem5_17_TwoBoxDimensionRecursion.lean",
          "line": 107
        }
      ]
    },
    {
      "id": "S05_L18",
      "label": "Lem 5.18",
      "title": "One-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_18_OneBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_18_tableauDim_oneBoxChildrenOdd_branching"
      ],
      "deps": [
        "S05_L15",
        "S05_L16"
      ],
      "summary": "Lem 5.18: One-box dimension recursion.",
      "statement": "Lem 5.18: One-box dimension recursion.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L15"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "one-box removals",
          "target": "S05_D07"
        },
        {
          "text": "One-box deletion intertwining",
          "target": "S05_L16"
        }
      ],
      "paperLabel": "lem:dimension-one-box-recurrence",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every partition $\\lambda\\vdash N$ with $N\\ge2$,\n\\begin{equation}\\label{eq:dimension-one-box-recurrence}\n  d_\\lambda=\\sum_{\\mu\\nearrow\\lambda}d_\\mu .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_18_tableauDim_oneBoxChildrenOdd_branching",
          "file": "DictatorshipTesting/Paper/S05_Lem5_18_OneBoxDimensionRecursion.lean",
          "line": 406
        }
      ]
    },
    {
      "id": "S05_L19",
      "label": "Lem 5.19",
      "title": "Sizes of the sign-pattern multisets",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
      "wrappers": [
        "S05_Lem5_19_evenSignPatternMultiset_card",
        "S05_Lem5_19_oddSignPatternMultiset_card",
        "S05_Lem5_19_evenSignPatternMultiset_zeroMultiplicity",
        "S05_Lem5_19_evenSignPatternMultiset_highMultiplicity",
        "S05_Lem5_19_oddSignPatternMultiset_highMultiplicity"
      ],
      "deps": [
        "S05_D10",
        "S05_L17",
        "S05_L18"
      ],
      "summary": "Lem 5.19: Sizes of the sign-pattern multisets.",
      "statement": "Lem 5.19: Sizes of the sign-pattern multisets.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D10"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D10"
        },
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L17"
        },
        {
          "text": "One-box dimension recursion",
          "target": "S05_L18"
        }
      ],
      "paperLabel": "lem:X-size",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $\\lambda\\vdash2m$,\n\\begin{equation*}\n  |\\mathsf X_m(\\lambda)|=d_\\lambda .\n\\end{equation*}\nFor $\\lambda\\vdash2m+1$,\n\\begin{equation*}\n  |\\mathsf X_m^{\\mathrm{odd}}(\\lambda)|=d_\\lambda .\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_19_evenSignPatternMultiset_card",
          "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
          "line": 59
        },
        {
          "name": "S05_Lem5_19_oddSignPatternMultiset_card",
          "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
          "line": 90
        },
        {
          "name": "S05_Lem5_19_evenSignPatternMultiset_zeroMultiplicity",
          "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
          "line": 206
        },
        {
          "name": "S05_Lem5_19_evenSignPatternMultiset_highMultiplicity",
          "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
          "line": 236
        },
        {
          "name": "S05_Lem5_19_oddSignPatternMultiset_highMultiplicity",
          "file": "DictatorshipTesting/Paper/S05_Lem5_19_SizesOfTheSignPatternMultisets.lean",
          "line": 281
        }
      ]
    },
    {
      "id": "S05_L20",
      "label": "Lem 5.20",
      "title": "Matching subgroup eigenbasis",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
      "wrappers": [
        "S05_signedTwoBoxChild_orthogonal_decomposition",
        "S05_signedTwoBoxChildEmbedding_isometry",
        "S05_signedTwoBoxChildEmbedding_finalOperator",
        "S05_signedTwoBoxChildEmbedding_intertwinesEarlierAdjacent",
        "S05_signedTwoBoxChildEmbedding_ranges_orthogonal",
        "S05_signedTwoBoxChildEmbeddings_span",
        "S05_Lem5_20_canonicalEvenMatchingEigenbasis",
        "S05_canonicalEvenEigenbasisLabelMultiset_eq",
        "S05_canonicalEvenEigenbasisVector_inner",
        "S05_canonicalEvenEigenbasisVector_span",
        "S05_canonicalEvenEigenbasisVector_isMatchingEigenvector",
        "S05_canonicalEvenMatchingBasis_character_action",
        "S05_Lem5_20_arbitraryEvenMatchingEigenbasis_toOrdered",
        "S05_arbitraryEvenMatchingBasis_toOrdered_character_action",
        "S05_arbitraryEvenMatchingLabelMultiset_eq",
        "S05_Lem5_20_canonicalOddMatchingEigenbasis",
        "S05_nearPerfectMatchingUnmatchedPoint",
        "S05_nearPerfectMatchingRelabeling",
        "S05_Lem5_20_arbitraryOddMatchingEigenbasis_toOrdered",
        "S05_arbitraryOddMatchingBasis_toOrdered_character_action",
        "S05_arbitraryOddMatchingLabelMultiset_eq",
        "S05_perfectMatchingRelabeling",
        "YoungOrthogonalActionData.rho_inner",
        "S05_Lem5_20_matchingSignProjectionEven_isMatchingEigenvector",
        "S05_Lem5_20_matchingSignProjectionOdd_isMatchingEigenvector",
        "S05_Lem5_20_highLabelCount_of_evenSignPatternMultiset",
        "S05_Lem5_20_highLabelCount_of_oddSignPatternMultiset"
      ],
      "deps": [
        "S05_L01",
        "S05_L13",
        "S05_L15",
        "S05_L16",
        "S05_L17",
        "S05_L19",
        "S05_D10",
        "S05_D11"
      ],
      "summary": "Lem 5.20: Matching subgroup eigenbasis.",
      "statement": "Lem 5.20: Matching subgroup eigenbasis.",
      "terms": [
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "Two-box tableau branching",
          "target": "S05_L13"
        },
        {
          "text": "Sign-pattern multiset sizes",
          "target": "S05_L19"
        },
        {
          "text": "Matching characters",
          "target": "S05_D11"
        },
        {
          "text": "Even matching eigenvectors",
          "target": "S05_D11"
        },
        {
          "text": "Odd matching eigenvectors",
          "target": "S05_D11"
        },
        {
          "text": "Matching operators",
          "target": "S05_L01"
        }
      ],
      "paperLabel": "lem:matching-restriction-X",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $M$ be a perfect matching on $[2m]$ and $\\lambda\\vdash2m$.  There is an\northonormal basis $v_1,\\ldots,v_{d_\\lambda}$ of $V^\\lambda$ and a listing\n$R_1,\\ldots,R_{d_\\lambda}$ of the multiset $\\mathsf X_m(\\lambda)$ such that\n$v_a$ is an $M$-matching eigenvector with label $R_a$.\n\nIf $M$ is a near-perfect matching on $[2m+1]$ and\n$\\lambda\\vdash2m+1$, the analogous assertion holds with label multiset\n$\\mathsf X_m^{\\mathrm{odd}}(\\lambda)$.",
      "leanLinks": [
        {
          "name": "S05_signedTwoBoxChild_orthogonal_decomposition",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2413
        },
        {
          "name": "S05_signedTwoBoxChildEmbedding_isometry",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2048
        },
        {
          "name": "S05_signedTwoBoxChildEmbedding_finalOperator",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2117
        },
        {
          "name": "S05_signedTwoBoxChildEmbedding_intertwinesEarlierAdjacent",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2152
        },
        {
          "name": "S05_signedTwoBoxChildEmbedding_ranges_orthogonal",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2273
        },
        {
          "name": "S05_signedTwoBoxChildEmbeddings_span",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2397
        },
        {
          "name": "S05_Lem5_20_canonicalEvenMatchingEigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 3035
        },
        {
          "name": "S05_canonicalEvenEigenbasisLabelMultiset_eq",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2687
        },
        {
          "name": "S05_canonicalEvenEigenbasisVector_inner",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2730
        },
        {
          "name": "S05_canonicalEvenEigenbasisVector_span",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2807
        },
        {
          "name": "S05_canonicalEvenEigenbasisVector_isMatchingEigenvector",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 2936
        },
        {
          "name": "S05_canonicalEvenMatchingBasis_character_action",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 3062
        },
        {
          "name": "S05_Lem5_20_arbitraryEvenMatchingEigenbasis_toOrdered",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4532
        },
        {
          "name": "S05_arbitraryEvenMatchingBasis_toOrdered_character_action",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4498
        },
        {
          "name": "S05_arbitraryEvenMatchingLabelMultiset_eq",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4450
        },
        {
          "name": "S05_Lem5_20_canonicalOddMatchingEigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 3746
        },
        {
          "name": "S05_nearPerfectMatchingUnmatchedPoint",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4679
        },
        {
          "name": "S05_nearPerfectMatchingRelabeling",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4842
        },
        {
          "name": "S05_Lem5_20_arbitraryOddMatchingEigenbasis_toOrdered",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5219
        },
        {
          "name": "S05_arbitraryOddMatchingBasis_toOrdered_character_action",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5186
        },
        {
          "name": "S05_arbitraryOddMatchingLabelMultiset_eq",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5139
        },
        {
          "name": "S05_perfectMatchingRelabeling",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 4076
        },
        {
          "name": "YoungOrthogonalActionData.rho_inner",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 3858
        },
        {
          "name": "S05_Lem5_20_matchingSignProjectionEven_isMatchingEigenvector",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5568
        },
        {
          "name": "S05_Lem5_20_matchingSignProjectionOdd_isMatchingEigenvector",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5576
        },
        {
          "name": "S05_Lem5_20_highLabelCount_of_evenSignPatternMultiset",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5716
        },
        {
          "name": "S05_Lem5_20_highLabelCount_of_oddSignPatternMultiset",
          "file": "DictatorshipTesting/Paper/S05_Lem5_20_MatchingSubgroupEigenbasis.lean",
          "line": 5728
        }
      ]
    },
    {
      "id": "S05_L21",
      "label": "Lem 5.21",
      "title": "Local truncation on a matching character",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_21_LocalTruncationOnAMatchingCharacter.lean",
      "wrappers": [
        "S05_Lem5_21_matchingLocalProjection_preserves_low_matchingCharacter",
        "S05_Lem5_21_matchingLocalProjection_kills_high_matchingCharacter"
      ],
      "deps": [
        "S05_D11",
        "S04_D02"
      ],
      "summary": "Lem 5.21: Local truncation on a matching character.",
      "statement": "Lem 5.21: Local truncation on a matching character.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D11"
        }
      ],
      "paperLabel": "lem:PM-character-projection",
      "paperEnv": "lemma",
      "paperStatementLatex": "Fix a matching $M$ with $m$ edges.  On a right coset $C=\\rho_C A_M$, write\n\\begin{equation}\\label{eq:local-character-expansion-general}\n  F(\\rho_C\\tau_x)=\\sum_{R\\subseteq[m]} a_R(C)\\chi_R(\\tau_x).\n\\end{equation}\nThen\n\\begin{equation}\\label{eq:PM-keeps-small-characters}\n  (P_MF)(\\rho_C\\tau_x)=\\sum_{|R|\\le1}a_R(C)\\chi_R(\\tau_x).\n\\end{equation}\nIn particular, if $F(\\omega\\tau_x)=\\chi_T(\\tau_x)F(\\omega)$ for all $\\omega$ and\n$x$, then\n\\begin{equation*}\n  P_MF=\n  \\begin{cases}\n    F,& |T|\\le1,\\\\\n    0,& |T|\\ge2.\n  \\end{cases}\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_21_matchingLocalProjection_preserves_low_matchingCharacter",
          "file": "DictatorshipTesting/Paper/S05_Lem5_21_LocalTruncationOnAMatchingCharacter.lean",
          "line": 121
        },
        {
          "name": "S05_Lem5_21_matchingLocalProjection_kills_high_matchingCharacter",
          "file": "DictatorshipTesting/Paper/S05_Lem5_21_LocalTruncationOnAMatchingCharacter.lean",
          "line": 133
        }
      ]
    },
    {
      "id": "S05_L22",
      "label": "Lem 5.22",
      "title": "Trace of one local truncation on one Young block",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
      "wrappers": [
        "S05_Lem5_22_fixedMatching_tableauTrace_even_of_eigenbasis",
        "S05_Lem5_22_fixedMatching_tableauTrace_odd_of_eigenbasis",
        "S05_Lem5_22_fixedMatching_youngBlockTrace_even_of_eigenbasis",
        "S05_Lem5_22_fixedMatching_youngBlockTrace_odd_of_eigenbasis",
        "S05_Lem5_22_fixedMatching_tableauTrace_even",
        "S05_Lem5_22_fixedMatching_youngBlockTrace_even",
        "S05_Lem5_22_fixedMatching_tableauTrace_odd",
        "S05_Lem5_22_fixedMatching_youngBlockTrace_odd",
        "traceLocalTruncation_even_from_restriction",
        "traceLocalTruncation_odd_from_restriction"
      ],
      "deps": [
        "S05_L20",
        "S05_L21",
        "S04_D02"
      ],
      "summary": "Lem 5.22: Trace of one local truncation on one Young block.",
      "statement": "Lem 5.22: Trace of one local truncation on one Young block.",
      "terms": [
        {
          "text": "Matching subgroup eigenbasis",
          "target": "S05_L20"
        },
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L21"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "lem:PM-trace-young-block",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $M$ is a perfect matching on $[2m]$ and $\\lambda\\vdash2m$, then\n\\begin{equation}\\label{eq:trace-one-PM-even}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m(\\lambda).\n\\end{equation}\nIf $M$ is a near-perfect matching on $[2m+1]$ and\n$\\lambda\\vdash2m+1$, then\n\\begin{equation}\\label{eq:trace-one-PM-odd}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m^{\\mathrm{odd}}(\\lambda).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_22_fixedMatching_tableauTrace_even_of_eigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 72
        },
        {
          "name": "S05_Lem5_22_fixedMatching_tableauTrace_odd_of_eigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 97
        },
        {
          "name": "S05_Lem5_22_fixedMatching_youngBlockTrace_even_of_eigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 121
        },
        {
          "name": "S05_Lem5_22_fixedMatching_youngBlockTrace_odd_of_eigenbasis",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 145
        },
        {
          "name": "S05_Lem5_22_fixedMatching_tableauTrace_even",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 169
        },
        {
          "name": "S05_Lem5_22_fixedMatching_youngBlockTrace_even",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 186
        },
        {
          "name": "S05_Lem5_22_fixedMatching_tableauTrace_odd",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 198
        },
        {
          "name": "S05_Lem5_22_fixedMatching_youngBlockTrace_odd",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 215
        },
        {
          "name": "traceLocalTruncation_even_from_restriction",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 227
        },
        {
          "name": "traceLocalTruncation_odd_from_restriction",
          "file": "DictatorshipTesting/Paper/S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
          "line": 235
        }
      ]
    },
    {
      "id": "S05_L23",
      "label": "Lem 5.23",
      "title": "Local truncation as convolution",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_23_LocalTruncationAsConvolution.lean",
      "wrappers": [
        "S05_Lem5_23_local_truncation_as_convolution"
      ],
      "deps": [
        "S05_L21",
        "S05_D12",
        "S04_D02"
      ],
      "summary": "Lem 5.23: Local truncation as convolution.",
      "statement": "Lem 5.23: Local truncation as convolution.",
      "terms": [
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L21"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D12"
        }
      ],
      "paperLabel": "lem:PM-convolution",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every matching $M$,\n\\begin{equation*}\n  P_M=C_{p_M},\n  \\qquad\n  I-P_M=C_{q_M}.\n\\end{equation*}\nMoreover $p_M$ and $q_M$ are complementary idempotents:\n\\begin{equation*}\n  p_M^2=p_M,\n  \\qquad q_M^2=q_M,\n  \\qquad p_Mq_M=q_Mp_M=0,\n  \\qquad p_M+q_M=1.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_23_local_truncation_as_convolution",
          "file": "DictatorshipTesting/Paper/S05_Lem5_23_LocalTruncationAsConvolution.lean",
          "line": 25
        }
      ]
    },
    {
      "id": "S05_L24",
      "label": "Lem 5.24",
      "title": "Central averaged rejection",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_24_CentralAveragedRejection.lean",
      "wrappers": [
        "S05_Lem5_24_matchingMeanProjectionError_eq_high_idempotent_average"
      ],
      "deps": [
        "S05_L23",
        "S05_D12"
      ],
      "summary": "Lem 5.24: Central averaged rejection.",
      "statement": "Lem 5.24: Central averaged rejection.",
      "terms": [
        {
          "text": "Local truncation as convolution",
          "target": "S05_L23"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D12"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        },
        {
          "text": "spectral model",
          "target": "S05_L11"
        }
      ],
      "paperLabel": "lem:averaged-rejection-central",
      "paperEnv": "lemma",
      "paperStatementLatex": "The element $q$ in \\eqref{eq:averaged-high-element-and-operator} is central in\n$\\mathbb C[S_n]$, and\n\\begin{equation}\\label{eq:averaged-rejection-convolution}\n  \\cA=C_q.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_24_matchingMeanProjectionError_eq_high_idempotent_average",
          "file": "DictatorshipTesting/Paper/S05_Lem5_24_CentralAveragedRejection.lean",
          "line": 60
        }
      ]
    },
    {
      "id": "S05_L25",
      "label": "Lem 5.25",
      "title": "Block scalar of the averaged rejection",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean",
      "wrappers": [
        "S05_Lem5_25_scalar_eq_trace_div_dimension",
        "S05_Lem5_25_even_scalar_eq_hEven_div_dim",
        "S05_Lem5_25_odd_scalar_eq_hOdd_div_dim"
      ],
      "deps": [
        "S05_L22",
        "S05_L08"
      ],
      "summary": "Lem 5.25: Block scalar of the averaged rejection.",
      "statement": "Lem 5.25: Block scalar of the averaged rejection.",
      "terms": [
        {
          "text": "Trace of one local truncation",
          "target": "S05_L22"
        },
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L08"
        }
      ],
      "paperLabel": "lem:centralization-matchings",
      "paperEnv": "lemma",
      "paperStatementLatex": "On $\\mathcal H_\\lambda$, the operator $\\cA$ acts by\n\\begin{equation}\\label{eq:A-eigenvalue-even}\n  \\frac{h_m(\\lambda)}{d_\\lambda}\n  \\qquad(n=2m),\n\\end{equation}\nand by\n\\begin{equation}\\label{eq:A-eigenvalue-odd}\n  \\frac{h_m^{\\mathrm{odd}}(\\lambda)}{d_\\lambda}\n  \\qquad(n=2m+1).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_25_scalar_eq_trace_div_dimension",
          "file": "DictatorshipTesting/Paper/S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean",
          "line": 109
        },
        {
          "name": "S05_Lem5_25_even_scalar_eq_hEven_div_dim",
          "file": "DictatorshipTesting/Paper/S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean",
          "line": 116
        },
        {
          "name": "S05_Lem5_25_odd_scalar_eq_hOdd_div_dim",
          "file": "DictatorshipTesting/Paper/S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean",
          "line": 126
        }
      ]
    },
    {
      "id": "S05_L26",
      "section": "Section 5",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "terms": [],
      "paperStatementLatex": "Let $F_\\lambda$ and $E_F(\\lambda)$ be the concrete components and energies from\n\\Cref{def:young-block}.  If $n=2m$, then\n\\begin{equation}\\label{eq:global-weighted-matching-even}\n  \\E_M\\|(I-P_M)F\\|_2^2\n  =\\sum_{\\lambda\\notin\\{(2m),(2m-1,1)\\}}\n     \\frac{h_m(\\lambda)}{d_\\lambda}E_F(\\lambda).\n\\end{equation}\nIf $n=2m+1$, then\n\\begin{equation}\\label{eq:global-weighted-matching-odd}\n  \\E_M\\|(I-P_M)F\\|_2^2\n  =\\sum_{\\lambda\\notin\\{(2m+1),(2m,1)\\}}\n     \\frac{h_m^{\\mathrm{odd}}(\\lambda)}{d_\\lambda}E_F(\\lambda).\n\\end{equation}",
      "label": "Lem 5.26",
      "title": "Global weighted matching identity",
      "file": "DictatorshipTesting/Paper/S05_Lem5_26_GlobalWeightedMatchingIdentity.lean",
      "wrappers": [
        "S05_Lem5_26_global_weighted_matching_identity_even",
        "S05_Lem5_26_global_weighted_matching_identity_odd"
      ],
      "deps": [
        "S05_L11",
        "S05_L12",
        "S05_L25",
        "S04_D02"
      ],
      "summary": "Lem 5.26: Global weighted matching identity.",
      "statement": "Lem 5.26: Global weighted matching identity.",
      "leanLinks": [
        {
          "name": "S05_Lem5_26_global_weighted_matching_identity_even",
          "file": "DictatorshipTesting/Paper/S05_Lem5_26_GlobalWeightedMatchingIdentity.lean",
          "line": 14
        },
        {
          "name": "S05_Lem5_26_global_weighted_matching_identity_odd",
          "file": "DictatorshipTesting/Paper/S05_Lem5_26_GlobalWeightedMatchingIdentity.lean",
          "line": 28
        }
      ],
      "paperLabel": "lem:global-weighted-matching-identity",
      "paperEnv": "lemma"
    },
    {
      "id": "S05_L27",
      "label": "Lem 5.27",
      "title": "Block lower bound implies the gap",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_27_BlockLowerBoundImpliesTheGap.lean",
      "wrappers": [
        "S05_Lem5_27_spectralGapFromBlockModelWithDim"
      ],
      "deps": [
        "S05_D06",
        "S05_L25"
      ],
      "summary": "Lem 5.27: Block lower bound implies the gap.",
      "statement": "Lem 5.27: Block lower bound implies the gap.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D06"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D06"
        },
        {
          "text": "Block scalar of averaged rejection",
          "target": "S05_L25"
        }
      ],
      "paperLabel": "lem:block-lower-bound-gap",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $\\cA$ acts on every block outside $U_1$ by a scalar at least $c$, then\n\\[\n  \\langle F,\\cA F\\rangle\\ge c\\|F-P_{U_1}F\\|_2^2.\n\\]",
      "leanLinks": [
        {
          "name": "S05_Lem5_27_spectralGapFromBlockModelWithDim",
          "file": "DictatorshipTesting/Paper/S05_Lem5_27_BlockLowerBoundImpliesTheGap.lean",
          "line": 148
        }
      ]
    },
    {
      "id": "S05_L28",
      "label": "Lem 5.28",
      "title": "Even spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_28_EvenSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_28_tableauDim_evenSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L27",
        "S05_L11",
        "S05_L33"
      ],
      "summary": "Lem 5.28: Even spectral bridge.",
      "statement": "Lem 5.28: Even spectral bridge.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L27"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L11"
        },
        {
          "text": "Even certificate",
          "target": "S05_L33"
        },
        {
          "text": "spectral model",
          "target": "S05_L11"
        }
      ],
      "paperLabel": "lem:spectral-certificate-even",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $n=2m$.  Suppose that\n\\begin{equation}\\label{eq:even-certificate-condition}\n  h_m(\\lambda)\\ge c d_\\lambda\n\\end{equation}\nfor every $\\lambda\\vdash2m$ other than $(2m)$ and $(2m-1,1)$.  Then\n\\eqref{eq:desired-A-gap} holds with constant $c$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_28_tableauDim_evenSpectralGapFromCertificates",
          "file": "DictatorshipTesting/Paper/S05_Lem5_28_EvenSpectralBridge.lean",
          "line": 53
        }
      ]
    },
    {
      "id": "S05_L29",
      "label": "Lem 5.29",
      "title": "Odd spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_29_OddSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_29_tableauDim_oddSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L27",
        "S05_L11",
        "S05_L35"
      ],
      "summary": "Lem 5.29: Odd spectral bridge.",
      "statement": "Lem 5.29: Odd spectral bridge.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L27"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L11"
        },
        {
          "text": "Odd certificate",
          "target": "S05_L35"
        },
        {
          "text": "spectral model",
          "target": "S05_L11"
        }
      ],
      "paperLabel": "lem:spectral-certificate-odd",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $n=2m+1$.  Suppose that\n\\begin{equation}\\label{eq:odd-certificate-condition}\n  h_m^{\\mathrm{odd}}(\\lambda)\\ge c d_\\lambda\n\\end{equation}\nfor every $\\lambda\\vdash2m+1$ other than $(2m+1)$ and $(2m,1)$.  Then\n\\eqref{eq:desired-A-gap} holds with constant $c$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_29_tableauDim_oddSpectralGapFromCertificates",
          "file": "DictatorshipTesting/Paper/S05_Lem5_29_OddSpectralBridge.lean",
          "line": 53
        }
      ]
    },
    {
      "id": "S05_L30",
      "label": "Lem 5.30",
      "title": "Counting one more matching edge",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_30_CountingOneMoreMatchingEdge.lean",
      "wrappers": [
        "S05_Lem5_30_CountingOneMoreMatchingEdge"
      ],
      "deps": [
        "S05_D10"
      ],
      "summary": "Lem 5.30: Counting one more matching edge.",
      "statement": "Lem 5.30: Counting one more matching edge.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D10"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D10"
        }
      ],
      "paperLabel": "lem:counting-one-more-matching-edge",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $\\lambda\\vdash2m$,\n\\begin{equation}\\label{eq:z-recurrence}\n  z_m(\\lambda)\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}z_{m-1}(\\mu),\n\\end{equation}\nand\n\\begin{equation}\\label{eq:h-recurrence}\n  h_m(\\lambda)\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}h_{m-1}(\\mu)\n   +\\sum_{\\mu\\in\\mathsf V_2(\\lambda)}\n      \\bigl(d_\\mu-z_{m-1}(\\mu)\\bigr).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_30_CountingOneMoreMatchingEdge",
          "file": "DictatorshipTesting/Paper/S05_Lem5_30_CountingOneMoreMatchingEdge.lean",
          "line": 25
        }
      ]
    },
    {
      "id": "S05_L31",
      "label": "Lem 5.31",
      "title": "Weight-zero entries are never a majority",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_31_WeightZeroEntriesAreNeverAMajority.lean",
      "wrappers": [
        "S05_Lem5_31_tableau_weightZeroEntries_never_majority"
      ],
      "deps": [
        "S05_L17",
        "S05_L30",
        "S05_D13"
      ],
      "summary": "Lem 5.31: Weight-zero entries are never a majority.",
      "statement": "Lem 5.31: Weight-zero entries are never a majority.",
      "terms": [
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L17"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L30"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D13"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D13"
        }
      ],
      "paperLabel": "lem:z-bound-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $\\lambda\\vdash2m$ and $\\lambda\\neq(2m)$, then\n\\begin{equation*}\n  z_m(\\lambda)\\le\\frac12d_\\lambda.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_31_tableau_weightZeroEntries_never_majority",
          "file": "DictatorshipTesting/Paper/S05_Lem5_31_WeightZeroEntriesAreNeverAMajority.lean",
          "line": 2539
        }
      ]
    },
    {
      "id": "S05_L32",
      "label": "Lem 5.32",
      "title": "Where the induction can fail",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_32_WhereTheInductionCanFail.lean",
      "wrappers": [
        "S05_Lem5_32_where_the_induction_can_fail"
      ],
      "deps": [
        "S05_L31",
        "S05_D13"
      ],
      "summary": "Lem 5.32: Where the induction can fail.",
      "statement": "Lem 5.32: Where the induction can fail.",
      "terms": [
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L31"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D13"
        }
      ],
      "paperLabel": "lem:exceptional-even-children",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $m\\ge3$, and let $\\lambda\\vdash 2m$ be neither $(2m)$ nor $(2m-1,1)$.\nSuppose that at least one of the following three events occurs:\n\\begin{enumerate}\n  \\item the one-row diagram $(2m-2)$ lies in $\\mathsf H_2(\\lambda)$;\n  \\item the one-row diagram $(2m-2)$ lies in $\\mathsf V_2(\\lambda)$;\n  \\item the standard diagram $(2m-3,1)$ lies in $\\mathsf H_2(\\lambda)$.\n\\end{enumerate}\nThen\n\\begin{equation}\\label{eq:exceptional-even-shapes}\n  \\lambda\\in\\{(2m-2,2),(2m-2,1,1),(2m-3,3),(2m-3,2,1)\\}.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_32_where_the_induction_can_fail",
          "file": "DictatorshipTesting/Paper/S05_Lem5_32_WhereTheInductionCanFail.lean",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_L33",
      "label": "Lem 5.33",
      "title": "Even certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_33_EvenCertificate.lean",
      "wrappers": [
        "S05_Lem5_33_tableau_even_certificate"
      ],
      "deps": [
        "S05_D10",
        "S05_D13",
        "S05_L17",
        "S05_L30",
        "S05_L31",
        "S05_L32",
        "S05_L19"
      ],
      "summary": "Lem 5.33: Even certificate.",
      "statement": "Lem 5.33: Even certificate.",
      "terms": [
        {
          "text": "Tableau even height",
          "target": "S05_D10"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D13"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D13"
        },
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L17"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L30"
        },
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L31"
        },
        {
          "text": "Where the induction can fail",
          "target": "S05_L32"
        },
        {
          "text": "Sign-pattern multiset sizes",
          "target": "S05_L19"
        }
      ],
      "paperLabel": "lem:h-even-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $m\\ge2$ and every partition $\\lambda\\vdash2m$ other than $(2m)$ and\n$(2m-1,1)$,\n\\begin{equation}\\label{eq:even-h-fifth}\n  h_m(\\lambda)\\ge\\frac15d_\\lambda.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_33_tableau_even_certificate",
          "file": "DictatorshipTesting/Paper/S05_Lem5_33_EvenCertificate.lean",
          "line": 4492
        }
      ]
    },
    {
      "id": "S05_L34",
      "label": "Lem 5.34",
      "title": "Odd exceptional children",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_34_OddExceptionalChildren.lean",
      "wrappers": [
        "S05_Lem5_34_odd_exceptional_children"
      ],
      "deps": [
        "S05_L33",
        "S05_D13"
      ],
      "summary": "Lem 5.34: Odd exceptional children.",
      "statement": "Lem 5.34: Odd exceptional children.",
      "terms": [
        {
          "text": "Even certificate",
          "target": "S05_L33"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D13"
        }
      ],
      "paperLabel": "lem:exceptional-odd-children",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $m\\ge2$, and let $\\lambda\\vdash 2m+1$ be neither $(2m+1)$ nor $(2m,1)$.\nIf some one-box child $\\mu\\nearrow\\lambda$ is either the one-row diagram $(2m)$\nor the standard diagram $(2m-1,1)$, then\n\\begin{equation}\\label{eq:exceptional-odd-shapes}\n  \\lambda\\in\\{(2m-1,2),(2m-1,1,1)\\}.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_34_odd_exceptional_children",
          "file": "DictatorshipTesting/Paper/S05_Lem5_34_OddExceptionalChildren.lean",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_L35",
      "label": "Lem 5.35",
      "title": "Odd certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_35_OddCertificate.lean",
      "wrappers": [
        "S05_Lem5_35_tableau_odd_certificate"
      ],
      "deps": [
        "S05_D10",
        "S05_D13",
        "S05_L18",
        "S05_L33",
        "S05_L34",
        "S05_L19"
      ],
      "summary": "Lem 5.35: Odd certificate.",
      "statement": "Lem 5.35: Odd certificate.",
      "terms": [
        {
          "text": "Tableau odd height",
          "target": "S05_D10"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D13"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D13"
        },
        {
          "text": "One-box dimension recursion",
          "target": "S05_L18"
        },
        {
          "text": "Even certificate",
          "target": "S05_L33"
        },
        {
          "text": "Odd exceptional children",
          "target": "S05_L34"
        },
        {
          "text": "Sign-pattern multiset sizes",
          "target": "S05_L19"
        }
      ],
      "paperLabel": "lem:h-odd-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $m\\ge2$ and every partition $\\lambda\\vdash2m+1$ other than\n$(2m+1)$ and $(2m,1)$,\n\\begin{equation*}\n  h_m^{\\mathrm{odd}}(\\lambda)\\ge\\frac16d_\\lambda.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_35_tableau_odd_certificate",
          "file": "DictatorshipTesting/Paper/S05_Lem5_35_OddCertificate.lean",
          "line": 813
        }
      ]
    }
  ]
};

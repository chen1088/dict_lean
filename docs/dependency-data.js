window.DICT_DEPENDENCY_DATA = {
  "repoUrl": "https://github.com/chen1088/dict_lean",
  "nodes": [
    {
      "id": "AppA_01",
      "label": "App A.1",
      "title": "Young orthogonal realization",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_ThmA_01_YoungOrthogonalRealization.lean",
      "wrappers": [
        "AppA_ThmA_01_YoungOrthogonalActionStatement",
        "AppA_ThmA_01_youngOrthogonalRealization"
      ],
      "deps": [],
      "summary": "Faithful Young action interface defined; the existing axiom still has its old numerical-shadow type.",
      "statement": "App A.1 now has a faithful operator statement type supplying YoungOrthogonalActionData: a linear multiplicative symmetric-group action whose adjacent generators are the explicit Young operators. The existing axiom declaration is still the older block-energy shadow because the regular-decomposition adapter is not proved.",
      "terms": [],
      "paperLabel": "thm:app-young-orthogonal",
      "paperEnv": "theorem",
      "paperStatementLatex": "Let $\\lambda\\vdash N$.  Let $V_\\lambda$ be the complex vector space with basis\n$\\{e_T:T\\in\\SYT(\\lambda)\\}$.  For each adjacent transposition $s_i=(i,i+1)$,\ndefine $S_i^\\lambda$ on this basis by Young's orthogonal local rule: if $i$ and\n$i+1$ are in the same row of $T$, then $S_i^\\lambda e_T=e_T$; if they are in the\nsame column, then $S_i^\\lambda e_T=-e_T$; otherwise $s_iT$ is standard and\n$S_i^\\lambda$ acts on $\\spanop\\{e_T,e_{s_iT}\\}$ by the usual $2\\times2$\nseminormal block determined by the axial distance.  Then the operators\n$S_i^\\lambda$ give the Young orthogonal, or seminormal, realization of the\nSpecht representation $S^\\lambda$ of $S_N$.",
      "leanLinks": [
        {
          "name": "AppA_ThmA_01_YoungOrthogonalActionStatement",
          "line": 31
        },
        {
          "name": "AppA_ThmA_01_youngOrthogonalRealization",
          "line": 52
        }
      ]
    },
    {
      "id": "AppA_02",
      "label": "App A.2",
      "title": "Jucys-Murphy content spectrum",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_ThmA_02_JucysMurphyContentSpectrum.lean",
      "wrappers": [
        "AppA_ThmA_02_JucysMurphyContentActionStatement",
        "AppA_ThmA_02_jucysMurphyContentSpectrum"
      ],
      "deps": [
        "AppA_01"
      ],
      "summary": "Faithful JM/content interface defined; the existing axiom still has its old trace/scalar-shadow type.",
      "statement": "App A.2 now has a faithful operator statement type supplying JucysMurphyContentActionData for the same A.1 action and the actual coefficient element J_k. The existing axiom declaration is still the older trace/scalar shadow because the concrete fixed-block trace theorem is not proved.",
      "terms": [],
      "paperLabel": "thm:app-jucys-murphy-content",
      "paperEnv": "theorem",
      "paperStatementLatex": "Let\n\\begin{equation*}\n  J_k=\\sum_{i<k}(i,k)\\in\\mathbb C[S_N].\n\\end{equation*}\nIn the Young orthogonal basis of $S^\\lambda$, the operator $\\rho^\\lambda(J_k)$\nis diagonal and satisfies\n\\begin{equation*}\n  \\rho^\\lambda(J_k)e_T=c_T(k)e_T,\n\\end{equation*}\nwhere $c_T(k)=\\col_T(k)-\\row_T(k)$ is the content of the box containing $k$ in\n$T$.",
      "leanLinks": [
        {
          "name": "AppA_ThmA_02_JucysMurphyContentActionStatement",
          "line": 33
        },
        {
          "name": "AppA_ThmA_02_jucysMurphyContentSpectrum",
          "line": 69
        }
      ]
    },
    {
      "id": "AppA_03",
      "label": "App A.3",
      "title": "Degree-one Young-block identification",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_LemA_03_DegreeOneYoungBlockIdentification.lean",
      "wrappers": [
        "AppA_LemA_03_degreeOneYoungBlockIdentification"
      ],
      "deps": [],
      "summary": "External marker identifying the degree-one Young blocks.",
      "statement": "App A.3: External marker identifying the degree-one Young blocks.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "lem:app-u1-young-blocks",
      "paperEnv": "lemma",
      "paperStatementLatex": "After complexifying, the degree-one space is\n\\begin{equation*}\n  U_1\\otimes_{\\mathbb R}\\mathbb C\n  =\\mathcal H_{(n)}\\oplus\\mathcal H_{(n-1,1)}.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "AppA_LemA_03_degreeOneYoungBlockIdentification",
          "line": 31
        }
      ]
    },
    {
      "id": "AppA_04",
      "label": "App A.4",
      "title": "Standard tableaux connectedness",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_LemA_04_StandardTableauxSwapConnectedness.lean",
      "wrappers": [
        "AppA_LemA_04_standardTableauxSwapConnectedness"
      ],
      "deps": [],
      "summary": "External marker for connectedness under adjacent swaps.",
      "statement": "App A.4: External marker for connectedness under adjacent swaps.",
      "terms": [
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        }
      ],
      "paperLabel": "lem:app-tableau-swap-connected",
      "paperEnv": "lemma",
      "paperStatementLatex": "For a fixed Young diagram $\\lambda$, the graph on $\\SYT(\\lambda)$ in which\n$T$ is adjacent to $s_iT$ whenever $s_iT$ is again standard is connected.",
      "leanLinks": [
        {
          "name": "AppA_LemA_04_standardTableauxSwapConnectedness",
          "line": 30
        }
      ]
    },
    {
      "id": "L2_3",
      "label": "Lem 2.3",
      "title": "Cube Fourier facts",
      "section": "Section 2",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S02_Lem2_03_CubeParseval.lean",
      "wrappers": [
        "L2_3_CubeParseval"
      ],
      "deps": [],
      "summary": "Cube-character orthonormality, Fourier expansion, and Parseval wrappers.",
      "statement": "Lem 2.3: Cube-character orthonormality, Fourier expansion, and Parseval wrappers.",
      "terms": [],
      "paperLabel": "lem:cube-parseval",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $S,T\\subseteq[m]$,\n\\begin{equation}\\label{eq:cube-character-orthonormality}\n  \\E_x\\chi_S(x)\\chi_T(x)\n  =\n  \\begin{cases}\n    1, & S=T,\\\\\n    0, & S\\ne T.\n  \\end{cases}\n\\end{equation}\nConsequently, every $g:\\{0,1\\}^m\\to\\mathbb R$ has the expansion\n\\begin{equation}\\label{eq:cube-fourier-expansion}\n  g(x)=\\sum_{S\\subseteq[m]}\\widehat g(S)\\chi_S(x),\n\\end{equation}\nand Parseval's identity holds:\n\\begin{equation}\\label{eq:cube-parseval-identity}\n  \\E_x[g(x)^2]=\\sum_{S\\subseteq[m]}\\widehat g(S)^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "L2_3_CubeParseval",
          "line": 25
        }
      ]
    },
    {
      "id": "S03_01",
      "label": "Lem 3.1",
      "title": "Completeness on matching cubes",
      "section": "Section 3",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S03_Lem3_01_DictatorToJunta.lean",
      "wrappers": [
        "L3_1_DictatorToJunta",
        "L3_1_ImageDictatorToJunta"
      ],
      "deps": [],
      "summary": "Dictators restrict to one-juntas on every matching cube.",
      "statement": "Lemma 3.1 proves completeness on matching cubes.",
      "terms": [],
      "paperLabel": "lem:dictator-to-junta",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $f:S_n\\to\\{0,1\\}$ is a dictator, then for every ordered matching $M$ and base permutation $\\pi$, the restricted cube function $x\\mapsto f(\\pi\\tau_x)$ is a one-junta.",
      "leanLinks": [
        {
          "name": "L3_1_DictatorToJunta",
          "line": 53
        },
        {
          "name": "L3_1_ImageDictatorToJunta",
          "line": 21
        }
      ]
    },
    {
      "id": "S03_02",
      "label": "Lem 3.2",
      "title": "Perfect completeness",
      "section": "Section 3",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S03_Lem3_02_PerfectCompleteness.lean",
      "wrappers": [
        "L3_2_PerfectCompleteness",
        "cubeOneJunta_square_zero"
      ],
      "deps": [
        "S03_01"
      ],
      "summary": "Dictators are accepted by one matching-cube square trial.",
      "statement": "Lemma 3.2 proves perfect completeness.",
      "terms": [
        {
          "text": "Completeness on matching cubes",
          "target": "S03_01"
        }
      ],
      "paperLabel": "lem:perfect-completeness",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $f:S_n\\to\\{0,1\\}$ is a dictator, then every execution of the matching-cube square test accepts $f$.",
      "leanLinks": [
        {
          "name": "L3_2_PerfectCompleteness",
          "line": 72
        },
        {
          "name": "cubeOneJunta_square_zero",
          "line": 21
        }
      ]
    },
    {
      "id": "L4_1",
      "label": "Lem 4.1",
      "title": "Cube square test",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_01_CubeSquare.lean",
      "wrappers": [
        "L4_1_CubeSquare"
      ],
      "deps": [
        "L2_3"
      ],
      "summary": "Boolean-cube square test Fourier calculation.",
      "statement": "Lem 4.1: Boolean-cube square test Fourier calculation.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "lem:cube-square",
      "paperEnv": "lemma",
      "paperStatementLatex": "Choose $u,v\\in\\{0,1\\}^m$ by the following coordinate-by-coordinate rule: independently for each $r\\in[m]$, the pair $(u_r,v_r)$ is uniformly distributed over $(0,0),(1,0),(0,1)$. Then, for\nevery $g:\\{0,1\\}^m\\to\\mathbb R$,\n\\[\n  \\E_{x,u,v}\\bigl[\\Delta_{u,v}g(x)^2\\bigr]\n  \\ge \\frac{32}{9}\\norm{g-P_{\\le1}g}^2.\n\\]",
      "leanLinks": [
        {
          "name": "L4_1_CubeSquare",
          "line": 509
        }
      ]
    },
    {
      "id": "S04_02",
      "label": "Lem 4.2",
      "title": "P_M independent of representatives",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_02_PMIndependentOfRepresentatives.lean",
      "wrappers": [
        "L4_4_PMIndependentOfRepresentatives"
      ],
      "deps": [
        "L2_3"
      ],
      "summary": "Representative-change invariance of the matching-local truncation.",
      "statement": "Lemma 4.2 proves that the definition of P_M is independent of representatives.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "lem:PM-independent-of-representatives",
      "paperEnv": "lemma",
      "paperStatementLatex": "The matching-local projection $P_M$ is independent of the choice of representatives for the matching cube cosets.",
      "leanLinks": [
        {
          "name": "L4_4_PMIndependentOfRepresentatives",
          "line": 22
        }
      ]
    },
    {
      "id": "S04_03",
      "label": "Lem 4.3",
      "title": "P_M fixes local degree one",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_03_PMFixesLocal.lean",
      "wrappers": [
        "L4_5_PMFixesLocal"
      ],
      "deps": [
        "S04_02"
      ],
      "summary": "The matching-local projection fixes exactly the local degree-one functions.",
      "statement": "Lemma 4.3 characterizes the fixed points of P_M.",
      "terms": [
        {
          "text": "P_M independent of representatives",
          "target": "S04_02"
        }
      ],
      "paperLabel": "lem:PM-fixes-local",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every matching $M$, $P_MF$ is locally degree one on every matching cube, and if $H$ is locally degree one on every matching cube, then $P_MH=H$.",
      "leanLinks": [
        {
          "name": "L4_5_PMFixesLocal",
          "line": 20
        }
      ]
    },
    {
      "id": "S04_04",
      "label": "Lem 4.4",
      "title": "Local high-degree error formula",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_04_LocalHighDegreeErrorFormula.lean",
      "wrappers": [
        "L4_6_LocalHighDegreeErrorFormula"
      ],
      "deps": [
        "S04_02",
        "L2_3"
      ],
      "summary": "Identifies local projection error with average high-degree cube energy.",
      "statement": "Lemma 4.4 proves the local high-degree error formula.",
      "terms": [
        {
          "text": "P_M independent of representatives",
          "target": "S04_02"
        },
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "lem:PM-error-formula",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $F:S_n\\to\\mathbb R$ and matching $M$, the squared error $\\|F-P_MF\\|_2^2$ equals the average high-degree Fourier energy of the restrictions of $F$ to the matching cubes of $M$.",
      "leanLinks": [
        {
          "name": "L4_6_LocalHighDegreeErrorFormula",
          "line": 22
        }
      ]
    },
    {
      "id": "S04_05",
      "label": "Lem 4.5",
      "title": "P_M perpendicular",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_05_PMPerpendicular.lean",
      "wrappers": [
        "L4_7_PMPerpendicular"
      ],
      "deps": [
        "S04_03",
        "L2_3"
      ],
      "summary": "The local high-degree residual is orthogonal to the local degree-one space.",
      "statement": "Lemma 4.5 proves perpendicularity of the P_M residual to local degree one.",
      "terms": [
        {
          "text": "P_M fixes local degree one",
          "target": "S04_03"
        },
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "lem:PM-perpendicular",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every matching $M$, the residual $F-P_MF$ is orthogonal to every matching-local degree-one function.",
      "leanLinks": [
        {
          "name": "L4_7_PMPerpendicular",
          "line": 111
        }
      ]
    },
    {
      "id": "S04_06",
      "label": "Lem 4.6",
      "title": "Basic indicators have local degree at most one",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_06_TijLocalDegree.lean",
      "wrappers": [
        "L4_8_TijLocalDegree"
      ],
      "deps": [
        "S03_01",
        "L2_3"
      ],
      "summary": "Each one-coset indicator restricts to local degree at most one.",
      "statement": "Lemma 4.6 proves that a basic indicator has local degree at most one.",
      "terms": [
        {
          "text": "Completeness on matching cubes",
          "target": "S03_01"
        },
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "lem:tij-local-degree",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every matching $M$ and every pair $i,j$, the basic indicator $1_{\\pi(i)=j}$ has matching-local degree at most one on the matching cubes of $M$.",
      "leanLinks": [
        {
          "name": "L4_8_TijLocalDegree",
          "line": 100
        }
      ]
    },
    {
      "id": "S04_07",
      "label": "Cor 4.7",
      "title": "U_1 is local",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Cor4_07_U1Local.lean",
      "wrappers": [
        "Cor4_9_U1Local"
      ],
      "deps": [
        "S04_03",
        "S04_06"
      ],
      "summary": "U_1 is contained in every matching-local degree-one space.",
      "statement": "Corollary 4.7 proves that U_1 is local for every matching.",
      "terms": [
        {
          "text": "P_M fixes local degree one",
          "target": "S04_03"
        },
        {
          "text": "Basic indicators have local degree at most one",
          "target": "S04_06"
        }
      ],
      "paperLabel": "cor:U1-local",
      "paperEnv": "corollary",
      "paperStatementLatex": "For every matching $M$, every $F\\in U_1$ is matching-local degree one and satisfies $P_MF=F$.",
      "leanLinks": [
        {
          "name": "Cor4_9_U1Local",
          "line": 53
        }
      ]
    },
    {
      "id": "L4_9",
      "label": "Lem 4.9",
      "title": "Trial cube coordinates",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_09_TrialCubeCoordinates.lean",
      "wrappers": [
        "L4_11_TrialCubeCoordinates"
      ],
      "deps": [
        "L4_1"
      ],
      "summary": "Identifies a group trial with a Boolean-cube square test on a matching coset.",
      "statement": "Lem 4.9: Identifies a group trial with a Boolean-cube square test on a matching coset.",
      "terms": [
        {
          "text": "Cube square test",
          "target": "L4_1"
        }
      ],
      "paperLabel": "lem:trial-cube-coordinates",
      "paperEnv": "lemma",
      "paperStatementLatex": "One execution of \\cref{alg:matching-trial} can be described equivalently as\nfollows.  First sample $M$ uniformly.  Then sample a coset $C\\in\\cC_M$ uniformly,\na cube point $x\\in\\{0,1\\}^m$ uniformly, and directions $u,v\\in\\{0,1\\}^m$ by the\ncoordinate-by-coordinate rule of \\Cref{lem:cube-square}.  If\n\\begin{equation*}\n  g_{C,M}(y)=f(\\rho_C\\tau_y),\n  \\qquad y\\in\\{0,1\\}^m,\n\\end{equation*}\nthen the four queried values are\n\\begin{equation}\\label{eq:trial-four-cube-values}\n  g_{C,M}(x),\\qquad g_{C,M}(x+u),\\qquad\n  g_{C,M}(x+v),\\qquad g_{C,M}(x+u+v),\n\\end{equation}\nand the algorithm rejects exactly when\n\\begin{equation}\\label{eq:trial-rejects-iff-delta-nonzero}\n  \\Delta_{u,v}g_{C,M}(x)\\neq0.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "L4_11_TrialCubeCoordinates",
          "line": 19
        }
      ]
    },
    {
      "id": "L4_11",
      "label": "Lem 4.11",
      "title": "One-trial soundness",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_11_OneTrialSoundness.lean",
      "wrappers": [
        "L4_13_OneTrialSoundness"
      ],
      "deps": [
        "Thm2_2",
        "Prop4_10"
      ],
      "summary": "Combines square-energy control with the FKN input.",
      "statement": "Lem 4.11: Combines square-energy control with the FKN input.",
      "terms": [
        {
          "text": "FKN/stability input",
          "target": "Thm2_2"
        },
        {
          "text": "Square energy controls global degree",
          "target": "Prop4_10"
        }
      ],
      "paperLabel": "lem:one-trial-soundness",
      "paperEnv": "lemma",
      "paperStatementLatex": "There is an absolute constant $c_0>0$ such that one execution of\n\\cref{alg:matching-trial} rejects every Boolean $f:S_n\\to\\{0,1\\}$ with\nprobability at least\n\\begin{equation}\\label{eq:one-trial-soundness-bound}\n  c_0\\,\\dist(f,\\D)^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "L4_13_OneTrialSoundness",
          "line": 155
        }
      ]
    },
    {
      "id": "Prop4_10",
      "label": "Prop 4.10",
      "title": "Square energy controls global degree",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Prop4_10_SquareEnergyControlsGlobalDegree.lean",
      "wrappers": [
        "Prop4_12_SquareEnergyControlsGlobalDegree"
      ],
      "deps": [
        "L4_1",
        "S04_04",
        "L4_9",
        "Thm4_8"
      ],
      "summary": "Uses the matching spectral gap to control distance from U1.",
      "statement": "Prop 4.10: Uses the matching spectral gap to control distance from U1.",
      "terms": [
        {
          "text": "Cube square test",
          "target": "L4_1"
        },
        {
          "text": "Local high-degree error formula",
          "target": "S04_04"
        },
        {
          "text": "Trial cube coordinates",
          "target": "L4_9"
        },
        {
          "text": "Matching-cube spectral gap",
          "target": "Thm4_8"
        },
        {
          "text": "U1",
          "target": "S05_D08"
        }
      ],
      "paperLabel": "eq:square-energy-global-bound",
      "paperEnv": "proposition",
      "paperStatementLatex": "Let $\\Delta$ denote the alternating sum of the four queried values in one\nexecution of \\cref{alg:matching-trial}.  Then for every $f:S_n\\to\\mathbb R$,\n\\begin{equation}\\label{eq:square-energy-global-bound}\n  \\E[\\Delta^2]\n  \\ge\n  \\frac{16}{27}\\norm{f-P_{U_1}f}^2.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "Prop4_12_SquareEnergyControlsGlobalDegree",
          "line": 156
        }
      ]
    },
    {
      "id": "S05_D01",
      "label": "Def 5.1",
      "title": "Young diagrams and boxes",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean",
      "wrappers": [
        "S05_Def5_01_YoungDiagram",
        "S05_Def5_01_youngRow",
        "S05_Def5_01_youngCells"
      ],
      "deps": [],
      "summary": "Young diagrams, row lengths, boxes, and cells.",
      "statement": "Definition 5.1 introduces Young diagrams, row lengths, Young cells, and the finite set of boxes used throughout the tableau proof.",
      "terms": [],
      "paperLabel": "def:young-diagrams-boxes",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda=(\\lambda_1,\\ldots,\\lambda_\\ell)\\vdash N$.  We identify\n$\\lambda$ with its Young diagram\n\\begin{equation*}\n  [\\lambda]:=\\{(r,c):1\\le r\\le \\ell,\\ 1\\le c\\le \\lambda_r\\},\n\\end{equation*}\nwhere rows and columns are numbered from $1$.  A \\emph{box} of $\\lambda$ is an\nordered pair $u=(r,c)\\in[\\lambda]$; write $\\row(u)=r$ and $\\col(u)=c$.",
      "leanLinks": [
        {
          "name": "S05_Def5_01_YoungDiagram",
          "line": 22
        },
        {
          "name": "S05_Def5_01_youngRow",
          "line": 25
        },
        {
          "name": "S05_Def5_01_youngCells",
          "line": 29
        }
      ]
    },
    {
      "id": "S05_D02",
      "label": "Def 5.2",
      "title": "Removable corners and one-box removals",
      "section": "Definitions",
      "kind": "paper",
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
      "summary": "Subdiagrams, removable rows/corners, one-box children, and finite one-box child sets.",
      "statement": "Definition 5.2 introduces Young subdiagrams, one-box children, removable rows, and removable corners.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "one-box removals",
          "target": "S05_D11"
        }
      ],
      "paperLabel": "def:removable-corners",
      "paperEnv": "definition",
      "paperStatementLatex": "A box $u$ of a Young diagram $\\lambda$ is a \\emph{removable corner} if\n$[\\lambda]\\setminus\\{u\\}$ is again the Young diagram of a partition.  In\ncoordinates this means $u=(r,\\lambda_r)$ and $\\lambda_r>\\lambda_{r+1}$, with\nthe convention $\\lambda_{\\ell+1}=0$.  We write $\\Rem(\\lambda)$ for the set of\nremovable corners.  If $[\\mu]\\subseteq[\\lambda]$, then $\\lambda\\setminus\\mu$\ndenotes the set of boxes $[\\lambda]\\setminus[\\mu]$.  If $u\\in\\Rem(\\lambda)$,\nthen $\\lambda\\setminus\\{u\\}$ denotes the partition whose Young diagram is\n$[\\lambda]\\setminus\\{u\\}$.",
      "leanLinks": [
        {
          "name": "S05_Def5_02_IsYoungSubdiagram",
          "line": 22
        },
        {
          "name": "S05_Def5_02_IsOneBoxChild",
          "line": 27
        },
        {
          "name": "S05_Def5_02_oneBoxChildren",
          "line": 32
        },
        {
          "name": "S05_Def5_02_IsRemovableRow",
          "line": 36
        }
      ]
    },
    {
      "id": "S05_D03",
      "label": "Def 5.3",
      "title": "Standard tableaux and occupation",
      "section": "Definitions",
      "kind": "paper",
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
      "summary": "Standard Young tableaux and the cell occupied by an entry.",
      "statement": "Definition 5.3 introduces standard Young tableaux, the occupied cell of an entry, and the maximum-entry-at-a-cell predicate.",
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
          "line": 22
        },
        {
          "name": "S05_Def5_03_cellOfEntry",
          "line": 26
        },
        {
          "name": "S05_Def5_03_TableauMaxAt",
          "line": 31
        }
      ]
    },
    {
      "id": "S05_D04",
      "label": "Def 5.4",
      "title": "Tableau coordinate space",
      "section": "Definitions",
      "kind": "paper",
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
      "summary": "Tableau-count dimension, coordinate space, and Young basis vectors.",
      "statement": "Definition 5.4 introduces tableauDim, the tableau coordinate space, and basis vectors indexed by standard tableaux.",
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
          "line": 23
        },
        {
          "name": "S05_Def5_04_TableauSpace",
          "line": 27
        },
        {
          "name": "S05_Def5_04_tableauBasisVec",
          "line": 31
        }
      ]
    },
    {
      "id": "S05_D05",
      "label": "Def 5.5",
      "title": "Contents and adjacent operators",
      "section": "Definitions",
      "kind": "paper",
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
      "summary": "Contents, adjacent transposition operators, and diagonal content operators.",
      "statement": "Definition 5.5 introduces cell content, entry content, Young adjacent operators, and diagonal content operators.",
      "terms": [
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        }
      ],
      "paperLabel": "def:content-adjacent-operators",
      "paperEnv": "definition",
      "paperStatementLatex": "For a box $u$, set $c(u)=\\col(u)-\\row(u)$.  If $T\\in\\SYT(\\lambda)$ and\n$a\\in[N]$, set $c_T(a):=c(u_T(a))$.\n\nFor each adjacent index $k$, define a concrete operator\n$S_k^\\lambda\\in\\End(V^\\lambda)$ as follows.  If $k$ and $k+1$ lie in the same\nrow of $T$, set $S_k^\\lambda e_T=e_T$.  If they lie in the same column, set\n$S_k^\\lambda e_T=-e_T$.  Otherwise let $T'=s_kT$ be the tableau obtained by\nswapping the entries $k$ and $k+1$; in this case $T'$ is standard.  On the span\nof $e_T$ and $e_{T'}$, set\n\\begin{equation}\\label{eq:young-orthogonal-two-by-two}\n  S_k^\\lambda\\big|_{\\spanop\\{e_T,e_{T'}\\}}\n  =\n  \\begin{pmatrix}\n    a & b\\\\\n    b & -a\n  \\end{pmatrix},\n  \\qquad\n  a=\\frac{1}{c_T(k+1)-c_T(k)},\n  \\qquad\n  b=\\sqrt{1-a^2},\n\\end{equation}\nwith respect to the ordered basis $(e_T,e_{T'})$.  The formula is independent\nof the choice of representative of the unordered pair $\\{T,T'\\}$, since the\naxial distance changes sign after the swap.",
      "leanLinks": [
        {
          "name": "S05_Def5_05_cellContent",
          "line": 22
        },
        {
          "name": "S05_Def5_05_entryContent",
          "line": 27
        },
        {
          "name": "S05_Def5_05_youngAdjacentOperator",
          "line": 32
        },
        {
          "name": "S05_Def5_05_diagonalContentOperator",
          "line": 37
        }
      ]
    },
    {
      "id": "S05_D06",
      "label": "Def 5.6",
      "title": "Young block",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_06_YoungBlock.lean",
      "wrappers": [
        "S05_YoungBlock"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Young-block index vocabulary.",
      "statement": "Definition 5.6 introduces the Young block indices used in the spectral decomposition interface.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        }
      ],
      "paperLabel": "def:young-block",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash n$, define\n\\begin{equation}\\label{eq:regular-young-decomposition}\n  \\mathcal H_\\lambda\n  :=\\spanop\\{\\pi\\mapsto\\langle e_S,\\rho^\\lambda(\\pi)e_T\\rangle:\n      S,T\\in\\SYT(\\lambda)\\}\\subseteq L^2(S_n;\\mathbb C).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_YoungBlock",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_D07",
      "label": "Def 5.7",
      "title": "Young-block energy profile",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_07_YoungBlockEnergyProfile.lean",
      "wrappers": [
        "S05_Def5_07_YoungBlockEnergyProfile"
      ],
      "deps": [
        "S05_D06"
      ],
      "summary": "Nonnegative Young-block energy profile interface.",
      "statement": "Definition 5.7 introduces the nonnegative Young-block energy profile.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "def:young-block-energy-profile",
      "paperEnv": "definition",
      "paperStatementLatex": "For a function $F:S_n\\to\\mathbb R$, a Young-block energy profile is a map\n$E$ from Young diagrams $\\lambda\\vdash n$ to nonnegative real numbers.  In the\nregular Young decomposition, the intended value is\n\\[\n  E(\\lambda)=\\|\\Pi_\\lambda F\\|_2^2,\n\\]\nwhere $\\Pi_\\lambda$ is orthogonal projection onto $\\mathcal H_\\lambda$.",
      "leanLinks": [
        {
          "name": "S05_Def5_07_YoungBlockEnergyProfile",
          "line": 24
        }
      ]
    },
    {
      "id": "S05_D08",
      "label": "Def 5.8",
      "title": "U1-compatible block profile",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_08_U1CompatibleYoungBlockProfile.lean",
      "wrappers": [
        "S05_Def5_08_U1CompatibleYoungBlockProfile"
      ],
      "deps": [
        "S05_D07"
      ],
      "summary": "Numerical identification of the one-row and standard blocks with U1.",
      "statement": "Definition 5.8 introduces the U1-compatible Young-block profile identifying the one-row and standard blocks with U1.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        }
      ],
      "paperLabel": "def:u1-compatible-young-block-profile",
      "paperEnv": "definition",
      "paperStatementLatex": "A Young-block energy profile $E$ for $F:S_n\\to\\mathbb R$ is\n$U_1$-compatible if\n\\begin{equation}\\label{eq:young-block-energy-u1-compatible}\n  \\norm{F-P_{U_1}F}^2\n  =\\sum_{\\lambda\\notin\\{(n),(n-1,1)\\}} E(\\lambda).\n\\end{equation}\nThese numerical interfaces record the nonnegativity and degree-one-block\nidentification consequences of the regular Young-block decomposition.",
      "leanLinks": [
        {
          "name": "S05_Def5_08_U1CompatibleYoungBlockProfile",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_D09",
      "label": "Def 5.9",
      "title": "Two-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_09_TwoBoxRemovals.lean",
      "wrappers": [
        "S05_IsHorizontalTwoBoxRemoval",
        "S05_IsVerticalTwoBoxRemoval"
      ],
      "deps": [
        "S05_D02"
      ],
      "summary": "Horizontal and vertical two-box removal predicates.",
      "statement": "Definition 5.9 introduces horizontal and vertical two-box removals.",
      "terms": [
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        }
      ],
      "paperLabel": "def:two-box-removals",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda\\vdash N$ with $N\\ge2$.  Define\n\\begin{align*}\n  \\mathsf H_2(\\lambda)\n  &:=\\{\\mu\\vdash N-2:\\lambda\\setminus\\mu\n      \\text{ has two boxes and no two lie in the same column}\\},\\\\\n  \\mathsf V_2(\\lambda)\n  &:=\\{\\mu\\vdash N-2:\\lambda\\setminus\\mu\n      \\text{ has two boxes and no two lie in the same row}\\}.\n\\end{align*}\nA disconnected two-box removal belongs to both sets.",
      "leanLinks": [
        {
          "name": "S05_IsHorizontalTwoBoxRemoval",
          "line": 23
        },
        {
          "name": "S05_IsVerticalTwoBoxRemoval",
          "line": 28
        }
      ]
    },
    {
      "id": "S05_D10",
      "label": "Def 5.10",
      "title": "Signed two-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_10_SignedTwoBoxRemovals.lean",
      "wrappers": [
        "S05_PositiveSignedTwoBoxRemoval",
        "S05_NegativeSignedTwoBoxRemoval"
      ],
      "deps": [
        "S05_D09"
      ],
      "summary": "Signs attached to horizontal and vertical two-box removals.",
      "statement": "Definition 5.10 introduces signed two-box removals.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        },
        {
          "text": "two-box removals",
          "target": "S05_D09"
        }
      ],
      "paperLabel": "def:signed-two-box-removals",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash N$, set\n\\begin{equation*}\n  \\mathsf B_2(\\lambda)\n  :=\\{(\\mu,+):\\mu\\in\\mathsf H_2(\\lambda)\\}\n    \\cup\n    \\{(\\mu,-):\\mu\\in\\mathsf V_2(\\lambda)\\}.\n\\end{equation*}\nFor $\\sigma\\in\\{+,-\\}$, write\n\\begin{equation*}\n  \\varepsilon_+=1,\n  \\qquad\n  \\varepsilon_-=-1.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_PositiveSignedTwoBoxRemoval",
          "line": 25
        },
        {
          "name": "S05_NegativeSignedTwoBoxRemoval",
          "line": 30
        }
      ]
    },
    {
      "id": "S05_D11",
      "label": "Def 5.11",
      "title": "One-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_11_OneBoxRemovals.lean",
      "wrappers": [
        "S05_IsOneBoxRemoval",
        "S05_oneBoxChildrenOdd"
      ],
      "deps": [
        "S05_D02"
      ],
      "summary": "One-box removal vocabulary.",
      "statement": "Definition 5.11 introduces one-box removals and odd one-box children.",
      "terms": [
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        },
        {
          "text": "one-box children",
          "target": "S05_D02"
        }
      ],
      "paperLabel": "def:one-box-removals",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\mu\\vdash N-1$ and $\\lambda\\vdash N$, write $\\mu\\nearrow\\lambda$ if\n$[\\mu]=[\\lambda]\\setminus\\{u\\}$ for some $u\\in\\Rem(\\lambda)$.",
      "leanLinks": [
        {
          "name": "S05_IsOneBoxRemoval",
          "line": 21
        },
        {
          "name": "S05_oneBoxChildrenOdd",
          "line": 30
        }
      ]
    },
    {
      "id": "S05_D12",
      "label": "Def 5.12",
      "title": "One-box deletion spaces",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_12_OneBoxDeletionSpaces.lean",
      "wrappers": [
        "S05_Def5_12_OneBoxDeletionTableaux"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "Deletion-fiber coordinate-space vocabulary.",
      "statement": "Definition 5.12 introduces the one-box deletion coordinate spaces.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
        },
        {
          "text": "coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L05"
        }
      ],
      "paperLabel": "def:one-box-deletion-spaces",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $\\lambda\\vdash N$ and $u\\in\\Rem(\\lambda)$.  Put\n\\begin{equation*}\n  \\mu_u:=\\lambda\\setminus\\{u\\},\n  \\qquad\n  W_u:=\\spanop\\{e_T:T\\in\\SYT(\\lambda),\\ T(u)=N\\}\\subseteq V^\\lambda .\n\\end{equation*}\nDefine the deletion map $D_u:W_u\\rightarrow V^{\\mu_u}$ on basis vectors by\n\\begin{equation*}\n  D_u(e_T):=e_{T|_{[\\mu_u]}} .\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Def5_12_OneBoxDeletionTableaux",
          "line": 22
        }
      ]
    },
    {
      "id": "S05_D13",
      "label": "Def 5.13",
      "title": "Even sign-pattern multiset",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_13_EvenSignPatternMultiset.lean",
      "wrappers": [
        "S05_evenZeroSignPatternCount",
        "S05_evenHighSignPatternCount"
      ],
      "deps": [
        "S05_D09"
      ],
      "summary": "Even zero/high sign-pattern counters.",
      "statement": "Definition 5.13 introduces the even sign-pattern multiset counters.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        }
      ],
      "paperLabel": "def:even-sign-patterns",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash2m$, define a multiset $\\mathsf X_m(\\lambda)$ of subsets of\n$[m]$ as follows.  For $m=1$,\n\\begin{equation*}\n  \\mathsf X_1((2))=\\{\\emptyset\\},\n  \\qquad\n  \\mathsf X_1((1,1))=\\{\\{1\\}\\}.\n\\end{equation*}\nFor $m\\ge2$,\n\\begin{equation}\\label{eq:X-recursion-even}\n\\begin{aligned}\n  \\mathsf X_m(\\lambda)\n  :=&\\biguplus_{\\mu\\in\\mathsf H_2(\\lambda)}\n      \\{R:R\\in\\mathsf X_{m-1}(\\mu)\\}  \\\\\n   &\\uplus\n     \\biguplus_{\\mu\\in\\mathsf V_2(\\lambda)}\n      \\{R\\cup\\{m\\}:R\\in\\mathsf X_{m-1}(\\mu)\\}.\n\\end{aligned}\n\\end{equation}\nHere $\\biguplus$ is multiset union.  Set\n\\begin{equation*}\n  z_m(\\lambda):=|\\{R\\in\\mathsf X_m(\\lambda):R=\\emptyset\\}|,\n  \\qquad\n  h_m(\\lambda):=|\\{R\\in\\mathsf X_m(\\lambda):|R|\\ge2\\}|.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_evenZeroSignPatternCount",
          "line": 24
        },
        {
          "name": "S05_evenHighSignPatternCount",
          "line": 29
        }
      ]
    },
    {
      "id": "S05_D14",
      "label": "Def 5.14",
      "title": "Odd sign-pattern multiset",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_14_OddSignPatternMultiset.lean",
      "wrappers": [
        "S05_oddHighSignPatternCount"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "Odd high sign-pattern counter.",
      "statement": "Definition 5.14 introduces the odd sign-pattern multiset counter.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
        }
      ],
      "paperLabel": "def:odd-sign-patterns",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash2m+1$, define\n\\begin{equation}\\label{eq:X-recursion-odd}\n  \\mathsf X_m^{\\mathrm{odd}}(\\lambda)\n  :=\\biguplus_{\\mu\\nearrow\\lambda}\\mathsf X_m(\\mu),\n\\end{equation}\nand set\n\\begin{equation*}\n  h_m^{\\mathrm{odd}}(\\lambda)\n  :=|\\{R\\in\\mathsf X_m^{\\mathrm{odd}}(\\lambda):|R|\\ge2\\}|.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_oddHighSignPatternCount",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_D15",
      "label": "Def 5.15",
      "title": "Matching characters",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_15_MatchingCharacters.lean",
      "wrappers": [
        "S05_matchingCharacter",
        "S05_matchingCharacterWeight"
      ],
      "deps": [
        "L2_3"
      ],
      "summary": "Matching-cube character vocabulary.",
      "statement": "Definition 5.15 introduces matching characters and their weights on matching cubes.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ],
      "paperLabel": "def:matching-characters",
      "paperEnv": "definition",
      "paperStatementLatex": "Let $M=\\{\\tau_1,\\ldots,\\tau_m\\}$ be a matching, where $\\tau_r$ swaps the two\npoints in the $r$-th edge.  Define\n\\begin{equation*}\n  A_M:=\\{\\tau_x:x\\in\\{0,1\\}^m\\},\n  \\qquad\n  \\tau_x:=\\prod_{r:x_r=1}\\tau_r .\n\\end{equation*}\nThe product is order-independent because the transpositions in a matching are\ndisjoint and hence commute.  For $R\\subseteq[m]$, define\n\\begin{equation*}\n  \\chi_R(\\tau_x):=(-1)^{\\sum_{r\\in R}x_r}.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_matchingCharacter",
          "line": 35
        },
        {
          "name": "S05_matchingCharacterWeight",
          "line": 39
        }
      ]
    },
    {
      "id": "S05_D16",
      "label": "Def 5.16",
      "title": "Even matching eigenvectors",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_16_IsMatchingEigenvectorEven.lean",
      "wrappers": [
        "S05_IsMatchingEigenvectorEven"
      ],
      "deps": [
        "S05_L01",
        "S05_D15"
      ],
      "summary": "Even simultaneous matching-edge eigenvector predicate.",
      "statement": "Definition 5.16 introduces the even simultaneous matching-eigenvector predicate.",
      "terms": [
        {
          "text": "Matching operators",
          "target": "S05_L01"
        }
      ],
      "paperLabel": "def:even-matching-eigenvector",
      "paperEnv": "definition",
      "paperStatementLatex": "Let \\(M\\) be a perfect matching on \\([2m]\\).  A vector \\(v\\in V^\\lambda\\) is\nan even \\(M\\)-matching eigenvector with label \\(R\\subseteq[m]\\) if\n\\begin{equation}\\label{eq:matching-eigenbasis-definition}\n  \\rho^\\lambda(\\tau_x)v=\\chi_R(\\tau_x)v\n  \\qquad(x\\in\\{0,1\\}^m).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_IsMatchingEigenvectorEven",
          "line": 22
        }
      ]
    },
    {
      "id": "S05_D17",
      "label": "Def 5.17",
      "title": "Odd matching eigenvectors",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_17_IsMatchingEigenvectorOdd.lean",
      "wrappers": [
        "S05_IsMatchingEigenvectorOdd"
      ],
      "deps": [
        "S05_L01",
        "S05_D15"
      ],
      "summary": "Odd simultaneous matching-edge eigenvector predicate.",
      "statement": "Definition 5.17 introduces the odd simultaneous matching-eigenvector predicate.",
      "terms": [
        {
          "text": "Matching operators",
          "target": "S05_L01"
        }
      ],
      "paperLabel": "def:odd-matching-eigenvector",
      "paperEnv": "definition",
      "paperStatementLatex": "Let \\(M\\) be a near-perfect matching on \\([2m+1]\\) with \\(m\\) edges.  A vector\n\\(v\\in V^\\lambda\\) is an odd \\(M\\)-matching eigenvector with label\n\\(R\\subseteq[m]\\) if it satisfies \\eqref{eq:matching-eigenbasis-definition}\nfor every \\(\\tau_x\\in A_M\\).",
      "leanLinks": [
        {
          "name": "S05_IsMatchingEigenvectorOdd",
          "line": 22
        }
      ]
    },
    {
      "id": "S05_D18",
      "label": "Def 5.18",
      "title": "Even restriction scalar input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_18_MatchingRestrictionEvenInput.lean",
      "wrappers": [
        "MatchingRestrictionEvenInput"
      ],
      "deps": [
        "S05_D13"
      ],
      "summary": "Even scalar matching-restriction input.",
      "statement": "Definition 5.18 introduces the even matching-restriction scalar input.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        }
      ],
      "paperLabel": "def:even-matching-restriction-input",
      "paperEnv": "definition",
      "paperStatementLatex": "Let \\(M\\) be a perfect matching on \\([2m]\\).  The even matching-restriction\ninput for \\(\\lambda\\vdash 2m\\) is the assertion that \\(V^\\lambda\\) has an\northonormal basis \\(v_1,\\ldots,v_{d_\\lambda}\\) and a listing\n\\(R_1,\\ldots,R_{d_\\lambda}\\) of \\(\\mathsf X_m(\\lambda)\\) such that each\n\\(v_a\\) is an even \\(M\\)-matching eigenvector with label \\(R_a\\).",
      "leanLinks": [
        {
          "name": "MatchingRestrictionEvenInput",
          "line": 24
        }
      ]
    },
    {
      "id": "S05_D19",
      "label": "Def 5.19",
      "title": "Odd restriction scalar input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_19_MatchingRestrictionOddInput.lean",
      "wrappers": [
        "MatchingRestrictionOddInput"
      ],
      "deps": [
        "S05_D14"
      ],
      "summary": "Odd scalar matching-restriction input.",
      "statement": "Definition 5.19 introduces the odd matching-restriction scalar input.",
      "terms": [
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        },
        {
          "text": "matching-restriction scalar input",
          "target": "S05_D18"
        }
      ],
      "paperLabel": "def:odd-matching-restriction-input",
      "paperEnv": "definition",
      "paperStatementLatex": "Let \\(M\\) be a near-perfect matching on \\([2m+1]\\) with \\(m\\) edges.  The odd\nmatching-restriction input for \\(\\lambda\\vdash 2m+1\\) is the assertion that\n\\(V^\\lambda\\) has an orthonormal basis \\(v_1,\\ldots,v_{d_\\lambda}\\) and a\nlisting \\(R_1,\\ldots,R_{d_\\lambda}\\) of\n\\(\\mathsf X_m^{\\mathrm{odd}}(\\lambda)\\) such that each \\(v_a\\) is an odd\n\\(M\\)-matching eigenvector with label \\(R_a\\).",
      "leanLinks": [
        {
          "name": "MatchingRestrictionOddInput",
          "line": 24
        }
      ]
    },
    {
      "id": "S05_D20",
      "label": "Def 5.20",
      "title": "Even trace input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_20_TraceLocalTruncationEvenInput.lean",
      "wrappers": [
        "TraceLocalTruncationEvenInput"
      ],
      "deps": [
        "S05_D18"
      ],
      "summary": "Even scalar trace formula interface.",
      "statement": "Definition 5.20 introduces the even local-truncation trace input.",
      "terms": [
        {
          "text": "Even restriction scalar input",
          "target": "S05_D18"
        }
      ],
      "paperLabel": "def:even-local-truncation-trace-input",
      "paperEnv": "definition",
      "paperStatementLatex": "For \\(n=2m\\), the even local-truncation trace input is the blockwise scalar\nidentity\n\\begin{equation*}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m(\\lambda)\n  \\qquad(\\lambda\\vdash2m),\n\\end{equation*}\nfor a perfect matching \\(M\\) on \\([2m]\\).",
      "leanLinks": [
        {
          "name": "TraceLocalTruncationEvenInput",
          "line": 21
        }
      ]
    },
    {
      "id": "S05_D21",
      "label": "Def 5.21",
      "title": "Odd trace input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_21_TraceLocalTruncationOddInput.lean",
      "wrappers": [
        "TraceLocalTruncationOddInput"
      ],
      "deps": [
        "S05_D19"
      ],
      "summary": "Odd scalar trace formula interface.",
      "statement": "Definition 5.21 introduces the odd local-truncation trace input.",
      "terms": [
        {
          "text": "Odd restriction scalar input",
          "target": "S05_D19"
        },
        {
          "text": "local-truncation trace input",
          "target": "S05_D20"
        }
      ],
      "paperLabel": "def:odd-local-truncation-trace-input",
      "paperEnv": "definition",
      "paperStatementLatex": "For \\(n=2m+1\\), the odd local-truncation trace input is the blockwise scalar\nidentity\n\\begin{equation*}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m^{\\mathrm{odd}}(\\lambda)\n  \\qquad(\\lambda\\vdash2m+1),\n\\end{equation*}\nfor a near-perfect matching \\(M\\) on \\([2m+1]\\).",
      "leanLinks": [
        {
          "name": "TraceLocalTruncationOddInput",
          "line": 21
        }
      ]
    },
    {
      "id": "S05_D22",
      "label": "Def 5.22",
      "title": "Matching idempotents",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_22_MatchingIdempotents.lean",
      "wrappers": [
        "S05_matchingLowIdempotent",
        "S05_matchingHighIdempotent",
        "S05_matchingLow_add_matchingHigh"
      ],
      "deps": [
        "S05_D15"
      ],
      "summary": "Low/high matching idempotents and their complementary identities.",
      "statement": "Definition 5.22 introduces the low and high matching idempotents and proves their complementary identities.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D15"
        }
      ],
      "paperLabel": "def:matching-idempotents",
      "paperEnv": "definition",
      "paperStatementLatex": "For a matching $M$ with $m$ edges, define elements of $\\mathbb C[S_n]$ by\n\\begin{equation*}\n  e_R^M:=2^{-m}\\sum_{x\\in\\{0,1\\}^m}\\chi_R(\\tau_x)\\tau_x,\n  \\qquad\n  p_M:=\\sum_{|R|\\le1}e_R^M,\n  \\qquad\n  q_M:=1-p_M .\n\\end{equation*}\nIf $a\\in\\mathbb C[S_n]$, let $C_a$ denote right convolution by $a$.",
      "leanLinks": [
        {
          "name": "S05_matchingLowIdempotent",
          "line": 25
        },
        {
          "name": "S05_matchingHighIdempotent",
          "line": 30
        },
        {
          "name": "S05_matchingLow_add_matchingHigh",
          "line": 222
        }
      ]
    },
    {
      "id": "S05_D23",
      "label": "Def 5.23",
      "title": "Young-basis scalar commutant input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_23_YoungBasisScalarCommutantInput.lean",
      "wrappers": [
        "S05_Def5_23_YoungBasisScalarCommutantInput"
      ],
      "deps": [
        "S05_D06"
      ],
      "summary": "Scalarity interface consumed by the spectral bridge.",
      "statement": "Definition 5.23 introduces the Young-basis scalar commutant input.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "def:young-basis-scalar-commutant-input",
      "paperEnv": "definition",
      "paperStatementLatex": "Let \\(E\\) be a Young-block energy profile for \\(F:S_n\\to\\mathbb R\\), and let\n\\(\\theta_\\lambda\\) be real scalars indexed by Young diagrams \\(\\lambda\\vdash n\\).\nThe Young-basis scalar commutant input for the averaged rejection\n\\(\\cA=\\E_M(I-P_M)\\) is the identity\n\\begin{equation*}\n  \\ip{F}{\\cA F}\n  =\n  \\sum_{\\lambda\\notin\\{(n),(n-1,1)\\}}\\theta_\\lambda E(\\lambda).\n\\end{equation*}\nIt records that \\(\\cA\\) acts by a scalar on each Young block.",
      "leanLinks": [
        {
          "name": "S05_Def5_23_YoungBasisScalarCommutantInput",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_D24",
      "label": "Def 5.24",
      "title": "Tableau even height",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_24_TableauEvenHeight.lean",
      "wrappers": [
        "hEvenTableau"
      ],
      "deps": [
        "S05_D04",
        "S05_D13"
      ],
      "summary": "Tableau-count even high-weight height used by the finite certificate and spectral bridge.",
      "statement": "Definition 5.24 introduces the tableau-count even height hEvenTableau.",
      "terms": [
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        }
      ],
      "paperLabel": "def:tableau-even-height",
      "paperEnv": "definition",
      "paperStatementLatex": "Define the tableau-count even height $h_m^{\\mathrm{tab}}(\\lambda)$ by\n$h_0^{\\mathrm{tab}}=0$ and\n\\[\n  h_m^{\\mathrm{tab}}(\\lambda)=\n  \\sum_{\\mu\\in\\mathsf H_2(\\lambda)}h_{m-1}^{\\mathrm{tab}}(\\mu)+\n  \\sum_{\\mu\\in\\mathsf V_2(\\lambda)}(d_\\mu-z_{m-1}(\\mu)).\n\\]",
      "leanLinks": [
        {
          "name": "hEvenTableau",
          "line": 24
        }
      ]
    },
    {
      "id": "S05_D25",
      "label": "Def 5.25",
      "title": "Tableau odd height",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_25_TableauOddHeight.lean",
      "wrappers": [
        "hOddTableau"
      ],
      "deps": [
        "S05_D24",
        "S05_D14"
      ],
      "summary": "Tableau-count odd high-weight height obtained by one-box deletion to even shapes.",
      "statement": "Definition 5.25 introduces the tableau-count odd height hOddTableau.",
      "terms": [
        {
          "text": "Tableau even height",
          "target": "S05_D24"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        }
      ],
      "paperLabel": "def:tableau-odd-height",
      "paperEnv": "definition",
      "paperStatementLatex": "For $\\lambda\\vdash2m+1$, define\n\\[\n  h_m^{\\mathrm{odd,tab}}(\\lambda)=\n  \\sum_{\\mu\\in\\mathsf O_1(\\lambda)} h_m^{\\mathrm{tab}}(\\mu),\n\\]\nwhere $\\mathsf O_1(\\lambda)$ is the set of one-box children of $\\lambda$.",
      "leanLinks": [
        {
          "name": "hOddTableau",
          "line": 24
        }
      ]
    },
    {
      "id": "S05_D26",
      "label": "Def 5.26",
      "title": "Certificate special diagrams",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "minor",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_26_CertificateSpecialDiagrams.lean",
      "wrappers": [
        "oneRowDiagram",
        "twoRowDiagram",
        "threeRowDiagram",
        "standardDiagramEven",
        "twoRowTwoDiagramEven",
        "twoRowTwoDiagramOdd"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Canonical Young diagrams used in the finite certificate case checks.",
      "statement": "Definition 5.26 introduces the canonical special diagrams used in the finite certificate checks.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        }
      ],
      "paperLabel": "def:certificate-special-diagrams",
      "paperEnv": "definition",
      "paperStatementLatex": "We use canonical names for the special diagrams appearing in the finite checks:\n$(n)$, $(a,b)$, $(a,b,c)$, the standard even shape $(2m-1,1)$, the even\nexceptional shapes, the odd exceptional shapes, and the size-four column\n$(1,1,1,1)$.",
      "leanLinks": [
        {
          "name": "oneRowDiagram",
          "line": 16
        },
        {
          "name": "twoRowDiagram",
          "line": 45
        },
        {
          "name": "threeRowDiagram",
          "line": 156
        }
      ]
    },
    {
      "id": "S05_D27",
      "label": "Def 5.27",
      "title": "Certificate exceptional predicates",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_27_CertificateExceptionalPredicates.lean",
      "wrappers": [
        "HasOneRowHorizontalChild",
        "HasOneRowVerticalChild",
        "HasStandardHorizontalChild",
        "IsEvenHExceptional",
        "HasOneRowOneBoxChild",
        "HasStandardOneBoxChild",
        "IsOddHExceptional"
      ],
      "deps": [
        "S05_D09",
        "S05_D11"
      ],
      "summary": "Predicates for finite-certificate bad children and exceptional shapes.",
      "statement": "Definition 5.27 introduces the finite-certificate exceptional-child and exceptional-shape predicates.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        },
        {
          "text": "One-box removals",
          "target": "S05_D11"
        }
      ],
      "paperLabel": "def:certificate-exceptional-predicates",
      "paperEnv": "definition",
      "paperStatementLatex": "We name the child obstructions used by the certificate inductions and the exceptional even\nshapes\n\\[(2m-2,2),(2m-2,1,1),(2m-3,3),(2m-3,2,1)\\]\nand odd shapes\n\\[(2m-1,2),(2m-1,1,1).\\]",
      "leanLinks": [
        {
          "name": "IsEvenHExceptional",
          "line": 47
        },
        {
          "name": "IsOddHExceptional",
          "line": 71
        }
      ]
    },
    {
      "id": "S05_D28",
      "label": "Def 5.28",
      "title": "Group-algebra action interface",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_28_GroupAlgebraAction.lean",
      "wrappers": [
        "GroupAlgebraElement",
        "rightConvolution",
        "repOfGroupAlgebraElement",
        "repOfGroupAlgebraElement_commutes_of_central",
        "repOfGroupAlgebraElements_commute_of_central",
        "YoungRepresentationActionData",
        "averagedRejectionYoungOperatorData_of_centralGroupAlgebraElement"
      ],
      "deps": [
        "S05_L16A"
      ],
      "summary": "Finite group-algebra action and the centrality-to-commutation theorem.",
      "statement": "Definition 5.28 introduces finite group-algebra coefficients, right convolution, representation action rho(a), and a Young representation-action interface. Explicit finite conjugation reindexing proves that coefficient centrality implies commutation with every represented group element and every represented group-algebra element.",
      "terms": [
        {
          "text": "AveragedRejectionYoungOperatorData",
          "target": "S05_L16A"
        },
        {
          "text": "adjacent/content commutation",
          "target": "S05_L16A"
        }
      ],
      "paperLabel": "def:group-algebra-action-interface",
      "paperEnv": "definition",
      "paperStatementLatex": "A finite group-algebra element is a coefficient function $a:G\\to\\mathbb R$.  It acts by right convolution\n\\[(C_aF)(x)=\\sum_{g\\in G}a(g)F(xg)\\]\nand, under a representation $\\rho$, by\n\\[\\rho(a)v=\\sum_{g\\in G}a(g)\\rho(g)v.\\]\nFor a Young block, the interface records the represented adjacent transpositions and Jucys--Murphy content elements needed to build the averaged rejection operator.",
      "leanLinks": [
        {
          "name": "rightConvolution",
          "line": 26
        },
        {
          "name": "repOfGroupAlgebraElement",
          "line": 48
        },
        {
          "name": "repOfGroupAlgebraElement_commutes_of_central",
          "line": 152
        },
        {
          "name": "repOfGroupAlgebraElements_commute_of_central",
          "line": 201
        },
        {
          "name": "YoungRepresentationActionData",
          "line": 234
        },
        {
          "name": "YoungRepresentationActionData.ofAppendixA",
          "line": 251
        },
        {
          "name": "averagedRejectionYoungOperatorData_of_centralGroupAlgebraElement",
          "line": 345
        }
      ]
    },
    {
      "id": "S05_D29",
      "label": "Def 5.29",
      "title": "Averaged high-matching element",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_29_AveragedHighMatchingElement.lean",
      "wrappers": [
        "S05_fixedMatchingCharacterElement",
        "representedMatchingIdempotent_apply_eigenvector",
        "representedHighMatchingElement_apply_eigenvector",
        "S05_fixedMatchingHighElement",
        "S05_fixedMatchingHighElement_rightConvolution",
        "S05_averagedHighMatchingElement",
        "S05_averagedHighMatchingElement_central",
        "S05_averagedRejectionYoungOperatorData_actual",
        "S05_averagedRejectionYoungOperatorData_from_appendixA",
        "S05_averagedRejectionYoungOperator_scalar_on_basis",
        "S05_averagedRejectionYoungOperator_scalar_from_appendixA"
      ],
      "deps": [
        "S05_D22",
        "S05_D28"
      ],
      "summary": "Actual character and high matching elements, their eigenvector action, centrality, and one-block represented action.",
      "statement": "Definition 5.29 pushes each matching-character Fourier idempotent and the high Fourier kernel into the symmetric-group algebra. Boolean-character orthogonality proves that the represented character idempotent selects its eigenspace and that the represented high element acts by one on high characters and zero on low characters. Averaging gives the central element and the scalar one-block Young operator.",
      "terms": [
        {
          "text": "Matching idempotents",
          "target": "S05_D22"
        },
        {
          "text": "Group-algebra action",
          "target": "S05_D28"
        },
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L15"
        }
      ],
      "paperLabel": "def:averaged-high-matching-element",
      "paperEnv": "definition",
      "paperStatementLatex": "For a matching $M$, let $q_M$ be the high-character idempotent in the matching subgroup algebra. Define the averaged element by\n\\[q=\\frac{1}{|\\mathcal M_n|}\\sum_{M\\in\\mathcal M_n}q_M.\\]\nRelabeling gives $q_{\\sigma M}(\\sigma g\\sigma^{-1})=q_M(g)$, hence $q(\\sigma g\\sigma^{-1})=q(g)$.",
      "leanLinks": [
        {
          "name": "S05_fixedMatchingCharacterElement",
          "line": 157
        },
        {
          "name": "representedMatchingIdempotent_apply_eigenvector",
          "line": 206
        },
        {
          "name": "representedHighMatchingElement_apply_eigenvector",
          "line": 292
        },
        {
          "name": "S05_fixedMatchingHighElement",
          "line": 169
        },
        {
          "name": "S05_fixedMatchingHighElement_rightConvolution",
          "line": 341
        },
        {
          "name": "S05_averagedHighMatchingElement",
          "line": 431
        },
        {
          "name": "S05_averagedHighMatchingElement_central",
          "line": 513
        },
        {
          "name": "S05_averagedRejectionYoungOperatorData_actual",
          "line": 623
        },
        {
          "name": "S05_averagedRejectionYoungOperatorData_from_appendixA",
          "line": 633
        },
        {
          "name": "S05_averagedRejectionYoungOperator_scalar_on_basis",
          "line": 665
        },
        {
          "name": "S05_averagedRejectionYoungOperator_scalar_from_appendixA",
          "line": 681
        }
      ]
    },
    {
      "id": "S05_D30",
      "label": "Def 5.30",
      "title": "Tableau-operator trace",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Defs/S05_Def5_30_TableauOperatorTrace.lean",
      "wrappers": [
        "tableauOperatorTrace",
        "tableauOperatorTrace_eq_linearMapTrace",
        "fixedMatchingRejectionYoungOperator_trace_eq_highLabelCount_of_eigenbasis",
        "S05_fixedMatchingRejectionYoungOperator_trace_eq_sum_characters",
        "youngBlockTrace_eq_tableauDim_mul_repTrace",
        "tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis",
        "scalar_eq_tableauOperatorTrace_div_tableauDim",
        "S05_averagedRejectionYoungOperator_trace_eq_average_fixed"
      ],
      "deps": [
        "S05_D04",
        "S05_D29"
      ],
      "summary": "Basis-independent tableau trace, fixed-eigenbasis count, full-block dimension factor, and scalar/average formulas.",
      "statement": "Definition 5.30 defines operator trace by summing diagonal tableau-basis coefficients and proves that this is Mathlib's basis-independent linear-map trace. In any supplied matching eigenbasis, the concrete fixed high-matching trace equals the number of high character labels. It also proves the extra tableau-dimension factor for right action on the full matrix-coordinate block and the scalar and matching-average trace formulas.",
      "terms": [
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "Averaged high-matching element",
          "target": "S05_D29"
        }
      ],
      "paperLabel": "def:tableau-operator-trace",
      "paperEnv": "definition",
      "paperStatementLatex": "For an operator $B$ on the tableau-coordinate space, define\n\\[\\operatorname{tr}_{\\mathrm{tab}}(B)=\\sum_{T\\in\\operatorname{SYT}(\\lambda)}(Be_T)(T).\\]\nIf $Be_T=c e_T$ for every $T$, then $\\operatorname{tr}_{\\mathrm{tab}}(B)=d_\\lambda c$.",
      "leanLinks": [
        {
          "name": "tableauOperatorTrace",
          "line": 27
        },
        {
          "name": "tableauOperatorTrace_eq_linearMapTrace",
          "line": 41
        },
        {
          "name": "fixedMatchingRejectionYoungOperator_trace_eq_highLabelCount_of_eigenbasis",
          "line": 66
        },
        {
          "name": "youngBlockTrace_eq_tableauDim_mul_repTrace",
          "line": 127
        },
        {
          "name": "S05_fixedMatchingRejectionYoungOperator_trace_eq_sum_characters",
          "line": 141
        },
        {
          "name": "tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis",
          "line": 181
        },
        {
          "name": "S05_averagedRejectionYoungOperator_trace_eq_tableauDim_mul_scalar",
          "line": 219
        },
        {
          "name": "S05_averagedRejectionYoungOperator_trace_eq_average_fixed",
          "line": 239
        },
        {
          "name": "S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim",
          "line": 290
        }
      ]
    },
    {
      "id": "S05_L01",
      "label": "Lem 5.1",
      "title": "Tableau Coxeter model",
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
      "summary": "Concrete adjacent-transposition matrices on tableau coordinates.",
      "statement": "Lemma 5.1 proves the concrete tableau-coordinate Coxeter model for adjacent transpositions.",
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
          "line": 1279
        }
      ]
    },
    {
      "id": "S05_L02",
      "label": "Lem 5.2",
      "title": "Diagonal content eigenspaces",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_02_DiagonalContentEigenspaces.lean",
      "wrappers": [
        "S05_Lem5_02_diagonalContentEigenspaces"
      ],
      "deps": [
        "S05_D05",
        "AppA_02"
      ],
      "summary": "Explicit diagonal content eigenspaces in the tableau basis.",
      "statement": "Lemma 5.2 proves diagonal content eigenspaces for the explicit content operators.",
      "terms": [
        {
          "text": "Contents and adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "AppA_02"
        }
      ],
      "paperLabel": "lem:jucys-murphy-eigenbasis",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $1\\le k\\le N$, let $C_k^\\lambda\\in\\End(V^\\lambda)$ be the diagonal\ncontent operator\n\\begin{equation}\\label{eq:content-diagonal-operator}\n  C_k^\\lambda e_T=c_T(k)e_T\n  \\qquad (T\\in\\SYT(\\lambda)).\n\\end{equation}\nThen the common eigenspaces of $C_1^\\lambda,\\ldots,C_N^\\lambda$ are exactly\nthe lines $\\mathbb C e_T$, $T\\in\\SYT(\\lambda)$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_02_diagonalContentEigenspaces",
          "line": 489
        }
      ]
    },
    {
      "id": "S05_L03",
      "label": "Lem 5.3",
      "title": "Two-box tableau branching",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_03_TwoBoxTableauBranching.lean",
      "wrappers": [
        "S05_Lem5_03_twoStepDeletionTableauxEquivChildTableaux"
      ],
      "deps": [
        "S05_D09",
        "S05_D03"
      ],
      "summary": "Fixed two-step deletion equivalence for tableaux.",
      "statement": "Lemma 5.3 proves fixed two-box tableau branching by iterated maximum-entry deletion.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        },
        {
          "text": "Standard-tableau deletion API",
          "target": "S05_D03"
        }
      ],
      "paperLabel": "lem:two-box-tableau-branching",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $\\lambda\\vdash N$ with $N\\ge2$.  For each\n$(\\mu,\\sigma)\\in\\mathsf B_2(\\lambda)$ there is a subspace\n$W_{\\mu,\\sigma}\\subseteq V^\\lambda$ and a unitary map\n\\begin{equation*}\n  D_{\\mu,\\sigma}:W_{\\mu,\\sigma}\\rightarrow V^\\mu .\n\\end{equation*}\nThe subspaces are mutually orthogonal and\n\\begin{equation}\\label{eq:two-box-orthogonal-sum}\n  V^\\lambda\n  =\\bigoplus_{(\\mu,\\sigma)\\in\\mathsf B_2(\\lambda)} W_{\\mu,\\sigma} .\n\\end{equation}\nFor every $w\\in W_{\\mu,\\sigma}$,\n\\begin{equation}\\label{eq:two-box-last-transposition}\n  S_{N-1}^\\lambda w=\\varepsilon_\\sigma w .\n\\end{equation}\nFor every $1\\le i\\le N-3$ and every $w\\in W_{\\mu,\\sigma}$,\n\\begin{equation}\\label{eq:two-box-intertwining}\n  D_{\\mu,\\sigma}\\bigl(S_i^\\lambda w\\bigr)\n  =S_i^\\mu D_{\\mu,\\sigma}(w).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_03_twoStepDeletionTableauxEquivChildTableaux",
          "line": 433
        }
      ]
    },
    {
      "id": "S05_L04",
      "label": "Lem 5.4",
      "title": "One-box corner decomposition",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_04_OneBoxCornerDecomposition.lean",
      "wrappers": [
        "S05_Lem5_04_row_form",
        "S05_Lem5_04_removable_corner"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "A one-box child removes a unique removable corner.",
      "statement": "Lemma 5.4 proves that one-box children differ in a unique removable corner.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
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
          "name": "S05_Lem5_04_row_form",
          "line": 77
        },
        {
          "name": "S05_Lem5_04_removable_corner",
          "line": 105
        }
      ]
    },
    {
      "id": "S05_L05",
      "label": "Lem 5.5",
      "title": "One-box deletion is unitary",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_05_OneBoxDeletionIsUnitary.lean",
      "wrappers": [
        "S05_Lem5_05_deletionCoordinateMap_inner"
      ],
      "deps": [
        "S05_D12",
        "S05_L04"
      ],
      "summary": "The deletion coordinate map preserves the finite coordinate inner product.",
      "statement": "Lemma 5.5 proves that one-box deletion is unitary on the finite coordinate spaces.",
      "terms": [
        {
          "text": "One-box deletion spaces",
          "target": "S05_D12"
        },
        {
          "text": "One-box corner decomposition",
          "target": "S05_L04"
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
          "name": "S05_Lem5_05_deletionCoordinateMap_inner",
          "line": 353
        }
      ]
    },
    {
      "id": "S05_L06",
      "label": "Lem 5.6",
      "title": "Deletion intertwines earlier swaps",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_06_OneBoxDeletionIntertwinesEarlierSwaps.lean",
      "wrappers": [
        "S05_Lem5_06_deletionCoordinateMap_youngAdjacentOperator_intertwines"
      ],
      "deps": [
        "S05_L05",
        "S05_L01"
      ],
      "summary": "One-box deletion intertwines earlier adjacent operators and content operators.",
      "statement": "Lemma 5.6 proves that one-box deletion intertwines earlier adjacent swaps and content operators.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L05"
        },
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L05"
        }
      ],
      "paperLabel": "lem:one-box-deletion-intertwines",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $\\lambda\\vdash N$, let $u\\in\\Rem(\\lambda)$, and let $1\\le i\\le N-2$.\nFor every $w\\in W_u$,\n\\begin{equation}\\label{eq:one-box-intertwining}\n  D_u\\bigl(S_i^\\lambda w\\bigr)=S_i^{\\mu_u}D_u(w).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_06_deletionCoordinateMap_youngAdjacentOperator_intertwines",
          "line": 676
        }
      ]
    },
    {
      "id": "S05_L07",
      "label": "Lem 5.7",
      "title": "Two-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_07_TwoBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_07_tableauDim_twoStrip_branching_sized"
      ],
      "deps": [
        "S05_L03"
      ],
      "summary": "Tableau-count dimension recursion for two-box removals.",
      "statement": "Lemma 5.7 proves the two-box tableauDim dimension recursion.",
      "terms": [
        {
          "text": "Two-box tableau branching",
          "target": "S05_L03"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "two-box removals",
          "target": "S05_D09"
        }
      ],
      "paperLabel": "lem:dimension-two-strip-recurrence",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every partition $\\lambda\\vdash 2m$ with $m\\ge2$,\n\\begin{equation}\\label{eq:dimension-two-strip-recurrence}\n  d_\\lambda\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}d_\\mu\n   +\\sum_{\\mu\\in\\mathsf V_2(\\lambda)}d_\\mu .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_07_tableauDim_twoStrip_branching_sized",
          "line": 107
        }
      ]
    },
    {
      "id": "S05_L08",
      "label": "Lem 5.8",
      "title": "One-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_08_OneBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_08_tableauDim_oneBoxChildrenOdd_branching"
      ],
      "deps": [
        "S05_L05",
        "S05_L06"
      ],
      "summary": "Tableau-count dimension recursion for one-box removals.",
      "statement": "Lemma 5.8 proves the one-box tableauDim dimension recursion.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L05"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "one-box removals",
          "target": "S05_D11"
        },
        {
          "text": "One-box deletion intertwining",
          "target": "S05_L06"
        }
      ],
      "paperLabel": "lem:dimension-one-box-recurrence",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every partition $\\lambda\\vdash N$ with $N\\ge2$,\n\\begin{equation}\\label{eq:dimension-one-box-recurrence}\n  d_\\lambda=\\sum_{\\mu\\nearrow\\lambda}d_\\mu .\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_08_tableauDim_oneBoxChildrenOdd_branching",
          "line": 406
        }
      ]
    },
    {
      "id": "S05_L09",
      "label": "Lem 5.9",
      "title": "Sizes of sign-pattern multisets",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_09_SizesOfTheSignPatternMultisets.lean",
      "wrappers": [
        "S05_Lem5_09_tableauDim_twoStrip_size",
        "S05_Lem5_09_tableauDim_oneBox_size"
      ],
      "deps": [
        "S05_D13",
        "S05_D14",
        "S05_L07",
        "S05_L08"
      ],
      "summary": "Tableau-count size identities for sign-pattern multisets.",
      "statement": "Lemma 5.9 proves the size identities for the sign-pattern multisets.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        },
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "One-box dimension recursion",
          "target": "S05_L08"
        }
      ],
      "paperLabel": "lem:X-size",
      "paperEnv": "lemma",
      "paperStatementLatex": "For $\\lambda\\vdash2m$,\n\\begin{equation*}\n  |\\mathsf X_m(\\lambda)|=d_\\lambda .\n\\end{equation*}\nFor $\\lambda\\vdash2m+1$,\n\\begin{equation*}\n  |\\mathsf X_m^{\\mathrm{odd}}(\\lambda)|=d_\\lambda .\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_09_tableauDim_twoStrip_size",
          "line": 89
        },
        {
          "name": "S05_Lem5_09_tableauDim_oneBox_size",
          "line": 109
        }
      ]
    },
    {
      "id": "S05_L10",
      "label": "Lem 5.10",
      "title": "Matching subgroup eigenbasis",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_10_MatchingSubgroupEigenbasis.lean",
      "wrappers": [
        "S05_Lem5_10_matchingSignProjectionEven_isMatchingEigenvector",
        "S05_Lem5_10_matchingSignProjectionOdd_isMatchingEigenvector"
      ],
      "deps": [
        "AppA_01",
        "AppA_02",
        "S05_L01",
        "S05_D15",
        "S05_D16",
        "S05_D17",
        "S05_D18",
        "S05_D19"
      ],
      "summary": "Concrete matching operators and sign projections are proved; the actual eigenbasis and label multiplicities are absent.",
      "statement": "Lemma 5.10 currently proves commuting matching operators, simultaneous sign projections, and character action on any resulting eigenvector. It does not yet prove that these vectors form a basis or that their character multiplicities are the recursive sign-pattern multiset required by the paper statement.",
      "terms": [
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "Matching characters",
          "target": "S05_D15"
        },
        {
          "text": "Even matching eigenvectors",
          "target": "S05_D16"
        },
        {
          "text": "Odd matching eigenvectors",
          "target": "S05_D17"
        },
        {
          "text": "Even restriction scalar input",
          "target": "S05_D18"
        },
        {
          "text": "Odd restriction scalar input",
          "target": "S05_D19"
        },
        {
          "text": "Matching operators",
          "target": "S05_L01"
        }
      ],
      "paperLabel": "lem:matching-restriction-X",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let \\(M\\) be a perfect matching on \\([2m]\\).  For every\n\\(\\lambda\\vdash2m\\), the even matching-restriction input holds for\n\\((M,\\lambda)\\).\n\nLet \\(M\\) be a near-perfect matching on \\([2m+1]\\) with \\(m\\) edges.  For\nevery \\(\\lambda\\vdash2m+1\\), the odd matching-restriction input holds for\n\\((M,\\lambda)\\).",
      "leanLinks": [
        {
          "name": "S05_Lem5_10_matchingSignProjectionEven_isMatchingEigenvector",
          "line": 362
        },
        {
          "name": "S05_Lem5_10_matchingSignProjectionOdd_isMatchingEigenvector",
          "line": 370
        }
      ]
    },
    {
      "id": "S05_L11",
      "label": "Lem 5.11",
      "title": "Local truncation on a matching character",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_11_LocalTruncationOnAMatchingCharacter.lean",
      "wrappers": [
        "S05_Lem5_11_matchingLocalProjection_preserves_low_matchingCharacter",
        "S05_Lem5_11_matchingLocalProjection_kills_high_matchingCharacter"
      ],
      "deps": [
        "S05_D15"
      ],
      "summary": "Matching-character local truncation calculation.",
      "statement": "Lemma 5.11 proves local truncation on a matching character.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D15"
        }
      ],
      "paperLabel": "lem:PM-character-projection",
      "paperEnv": "lemma",
      "paperStatementLatex": "Fix a matching $M$ with $m$ edges.  On a right coset $C=\\rho_C A_M$, write\n\\begin{equation}\\label{eq:local-character-expansion-general}\n  F(\\rho_C\\tau_x)=\\sum_{R\\subseteq[m]} a_R(C)\\chi_R(\\tau_x).\n\\end{equation}\nThen\n\\begin{equation}\\label{eq:PM-keeps-small-characters}\n  (P_MF)(\\rho_C\\tau_x)=\\sum_{|R|\\le1}a_R(C)\\chi_R(\\tau_x).\n\\end{equation}\nIn particular, if $F(\\omega\\tau_x)=\\chi_T(\\tau_x)F(\\omega)$ for all $\\omega$ and\n$x$, then\n\\begin{equation*}\n  P_MF=\n  \\begin{cases}\n    F,& |T|\\le1,\\\\\n    0,& |T|\\ge2.\n  \\end{cases}\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_11_matchingLocalProjection_preserves_low_matchingCharacter",
          "line": 121
        },
        {
          "name": "S05_Lem5_11_matchingLocalProjection_kills_high_matchingCharacter",
          "line": 133
        }
      ]
    },
    {
      "id": "S05_L12",
      "label": "Lem 5.12",
      "title": "Trace of one local truncation",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
      "wrappers": [
        "S05_Lem5_12_fixedMatching_tableauTrace_even_of_eigenbasis",
        "S05_Lem5_12_fixedMatching_tableauTrace_odd_of_eigenbasis",
        "S05_Lem5_12_fixedMatching_youngBlockTrace_even_of_eigenbasis",
        "S05_Lem5_12_fixedMatching_youngBlockTrace_odd_of_eigenbasis",
        "traceLocalTruncation_even_from_restriction",
        "traceLocalTruncation_odd_from_restriction"
      ],
      "deps": [
        "S05_L10",
        "S05_L11",
        "S05_D20",
        "S05_D21"
      ],
      "summary": "The actual fixed tableau and full Young-block traces are proved from the paper's labeled matching-eigenbasis hypothesis.",
      "statement": "Lemma 5.12 uses basis-invariance of trace and the proved 0/1 action of the concrete high-matching operator. From the explicitly supplied matching eigenbasis and its high-label count, it proves the even and odd tableau-space traces and the full-block formulas with the tableau-dimension factor. Lemma 5.10 must still construct that labeled eigenbasis for the application.",
      "terms": [
        {
          "text": "Matching subgroup eigenbasis",
          "target": "S05_L10"
        },
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L11"
        },
        {
          "text": "Even trace input",
          "target": "S05_D20"
        },
        {
          "text": "Odd trace input",
          "target": "S05_D21"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ],
      "paperLabel": "lem:PM-trace-young-block",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $M$ be a perfect matching on $[2m]$ and let $\\lambda\\vdash2m$.  Suppose\n$v_1,\\ldots,v_{d_\\lambda}$ is an orthonormal basis of $V^\\lambda$ and\n$R_1,\\ldots,R_{d_\\lambda}$ is a listing of $\\mathsf X_m(\\lambda)$ satisfying\n\\begin{equation*}\n  \\rho^\\lambda(\\tau_x)v_a=\\chi_{R_a}(\\tau_x)v_a\n  \\qquad(\\tau_x\\in A_M).\n\\end{equation*}\nThen\n\\begin{equation}\\label{eq:trace-one-PM-even}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m(\\lambda).\n\\end{equation}\nSimilarly, if $M$ is a near-perfect matching on $[2m+1]$, $\\lambda\\vdash2m+1$,\nand the corresponding basis is listed by\n$\\mathsf X_m^{\\mathrm{odd}}(\\lambda)$, then\n\\begin{equation}\\label{eq:trace-one-PM-odd}\n  \\operatorname{tr}\\bigl((I-P_M)|_{\\mathcal H_\\lambda}\\bigr)\n  =d_\\lambda h_m^{\\mathrm{odd}}(\\lambda).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_12_fixedMatching_tableauTrace_even_of_eigenbasis",
          "line": 72
        },
        {
          "name": "S05_Lem5_12_fixedMatching_tableauTrace_odd_of_eigenbasis",
          "line": 97
        },
        {
          "name": "S05_Lem5_12_fixedMatching_youngBlockTrace_even_of_eigenbasis",
          "line": 121
        },
        {
          "name": "S05_Lem5_12_fixedMatching_youngBlockTrace_odd_of_eigenbasis",
          "line": 145
        },
        {
          "name": "traceLocalTruncation_even_from_restriction",
          "line": 72
        },
        {
          "name": "traceLocalTruncation_odd_from_restriction",
          "line": 80
        }
      ]
    },
    {
      "id": "S05_L13",
      "label": "Lem 5.13",
      "title": "Local truncation as convolution",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_13_LocalTruncationAsConvolution.lean",
      "wrappers": [
        "S05_Lem5_13_local_truncation_as_convolution"
      ],
      "deps": [
        "S05_L11",
        "S05_D22"
      ],
      "summary": "Local projection as low convolution and residual as high convolution.",
      "statement": "Lemma 5.13 proves local truncation as low/high convolution.",
      "terms": [
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L11"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D22"
        }
      ],
      "paperLabel": "lem:PM-convolution",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every matching $M$,\n\\begin{equation*}\n  P_M=C_{p_M},\n  \\qquad\n  I-P_M=C_{q_M}.\n\\end{equation*}\nMoreover $p_M$ and $q_M$ are complementary idempotents:\n\\begin{equation*}\n  p_M^2=p_M,\n  \\qquad q_M^2=q_M,\n  \\qquad p_Mq_M=q_Mp_M=0,\n  \\qquad p_M+q_M=1.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_13_local_truncation_as_convolution",
          "line": 25
        }
      ]
    },
    {
      "id": "S05_L14",
      "label": "Lem 5.14",
      "title": "Central averaged rejection",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_14_CentralAveragedRejection.lean",
      "wrappers": [
        "S05_Lem5_14_matchingMeanProjectionError_eq_high_idempotent_average"
      ],
      "deps": [
        "S05_L13",
        "S05_D22"
      ],
      "summary": "Finite-average identity is proved; centrality on Young blocks is representation input.",
      "statement": "Lemma 5.14 proves the finite averaged-rejection identity, with centrality supplied by the spectral model boundary.",
      "terms": [
        {
          "text": "Local truncation as convolution",
          "target": "S05_L13"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D22"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ],
      "paperLabel": "lem:averaged-rejection-central",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $q:=\\E_M q_M$, with $M$ uniform over perfect matchings if $n$ is even and\nover near-perfect matchings if $n$ is odd.  Then $q$ is central in\n$\\mathbb C[S_n]$, and\n\\begin{equation*}\n  \\cA=C_q.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_14_matchingMeanProjectionError_eq_high_idempotent_average",
          "line": 60
        }
      ]
    },
    {
      "id": "S05_L15",
      "label": "Lem 5.15",
      "title": "Young-basis scalar commutant",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_15_YoungBasisScalarCommutant.lean",
      "wrappers": [
        "YoungModelOperatorCommutationData",
        "S05_Lem5_15_youngModelOperator_scalar_on_basis",
        "S05_Lem5_15_matchingAverageScalarity_eq_sum"
      ],
      "deps": [
        "S05_L14",
        "S05_D23",
        "AppA_04"
      ],
      "summary": "Generic Young-model scalar commutant theorem, plus the old scalarity-input projection.",
      "statement": "Lemma 5.15 proves that a linear operator on one tableau block commuting with all diagonal content operators and adjacent Young operators is scalar on the tableau basis, assuming A.4 connectedness. The averaged matching-rejection instantiation remains the scalarity bridge input.",
      "terms": [
        {
          "text": "Central averaged rejection",
          "target": "S05_L14"
        },
        {
          "text": "Young-basis scalar commutant input",
          "target": "S05_D23"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "AppA_04"
        },
        {
          "text": "scalar commutant",
          "target": "S05_D23"
        }
      ],
      "paperLabel": "lem:young-basis-scalar-commutant",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $B\\in\\End(V^\\lambda)$.  Suppose that $B$ commutes with every diagonal\ncontent operator $C_k^\\lambda$ and with every adjacent tableau operator\n$S_i^\\lambda$.  Then\n\\begin{equation*}\n  B=\\frac{\\operatorname{tr}B}{d_\\lambda}I.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_15_matchingAverageScalarity_eq_sum",
          "line": 158
        },
        {
          "name": "YoungModelOperatorCommutationData",
          "line": 30
        },
        {
          "name": "S05_Lem5_15_youngModelOperator_scalar_on_basis",
          "line": 145
        }
      ]
    },
    {
      "id": "S05_L16",
      "label": "Lem 5.16",
      "title": "Block scalar of averaged rejection",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_16_BlockScalarOfTheAveragedRejection.lean",
      "wrappers": [
        "S05_matchingAverageScalarity_from_young_model_input",
        "S05_Lem5_16_scalar_eq_trace_div_dimension",
        "S05_Lem5_16_even_scalar_eq_hEven_div_dim"
      ],
      "deps": [
        "AppA_02",
        "AppA_04",
        "S05_L12",
        "S05_L15"
      ],
      "summary": "Section 5 scalarity bridge input plus trace-divided-by-dimension algebra.",
      "statement": "Lemma 5.16 isolates matching-average scalarity as a Section 5 input and proves the trace-divided-by-dimension algebra.",
      "terms": [
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "AppA_02"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "AppA_04"
        },
        {
          "text": "Trace of one local truncation",
          "target": "S05_L12"
        },
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L15"
        }
      ],
      "paperLabel": "lem:centralization-matchings",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $\\cA=\\E_M(I-P_M)$.  On $\\mathcal H_\\lambda$, the operator $\\cA$ acts as the\nscalar\n\\begin{equation}\\label{eq:A-eigenvalue-even}\n  \\frac{h_m(\\lambda)}{d_\\lambda}\n  \\qquad(n=2m),\n\\end{equation}\nand as the scalar\n\\begin{equation}\\label{eq:A-eigenvalue-odd}\n  \\frac{h_m^{\\mathrm{odd}}(\\lambda)}{d_\\lambda}\n  \\qquad(n=2m+1).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_matchingAverageScalarity_from_young_model_input",
          "line": 52
        },
        {
          "name": "S05_Lem5_16_scalar_eq_trace_div_dimension",
          "line": 126
        },
        {
          "name": "S05_Lem5_16_even_scalar_eq_hEven_div_dim",
          "line": 133
        }
      ]
    },
    {
      "id": "S05_L16A",
      "label": "Lem 5.16a",
      "title": "Averaged rejection Young operator",
      "section": "Spectral bridge",
      "kind": "internal",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Lem5_16a_AveragedRejectionYoungOperator.lean",
      "wrappers": [
        "AveragedRejectionYoungOperatorData",
        "averagedRejectionYoungOperator_commutes_adjacent",
        "averagedRejectionYoungOperator_commutes_content",
        "averagedRejectionYoungOperator_scalar_on_basis"
      ],
      "deps": [
        "S05_L15"
      ],
      "summary": "One-block operator interface for the averaged rejection operator.",
      "statement": "Lemma 5.16a names the operator data needed to instantiate the generic scalar commutant theorem: a one-block operator, linearity, and commutation with adjacent and diagonal content operators. It does not construct rho_lambda(q).",
      "terms": [
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L15"
        },
        {
          "text": "adjacent Young operators",
          "target": "S05_L15"
        },
        {
          "text": "diagonal content operators",
          "target": "S05_L15"
        }
      ],
      "paperLabel": "lem:averaged-rejection-young-operator-interface",
      "paperEnv": "interface",
      "paperStatementLatex": "Let \\(B_\\lambda:V^\\lambda\\to V^\\lambda\\) be the operator that should represent\n\\(\\rho^\\lambda(q)\\), where \\(q=\\mathbb E_M q_M\\) is the averaged high matching\nidempotent.  The interface records linearity and the commutation relations\n\\(B_\\lambda S_i^\\lambda=S_i^\\lambda B_\\lambda\\) and\n\\(B_\\lambda C_k^\\lambda=C_k^\\lambda B_\\lambda\\).",
      "leanLinks": [
        {
          "name": "AveragedRejectionYoungOperatorData",
          "line": 29
        },
        {
          "name": "averagedRejectionYoungOperator_commutes_adjacent",
          "line": 61
        },
        {
          "name": "averagedRejectionYoungOperator_commutes_content",
          "line": 71
        },
        {
          "name": "averagedRejectionYoungOperator_scalar_on_basis",
          "line": 82
        }
      ]
    },
    {
      "id": "S05_L17",
      "label": "Lem 5.17",
      "title": "Block lower bound implies the gap",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_17_BlockLowerBoundImpliesTheGap.lean",
      "wrappers": [
        "S05_Lem5_17_spectralGapFromBlockModelWithDim"
      ],
      "deps": [
        "S05_D07",
        "S05_D08",
        "S05_L16"
      ],
      "summary": "Weighted-sum spectral-gap algebra from block scalar lower bounds.",
      "statement": "Lemma 5.17 proves that a block lower bound implies the global spectral gap.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D08"
        },
        {
          "text": "Block scalar of averaged rejection",
          "target": "S05_L16"
        }
      ],
      "paperLabel": "lem:block-lower-bound-gap",
      "paperEnv": "lemma",
      "paperStatementLatex": "Assume that $\\cA$ acts on each $\\mathcal H_\\lambda$ by a scalar $\\theta_\\lambda$\nand that\n\\begin{equation*}\n  \\theta_\\lambda\\ge c\n  \\qquad\n  \\text{for all }\\lambda\\notin\\{(n),(n-1,1)\\}.\n\\end{equation*}\nThen\n\\begin{equation*}\n  \\ip{f}{\\cA f}\\ge c\\norm{f-P_{U_1}f}^2\n  \\qquad(f:S_n\\to\\mathbb R).\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_17_spectralGapFromBlockModelWithDim",
          "line": 148
        }
      ]
    },
    {
      "id": "S05_L18",
      "label": "Lem 5.18",
      "title": "Regular Young-block decomposition",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_18_RegularYoungBlockDecomposition.lean",
      "wrappers": [
        "spectralBlockModelInputWithDim_even_from_appendixA",
        "spectralBlockModelInputWithDim_odd_from_appendixA"
      ],
      "deps": [
        "S05_D07",
        "S05_D08",
        "AppA_01",
        "AppA_02",
        "AppA_03",
        "AppA_04",
        "S05_L16",
        "S05_L02"
      ],
      "summary": "Assembles Appendix A markers plus the Section 5 scalarity input into the dimension-parameterized spectral-block model.",
      "statement": "Lemma 5.18 assembles Appendix A ingredients and the Section 5 scalarity bridge into the regular Young-block spectral model.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D08"
        },
        {
          "text": "Young orthogonal realization",
          "target": "AppA_01"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "AppA_02"
        },
        {
          "text": "Degree-one Young-block identification",
          "target": "AppA_03"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "AppA_04"
        },
        {
          "text": "matching-average scalarity bridge",
          "target": "S05_L16"
        },
        {
          "text": "Diagonal content eigenspaces",
          "target": "S05_L02"
        }
      ],
      "paperLabel": "lem:regular-young-block-decomposition",
      "paperEnv": "lemma",
      "paperStatementLatex": "Over $\\mathbb C$, the Specht modules $S^\\lambda$, $\\lambda\\vdash n$, form a\ncomplete set of irreducible representations of $S_n$.  For each $\\lambda$, let\n$d_\\lambda=\\dim S^\\lambda$ and define the matrix-coefficient space\n\\begin{equation*}\n  \\mathcal H_\\lambda\n  =\\spanop\\{\\pi\\mapsto\\langle e_S,\\rho^\\lambda(\\pi)e_T\\rangle:\n      S,T\\in\\SYT(\\lambda)\\}\\subseteq L^2(S_n;\\mathbb C).\n\\end{equation*}\nThen the spaces $\\mathcal H_\\lambda$ are mutually orthogonal, span\n$L^2(S_n;\\mathbb C)$, and have dimension $d_\\lambda^2$.",
      "leanLinks": [
        {
          "name": "spectralBlockModelInputWithDim_even_from_appendixA",
          "line": 86
        },
        {
          "name": "spectralBlockModelInputWithDim_odd_from_appendixA",
          "line": 133
        }
      ]
    },
    {
      "id": "S05_L19",
      "label": "Lem 5.19",
      "title": "Even spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_19_EvenSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_19_tableauDim_evenSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L17",
        "S05_L18",
        "S05_L24"
      ],
      "summary": "Even algebraic bridge from spectral model plus finite certificate.",
      "statement": "Lemma 5.19 proves the even spectral bridge from the spectral model and finite even certificate.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L17"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L18"
        },
        {
          "text": "Even certificate",
          "target": "S05_L24"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ],
      "paperLabel": "lem:spectral-certificate-even",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $n=2m$.  Suppose that\n\\begin{equation}\\label{eq:even-certificate-condition}\n  h_m(\\lambda)\\ge c d_\\lambda\n\\end{equation}\nfor every $\\lambda\\vdash2m$ other than $(2m)$ and $(2m-1,1)$.  Then\n\\eqref{eq:desired-A-gap} holds with constant $c$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_19_tableauDim_evenSpectralGapFromCertificates",
          "line": 53
        }
      ]
    },
    {
      "id": "S05_L20",
      "label": "Lem 5.20",
      "title": "Odd spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_20_OddSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_20_tableauDim_oddSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L17",
        "S05_L18",
        "S05_L26"
      ],
      "summary": "Odd algebraic bridge from spectral model plus finite certificate.",
      "statement": "Lemma 5.20 proves the odd spectral bridge from the spectral model and finite odd certificate.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L17"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L18"
        },
        {
          "text": "Odd certificate",
          "target": "S05_L26"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ],
      "paperLabel": "lem:spectral-certificate-odd",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $n=2m+1$.  Suppose that\n\\begin{equation}\\label{eq:odd-certificate-condition}\n  h_m^{\\mathrm{odd}}(\\lambda)\\ge c d_\\lambda\n\\end{equation}\nfor every $\\lambda\\vdash2m+1$ other than $(2m+1)$ and $(2m,1)$.  Then\n\\eqref{eq:desired-A-gap} holds with constant $c$.",
      "leanLinks": [
        {
          "name": "S05_Lem5_20_tableauDim_oddSpectralGapFromCertificates",
          "line": 53
        }
      ]
    },
    {
      "id": "S05_L21",
      "label": "Lem 5.21",
      "title": "Counting one more matching edge",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_21_CountingOneMoreMatchingEdge.lean",
      "wrappers": [
        "S05_Lem5_21_counting_one_more_matching_edge"
      ],
      "deps": [
        "S05_D13",
        "S05_D14"
      ],
      "summary": "Finite recurrence for zero/high sign-pattern counts.",
      "statement": "Lemma 5.21 proves the counting-one-more-matching-edge recurrence.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        }
      ],
      "paperLabel": "lem:counting-one-more-matching-edge",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $\\lambda\\vdash2m$,\n\\begin{equation}\\label{eq:z-recurrence}\n  z_m(\\lambda)\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}z_{m-1}(\\mu),\n\\end{equation}\nand\n\\begin{equation}\\label{eq:h-recurrence}\n  h_m(\\lambda)\n  =\\sum_{\\mu\\in\\mathsf H_2(\\lambda)}h_{m-1}(\\mu)\n   +\\sum_{\\mu\\in\\mathsf V_2(\\lambda)}\n      \\bigl(d_\\mu-z_{m-1}(\\mu)\\bigr).\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_21_counting_one_more_matching_edge",
          "line": 43
        }
      ]
    },
    {
      "id": "S05_L22",
      "label": "Lem 5.22",
      "title": "Weight-zero entries are never a majority",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_22_WeightZeroEntriesAreNeverAMajority.lean",
      "wrappers": [
        "S05_Lem5_22_tableau_weightZeroEntries_never_majority"
      ],
      "deps": [
        "S05_L07",
        "S05_L21",
        "S05_D26",
        "S05_D27"
      ],
      "summary": "Tableau-count z-bound certificate.",
      "statement": "Lemma 5.22 proves that weight-zero entries are never a majority.",
      "terms": [
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L21"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D26"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D27"
        }
      ],
      "paperLabel": "lem:z-bound-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "If $\\lambda\\vdash2m$ and $\\lambda\\neq(2m)$, then\n\\begin{equation*}\n  z_m(\\lambda)\\le\\frac12d_\\lambda.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_22_tableau_weightZeroEntries_never_majority",
          "line": 2687
        }
      ]
    },
    {
      "id": "S05_L23",
      "label": "Lem 5.23",
      "title": "Where the induction can fail",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_23_WhereTheInductionCanFail.lean",
      "wrappers": [
        "S05_Lem5_23_where_the_induction_can_fail"
      ],
      "deps": [
        "S05_L22",
        "S05_D27"
      ],
      "summary": "Exceptional-shape localization for the even induction.",
      "statement": "Lemma 5.23 identifies where the even certificate induction can fail.",
      "terms": [
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L22"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D27"
        }
      ],
      "paperLabel": "lem:exceptional-even-children",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $m\\ge3$, and let $\\lambda\\vdash 2m$ be neither $(2m)$ nor $(2m-1,1)$.\nSuppose that at least one of the following three events occurs:\n\\begin{enumerate}\n  \\item the one-row diagram $(2m-2)$ lies in $\\mathsf H_2(\\lambda)$;\n  \\item the one-row diagram $(2m-2)$ lies in $\\mathsf V_2(\\lambda)$;\n  \\item the standard diagram $(2m-3,1)$ lies in $\\mathsf H_2(\\lambda)$.\n\\end{enumerate}\nThen\n\\begin{equation}\\label{eq:exceptional-even-shapes}\n  \\lambda\\in\\{(2m-2,2),(2m-2,1,1),(2m-3,3),(2m-3,2,1)\\}.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_23_where_the_induction_can_fail",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_L24",
      "label": "Lem 5.24",
      "title": "Even certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_24_EvenCertificate.lean",
      "wrappers": [
        "S05_Lem5_24_tableau_even_certificate"
      ],
      "deps": [
        "S05_D24",
        "S05_D26",
        "S05_D27",
        "S05_L07",
        "S05_L21",
        "S05_L22",
        "S05_L23",
        "S05_L09"
      ],
      "summary": "Finite even h-bound certificate.",
      "statement": "Lemma 5.24 proves the even finite certificate.",
      "terms": [
        {
          "text": "Tableau even height",
          "target": "S05_D24"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D26"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D27"
        },
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L21"
        },
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L22"
        },
        {
          "text": "Where the induction can fail",
          "target": "S05_L23"
        },
        {
          "text": "Sign-pattern multiset sizes",
          "target": "S05_L09"
        }
      ],
      "paperLabel": "lem:h-even-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $m\\ge2$ and every partition $\\lambda\\vdash2m$ other than $(2m)$ and\n$(2m-1,1)$,\n\\begin{equation}\\label{eq:even-h-fifth}\n  h_m(\\lambda)\\ge\\frac15d_\\lambda.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_24_tableau_even_certificate",
          "line": 4713
        }
      ]
    },
    {
      "id": "S05_L25",
      "label": "Lem 5.25",
      "title": "Odd exceptional children",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_25_OddExceptionalChildren.lean",
      "wrappers": [
        "S05_Lem5_25_odd_exceptional_children"
      ],
      "deps": [
        "S05_L24",
        "S05_D27"
      ],
      "summary": "Odd exceptional child analysis.",
      "statement": "Lemma 5.25 proves the odd exceptional-children analysis.",
      "terms": [
        {
          "text": "Even certificate",
          "target": "S05_L24"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D27"
        }
      ],
      "paperLabel": "lem:exceptional-odd-children",
      "paperEnv": "lemma",
      "paperStatementLatex": "Let $m\\ge2$, and let $\\lambda\\vdash 2m+1$ be neither $(2m+1)$ nor $(2m,1)$.\nIf some one-box child $\\mu\\nearrow\\lambda$ is either the one-row diagram $(2m)$\nor the standard diagram $(2m-1,1)$, then\n\\begin{equation}\\label{eq:exceptional-odd-shapes}\n  \\lambda\\in\\{(2m-1,2),(2m-1,1,1)\\}.\n\\end{equation}",
      "leanLinks": [
        {
          "name": "S05_Lem5_25_odd_exceptional_children",
          "line": 23
        }
      ]
    },
    {
      "id": "S05_L26",
      "label": "Lem 5.26",
      "title": "Odd certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_26_OddCertificate.lean",
      "wrappers": [
        "S05_Lem5_26_tableau_odd_certificate"
      ],
      "deps": [
        "S05_D25",
        "S05_D26",
        "S05_D27",
        "S05_L08",
        "S05_L24",
        "S05_L25",
        "S05_L09"
      ],
      "summary": "Finite odd h-bound certificate.",
      "statement": "Lemma 5.26 proves the odd finite certificate.",
      "terms": [
        {
          "text": "Tableau odd height",
          "target": "S05_D25"
        },
        {
          "text": "Certificate special diagrams",
          "target": "S05_D26"
        },
        {
          "text": "Certificate exceptional predicates",
          "target": "S05_D27"
        },
        {
          "text": "One-box dimension recursion",
          "target": "S05_L08"
        },
        {
          "text": "Even certificate",
          "target": "S05_L24"
        },
        {
          "text": "Odd exceptional children",
          "target": "S05_L25"
        },
        {
          "text": "Sign-pattern multiset sizes",
          "target": "S05_L09"
        }
      ],
      "paperLabel": "lem:h-odd-app",
      "paperEnv": "lemma",
      "paperStatementLatex": "For every $m\\ge2$ and every partition $\\lambda\\vdash2m+1$ other than\n$(2m+1)$ and $(2m,1)$,\n\\begin{equation*}\n  h_m^{\\mathrm{odd}}(\\lambda)\\ge\\frac16d_\\lambda.\n\\end{equation*}",
      "leanLinks": [
        {
          "name": "S05_Lem5_26_tableau_odd_certificate",
          "line": 842
        }
      ]
    },
    {
      "id": "Thm1_1",
      "label": "Thm 1.1",
      "title": "Main theorem",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S01_Thm1_01_MainIntro.lean",
      "wrappers": [
        "Thm1_1_MainIntro"
      ],
      "deps": [
        "L4_11"
      ],
      "summary": "Main theorem wrapper, proved from one-trial soundness.",
      "statement": "Thm 1.1: Main theorem wrapper, proved from one-trial soundness.",
      "terms": [
        {
          "text": "One-trial soundness",
          "target": "L4_11"
        }
      ],
      "paperLabel": "thm:main-intro",
      "paperEnv": "theorem",
      "paperStatementLatex": "There is a nonadaptive one-sided oracle tester which, given\n$f:S_n\\to\\{0,1\\}$ and $0<\\epsilon<1$, accepts every $f\\in\\mathcal D$ and rejects\nevery $f$ with $\\dist(f,\\mathcal D)\\ge\\epsilon$ with probability at least $2/3$.\nThe tester uses $O(\\epsilon^{-2})$ queries.",
      "leanLinks": [
        {
          "name": "Thm1_1_MainIntro",
          "line": 56
        }
      ]
    },
    {
      "id": "Thm2_1",
      "label": "Thm 2.1",
      "title": "Boolean U1 classification",
      "section": "External inputs",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean",
      "wrappers": [
        "Thm2_1_BooleanU1",
        "booleanU1_dictator_classification_input"
      ],
      "deps": [],
      "summary": "External structural classification for Boolean degree-one functions.",
      "statement": "Thm 2.1: External structural classification for Boolean degree-one functions.",
      "terms": [
        {
          "text": "U1",
          "target": "S05_D08"
        }
      ],
      "paperLabel": "thm:boolean-u1",
      "paperEnv": "theorem",
      "paperStatementLatex": "If $f:S_n\\to\\{0,1\\}$ lies in $U_1$, then $f\\in\\D$.  Conversely, every\n$f\\in\\D$ lies in $U_1$.",
      "leanLinks": [
        {
          "name": "Thm2_1_BooleanU1",
          "line": 163
        },
        {
          "name": "booleanU1_dictator_classification_input",
          "line": 156
        }
      ]
    },
    {
      "id": "Thm2_2",
      "label": "Thm 2.2",
      "title": "FKN/stability input",
      "section": "External inputs",
      "kind": "external",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean",
      "wrappers": [
        "Thm2_2_FKNInput",
        "fknStability_input"
      ],
      "deps": [],
      "summary": "External Filmus stability theorem in the distance-to-dictators form.",
      "statement": "Thm 2.2: External Filmus stability theorem in the distance-to-dictators form.",
      "terms": [],
      "paperLabel": "thm:fkn-input",
      "paperEnv": "theorem",
      "paperStatementLatex": "There is an absolute constant $c_{\\mathrm{FKN}}>0$ such that every Boolean\n$f:S_n\\to\\{0,1\\}$ satisfies\n\\[\n  \\norm{f-P_{U_1}f}^2\n  \\ge c_{\\mathrm{FKN}}\\,\\dist(f,\\D)^2.\n\\]",
      "leanLinks": [
        {
          "name": "Thm2_2_FKNInput",
          "line": 40
        },
        {
          "name": "fknStability_input",
          "line": 32
        }
      ]
    },
    {
      "id": "Thm4_8",
      "label": "Thm 4.8",
      "title": "Matching-cube spectral gap",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Thm4_08_MatchingGap.lean",
      "wrappers": [
        "Thm4_10_MatchingGap"
      ],
      "deps": [
        "S05_L19",
        "S05_L20"
      ],
      "summary": "The active proof uses the tableauDim spectral bridges and Appendix A spectral-model inputs.",
      "statement": "Thm 4.8: The active proof uses the tableauDim spectral bridges and Appendix A spectral-model inputs.",
      "terms": [
        {
          "text": "Even spectral bridge",
          "target": "S05_L19"
        },
        {
          "text": "Odd spectral bridge",
          "target": "S05_L20"
        },
        {
          "text": "even spectral bridge",
          "target": "S05_L19"
        },
        {
          "text": "odd spectral bridge",
          "target": "S05_L20"
        },
        {
          "text": "Appendix A spectral-model inputs",
          "target": "S05_L18"
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
          "name": "Thm4_10_MatchingGap",
          "line": 40
        }
      ]
    }
  ]
};

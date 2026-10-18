# Related literature for current results

This bibliography connects the current result guides to the 19 references in
the user-supplied survey. Entries describe subject relationships, not a claim
that a paper proves a Lean declaration or that this project subsumes its scope.
The [reference review](REFERENCE_REVIEW.md) distinguishes bibliographic checks
from external theorem premises. No new external premise is admitted here.

## General coefficient spaces and symmetry

| Source | Relevant subject and citation role | Repository entry point |
| --- | --- | --- |
| **G1.** H.-L. Li, Z. Ren, M.-L. Xiao, J.-H. Yu, Y.-H. Zheng, *Operators For Generic Effective Field Theory at any Dimension: On-shell Amplitude Basis Construction*, JHEP 04 (2022) 140, [2201.04639v2](https://arxiv.org/abs/2201.04639v2) | Explicit Lorentz/gauge/flavor bases with repeated-field permutation structure. Related construction; its on-shell/amplitude and basis-conversion framework is not identified with the general residual-Hom equivalence. | [General theorems](current/GENERAL_THEOREMS.md); [selected Li comparisons](../verification/li-basis-coverage.md) |
| **G2.** B. Henning, X. Lu, T. Melia, H. Murayama, *Operator bases, S-matrices, and their partition functions*, JHEP 10 (2017) 199, [1706.08520v1](https://arxiv.org/abs/1706.08520v1) | Hilbert-series and operator-space framework that handles EOM/IBP redundancy. Related methods with a different quotient domain. | [Coefficient decomposition](current/core/Math/GRADED_OPERATOR_COMPLETENESS.md) |
| **G3.** L. Lehman, A. Martin, *Hilbert Series for Constructing Lagrangians: expanding the phenomenologist's toolbox*, Phys. Rev. D 91 (2015) 105014, [1503.07537](https://arxiv.org/abs/1503.07537) | Invariant counting, including non-derivative examples. Counting context, not a supplied multiplicity or completeness premise. | [General theorems](current/GENERAL_THEOREMS.md) |
| **G4.** B. Grinstein, X. Lu, C. Miró, P. Quílez, *Accidental symmetries, Hilbert series, and friends*, JHEP 03 (2025) 172, [2412.05359v1](https://arxiv.org/abs/2412.05359v1) | All-order non-derivative accidental symmetry and friendship. The published bosonic criterion's fermionic caveat matters; no friendship-to-Lean equivalence is certified. | [Symmetry criterion](current/core/Math/ALL_DEGREE_SYMMETRY_PROTECTION.md); [inspected locations and limitations](../topics/all-degree-symmetry-protection/references.md#r1--all-order-accidental-symmetries) |
| **G5.** R. V. Harlander, M. C. Schaaf, *AutoEFT: Automated operator construction for effective field theories*, Comput. Phys. Commun. 300 (2024) 109198, [2309.15783v2](https://arxiv.org/abs/2309.15783v2) | Automated operator construction for supported fields/groups. Software-related work; no installation, execution, output comparison or formal certification of AutoEFT. | [General theorems](current/GENERAL_THEOREMS.md) |

## Charges, minimum dimensions and model-input constraints

| Source | Relevant subject and citation role | Repository entry point |
| --- | --- | --- |
| **C1.** A. Kobach, *Baryon Number, Lepton Number, and Operator Dimension in the Standard Model*, Phys. Lett. B 758 (2016) 455–457, [1604.05726v1](https://arxiv.org/abs/1604.05726v1) | Dimension/B/L parity constraints. Comparison context; no signed-charge/grade semantic bridge is certified by this bibliography. | [Degree bounds](current/applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md) |
| **C2.** A. Helset, A. Kobach, *Baryon number, lepton number, and operator dimension in the SMEFT with flavor symmetries*, Phys. Lett. B 800 (2020) 135132, [1909.05853v1](https://arxiv.org/abs/1909.05853v1) | Flavor-dependent suppression and dimension-nine leading B/L violation for specified flavor assumptions. Those inputs differ from the scalar-cyclic q/l dictionary. | [Decidable classifications](current/DECIDABLE_CLASSIFICATIONS.md) |
| **C3.** S. Koren, *A Note on Proton Stability in the Standard Model*, Universe 8 (2022) 308, [2204.01741v2](https://arxiv.org/abs/2204.01741v2) | B/L residual symmetry context. Existing algebraic consumers do not certify the paper's full quantum/nonperturbative physical conclusion. | [Koren model input](../topics/koren-sm-selection/README.md); [source-to-result coverage](../verification/proton-protection-model-coverage.md) |
| **C4.** H. K. Dreiner, C. Luhn, M. Thormeier, *What is the Discrete Gauge Symmetry of the MSSM?*, Phys. Rev. D 73 (2006) 075007, [hep-ph/0512163v1](https://arxiv.org/abs/hep-ph/0512163v1) | MSSM discrete-symmetry classification context. Component-field restrictions retain their own Higgs/action dictionary; no anomaly-free MSSM/UV realization is inferred. | [Discrete protection study](../model-studies/discrete-baryon-protection/README.md) |
| **C5.** S. Weinberg, *Baryon- and Lepton-Nonconserving Processes*, Phys. Rev. Lett. 43 (1979) 1566, [publisher record](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.43.1566) | Historical B/L-violation context. No paper-wide operator-list or decay-observable comparison is added. | [Selected sectors](current/DECIDABLE_CLASSIFICATIONS.md#selected-coefficient-sectors) |
| **C6.** S. Rao, R. E. Shrock, *Six-fermion (B−L)-violating operators of arbitrary generational structure*, Nucl. Phys. B 232 (1984) 143–179, [publication DOI](https://doi.org/10.1016/0550-3213%2884%2990365-1) | Earlier six-fermion/generation-structure classification. Historical context, not the source of the Li printed seeds or an assumed six-quark basis. | [Six-quark certificate](current/applications/Physics/LI_SIX_QUARK_BASIS.md) |

## Bounded operator sectors

| Source | Relevant subject and citation role | Repository entry point |
| --- | --- | --- |
| **S1.** B. Grzadkowski, M. Iskrzyński, M. Misiak, J. Rosiek, *Dimension-Six Terms in the Standard Model Lagrangian*, JHEP 10 (2010) 085, [1008.4884v3](https://arxiv.org/abs/1008.4884v3) | Warsaw-basis context including four baryon-violating structures. No whole-Warsaw-basis or EOM/IBP comparison is certified here. | [Selected sectors](current/DECIDABLE_CLASSIFICATIONS.md#selected-coefficient-sectors) |
| **S2.** L. Lehman, *Extending the Standard Model Effective Field Theory with the Complete Set of Dimension-7 Operators*, Phys. Rev. D 90 (2014) 125023, [1410.4193v2](https://arxiv.org/abs/1410.4193v2) | Dimension-seven operator-list context. Read alongside the subsequent redundancy discussion below, not as the final imported basis count. | [Bound-seven coefficient theorem](current/applications/Physics/BNV_SEVEN_COMPLETENESS.md) |
| **S3.** Y. Liao, X.-D. Ma, *Renormalization group evolution of dimension-seven baryon- and lepton-number-violating operators*, JHEP 11 (2016) 043, [1607.07309v2](https://arxiv.org/abs/1607.07309v2) | Basis redundancy removal uses EOM/Fierz identities; the paper also computes RGE. Those quotient/RGE results are outside the derivative-free coefficient theorem. | [Bound-seven coefficient theorem](current/applications/Physics/BNV_SEVEN_COMPLETENESS.md) |
| **S4.** H.-L. Li et al., *Complete Set of Dimension-9 Operators in the Standard Model Effective Field Theory*, Phys. Rev. D 104 (2021) 015025, [2007.07899v1](https://arxiv.org/abs/2007.07899v1) | Actual printed-candidate source for the existing selected six-quark comparison; its extension/flavor boundaries remain explicit. Distinct from G1. | [Six-quark certificate](current/applications/Physics/LI_SIX_QUARK_BASIS.md); [Li coverage](../verification/li-basis-coverage.md) |
| **S5.** J. Heeck, B. B. Le, *Basis for non-derivative baryon-number-violating operators*, [2604.25134v2](https://arxiv.org/abs/2604.25134v2) | Existing literal comparisons in selected four-fermion and six-quark sectors. The paper's higher-dimensional scope is not covered wholesale. | [Heeck–Le dossier](current/applications/Physics/HEECK_LE_BASIS.md); [coverage](../verification/heeck-le-coverage.md) |

## Mathematical background and conceptual analogies

| Source | Appropriate use and limit | Repository entry point |
| --- | --- | --- |
| **M1.** S. Mac Lane, *Categories for the Working Mathematician*, second edition (1998), [publisher](https://link.springer.com/book/10.1007/978-1-4757-4721-8) | Background on universal constructions, adjoints and natural transformations. Not an attribution of the project's particular quotient/Hom theorem to this book. | [Coefficient decomposition](current/core/Math/GRADED_OPERATOR_COMPLETENESS.md) |
| **M2.** W. Fulton, J. Harris, *Representation Theory: A First Course* (1991), [publisher](https://link.springer.com/book/10.1007/978-1-4612-0979-9) | Background on symmetric-group representations and Weyl's construction, relevant to tensor statistics. It does not supply the arbitrary-group theorem as an external premise. | [General theorems](current/GENERAL_THEOREMS.md) |
| **M3.** A. Joyal, *Une théorie combinatoire des séries formelles*, Adv. Math. 42 (1981) 1–82, [publisher](https://www.sciencedirect.com/science/article/pii/0001870881900529) | Optional conceptual analogy for labelled structures and permutation organization. A field-species alphabet here is not itself a formalized Joyal species functor; no species-theoretic equivalence is claimed. | [General theorems](current/GENERAL_THEOREMS.md) |

## Findings from actual literature comparisons

The [scoped findings summary](../verification/literature-findings.md) collects
three comparisons with explicit mathematical consequences and limitations.
It separates printed-span applicability, fixed-reading normalization and
conditional coefficient matching. Dutka–Gargalionis and Dev–Mohapatra are
additional comparison sources, outside this page's 19-reference survey table.
The summary is not a claim of three unconditional paper errors.

## Inspection limits

Primary article records/abstracts and publisher contents establish bibliographic
identity and broad subjects. Books are linked using the publisher's second-edition
or original-print information rather than eBook upload years. For G4 the
[published full text](https://escholarship.org/content/qt1t19h386/qt1t19h386_noSplash_993f2e81391bf4798f8679692cb42df3.pdf)
confirms the caveat after Eq. (4.24); the existing topic register owns that audit.
For C6 only publisher metadata/abstract information was available in this pass;
full text was not inspected. C5 is likewise publisher-record/abstract context.
No theorem-by-theorem comparison of these newly linked sources is claimed.

Existing [coverage ledgers](../verification/README.md) own only their actual
bounded source-to-formal-result comparisons. These references create neither
new coverage rows nor proof obligations to implement derivatives, EOM/IBP,
software, quantum anomalies or RGE. This is not an exhaustive prior-art search
and supports no priority or novelty claim.

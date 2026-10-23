# Related literature for current results

This bibliography connects current result guides to the user-supplied
survey references and subsequent topic investigations. Entries describe subject relationships, not a claim
that a paper proves a Lean declaration or that this project subsumes its scope.
The [reference review](REFERENCE_REVIEW.md) distinguishes bibliographic checks
from external theorem premises. No new external premise is admitted here.

## General coefficient spaces and symmetry

| Source | Relevant subject and citation role | Repository entry point |
| --- | --- | --- |
| **G1.** H.-L. Li, Z. Ren, M.-L. Xiao, J.-H. Yu, Y.-H. Zheng, *Operators For Generic Effective Field Theory at any Dimension: On-shell Amplitude Basis Construction*, JHEP 04 (2022) 140, [2201.04639v2](https://arxiv.org/abs/2201.04639v2) | Explicit Lorentz/gauge/flavor bases with repeated-field permutation structure. Related construction; its on-shell/amplitude and basis-conversion framework is not identified with the general residual-Hom equivalence. | [General theorems](current/GENERAL_THEOREMS.md); [selected Li comparisons](../verification/li-basis-coverage.md) |
| **G2.** B. Henning, X. Lu, T. Melia, H. Murayama, *Operator bases, S-matrices, and their partition functions*, JHEP 10 (2017) 199, [1706.08520v1](https://arxiv.org/abs/1706.08520v1) | EOM/IBP framework and bounded scalar comparison guidance. Independent Lean proofs give native four-field coefficient counts through derivative order 4, including the complete K-squared coefficient line. No arbitrary-order Hilbert-series, Euclidean/Lorentz or amplitude equivalence is imported. | [Coefficient decomposition](current/core/Math/GRADED_OPERATOR_COMPLETENESS.md); [inspected locations](../topics/derivative-ibp/references.md#r2--two-descriptions-of-derivative-operators); [order-four result](../topics/scalar-quartic-four-completeness/results.md) |
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

## SU(6) model-construction boundary

| Source | Role and limits | Repository entry point |
| --- | --- | --- |
| A. Angelescu, A. Bally, S. Blasi, F. Goertz, *Minimal SU(6) Gauge-Higgs Grand Unification*, Phys. Rev. D 105 (2022) 035026, [2104.07366v2](https://arxiv.org/html/2104.07366v2) | Actual unmixed boundary amplitudes, residual baryon action, internal mass contractions and SM/Higgs B1 prohibition proved. Analytic mixed-mode admission and quantum protection remain separate. | [Source register](../topics/su6-protection-feasibility/references.md); [boundary result](../model-studies/su6-protection/boundary-model.md); [shared joint-action dictionaries](../topics/model-input-connections/literature-validation.md) |

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

## Additional spurion and covariant references

These sources supplement the original survey table. The finite-group result
also derives a sufficient spurion total-degree cutoff from the actual orbit
size; no such degree statement is imported from these sources. Their citation roles are
recorded in the [finite-group source register](../topics/finite-group-spurion-evaluation/references.md).

The [actual jet connection](../topics/jet-spurion-evaluation/results.md)
retains those bounds for fixed scalar EOM/IBP and mixed off-shell IBP sources,
after constructing local coinvariants. It includes the existing four-dimensional
massless scalar/Lorentz action and a complete one-direction sign-spurion
consumer with a sharp degree-one control. Spurions are constant and locally
neutral; the finite residual group alone is averaged. These source connections
are proved locally, with no new saturation, counting or amplitude premise from
the papers. The [connection register](../topics/jet-spurion-evaluation/references.md)
records the same restricted citation roles.

| Source | Relevant subject and citation role | Repository entry point |
| --- | --- | --- |
| B. Grinstein, X. Lu, C. Miró, P. Quílez, *Most general EFTs from spurion analysis: Hilbert series and Minimal Lepton Flavor Violation*, [2412.16285v1](https://arxiv.org/abs/2412.16285v1) | Motivation: saturation from arbitrary spurion powers at generic vacuum values. The finite-group proof is direct and applies at every value; no paper-wide or MLFV comparison is certified. Metadata and abstract checked for this extension; prior full-text inspection remains in the predecessor register. | [Finite-group evaluation](current/core/Math/FINITE_GROUP_SPURION_EVALUATION.md) |
| M. Brion, *Sur les modules de covariants*, Ann. sci. École Norm. Sup. (4) 26 (1993), no. 1, 1–21, [publication](https://numdam.org/articles/10.24033/asens.1665/) | Covariant-module background and the separate general algebraic-group boundary. A module-rank statement is not itself pointwise evaluation surjectivity; this theorem is not a premise of finite interpolation and averaging. Metadata checked for this extension. | [General-route feasibility and hypotheses](../topics/all-degree-symmetry-protection/feasibility.md); [finite-group result](current/core/Math/FINITE_GROUP_SPURION_EVALUATION.md) |

Existing [coverage ledgers](../verification/README.md) own only their actual
bounded source-to-formal-result comparisons. These references create neither
new coverage rows nor proof obligations to implement derivatives, EOM/IBP,
software, quantum anomalies or RGE. This is not an exhaustive prior-art search
and supports no priority or novelty claim.

## Derivative and IBP foundation survey

| Source | Citation role and limits | Repository entry point |
| --- | --- | --- |
| B. Henning, X. Lu, T. Melia, H. Murayama, *Hilbert series and operator bases with derivatives in effective field theories*, [1507.07240v1](https://arxiv.org/abs/1507.07240v1) | Fixed-multiplicity scalar momentum polynomials and translation relations in one dimension. Guidance for the independently proved scalar jet/IBP foundation. The bounded two-species C1 counts through order 2 now agree with Eq. (3.11); no general momentum-symbol or full-series equivalence is certified. | [Inspected locations and conditions](../topics/derivative-ibp/references.md#r1--scalar-momentum-space-pilot); [scalar result](current/core/Math/SCALAR_JET_IBP.md); [bounded C1 result](../topics/scalar-derivative-completeness/results.md) |
| L. Lehman, A. Martin, *Low-derivative operators of the Standard Model effective field theory via Hilbert series methods*, [1510.00372v1](https://arxiv.org/abs/1510.00372v1) | Conditions on simple vector-count subtraction; its limitation is not a limitation of all later methods. The complete native four-field order-two/order-four coefficient counts agree with its low-order scalar examples. The displayed subtraction failure starts at order six; no SMEFT table is certified. | [Survey conditions](../topics/derivative-ibp/references.md#r3--limits-of-simple-counting-subtraction); [complete-coefficient recheck](../topics/scalar-quartic-four-completeness/literature-validation.md) |
| W. Cao, F. Herzog, T. Melia, J. Roosmale Nepveu, *Renormalization and non-renormalization of scalar EFTs at higher orders*, JHEP 09 (2021) 014, [2105.12742v3](https://arxiv.org/abs/2105.12742v3) | Eqs. (3.28)–(3.29) and the bounded Eq. (A.20) count are compared in the native free scalar input. Evaluation on the chosen density is an equivalence on all selected coefficients; the three prescribed density values have a proved necessary and sufficient compatibility condition. No conformal, amplitude or renormalization premise is imported. | [Source roles and full comparison](../topics/scalar-quartic-four-completeness/literature-validation.md); [Lean consumers](../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarQuarticLiteratureChecks.lean) |
| H. K. Dreiner, H. E. Haber, S. P. Martin, *Two-component spinor techniques and Feynman rules for quantum field theory and supersymmetry*, [0812.1594v6](https://arxiv.org/abs/0812.1594v6) | Selected inspection: Section 2; (3.1.1)–(3.1.2),(3.2.1),(4.3.2); Appendices A and G.1. Proved comparisons cover free left/right EOM covariance, conjugate/IBP transport, ordered Weyl/Higgs current signs, and scalar/Weyl Yukawa density/Euler/full-relation dictionaries. Conjugate labels remain complexified; no physical reality, quantization, Feynman-rule or amplitude theorem. | [Original source register](../topics/linear-eom-weyl/references.md); [conjugate extension and limits](../topics/jet-eom-completion/references.md); [Weyl result](current/core/Physics/WEYL_CONJUGATE_IBP.md); [Weyl/Higgs current conventions](../topics/weyl-higgs-current-completeness/literature-validation.md); [Yukawa model comparison](../topics/lagrangian-model-connections/literature-validation.md); [automatic density-to-Euler comparison](../topics/euler-naturality/literature-validation.md); [full-input field-coordinate connection](../topics/model-input-connections/literature-validation.md) |
| D. Tong, *Electromagnetism*, [Electromagnetism and Relativity chapter](https://www.damtp.cam.ac.uk/user/tong/em/em4.pdf) | Selected text inspection of Sections 5.1.3–5.1.4, 5.3.2 and 5.4 in the served PDF: metric/index rules, antisymmetric field strength and covariant Maxwell/Bianchi equations. Convention guidance for a free complexified source model. No analytic, gauge-potential exactness, classical field-index dictionary or paper-wide comparison premise is imported. | [Inspection and library roles](../topics/abelian-field-strength/references.md); [free Abelian source result](current/core/Physics/ABELIAN_FIELD_STRENGTH_IBP.md) |
| D. Tong, *Gauge Theory*, [Yang–Mills chapter, Section 2.1](https://davidtong.org/pdfs/teaching/gauge-theory/gauge2.pdf) | Selected inspection of connection, curvature, covariant commutator, source-free EOM, Bianchi and local transformation formulas. Convention guidance for an independently proved formal complex matrix model with `nabla = partial + [A,-]`, including nonconstant internal-unit covariance. Section 2.1.1 also guides the independently proved formal trace first variation. No analytic, variational, gauge-orbit quotient, SU(N) real-form or paper-wide equivalence premise is imported. | [Source roles](../topics/nonlinear-eom-gauge-jets/references.md); [polynomial scalar and formal Yang–Mills result](current/core/Physics/FORMAL_YANG_MILLS_IBP.md); [gauge/trace extension](../topics/gauge-covariance-engineering/references.md); [first-variation result](../topics/formal-first-variation/results.md) |

The related position/momentum survey of Henning et al. is listed in G2 above.
These sources supply no theorem premise. The scalar foundation and its
[internal-linear/mixed extension](current/core/Math/MIXED_JET_IBP.md) prove
their jet, divergence and coefficient-descent statements independently; no
literature-to-Lean IBP or amplitude equivalence is certified.

## Formal library inputs for derivative foundations

[Physlib](https://github.com/leanprover-community/physlib), revision
[fixed revision](https://github.com/leanprover-community/physlib/commit/5bbbb30d08b8e151406a10affbc8a369b74b32c6), supplies the general
`PhyslibAlpha.Mathematics.ExteriorAlgebra` dependency and sections D/E of
`SymmetricAlgebra`, adapted under `Math.PhyslibSymmetric` in the
[local compatibility fragment](../../Math/LinearAlgebra/Symmetric/PhyslibSymmetricDerivations.lean).
The symmetric functoriality/product sections are omitted to avoid name conflicts
with TauCeti; source proofs and hypotheses are retained with qualified names.
These are checked Lean proofs of even derivation and covariance properties,
not assumed literature theorems. The
[connection audit](../../Math/Audit/AuditPhyslibAlgebraConnection.lean)
checks the selected declarations; the [dependency record](../topics/derivative-ibp/dependency-integration.md)
owns the exact environment and verification. The larger SM jet and analytic
IBP packages are not certified by this narrow connection. Source authorship
and Apache-2.0 notices remain in the upstream files and the adapted header.
The [completed compatibility gate](../topics/derivative-ibp/carrier-pilot.md)
checks the combined project closure with these sources; it adds no
derivative/IBP completeness or amplitude-equivalence claim.

The subsequent [A/B implementation](current/core/Math/MIXED_JET_IBP.md) uses
the exterior even derivation in its actual mixed algebra. Pinned TauCeti
[symmetric-power bases](https://github.com/TauCetiProject/TauCeti/blob/1f9b4414105d86e487a4ac4c3d3397076a44d0d2/TauCeti/LinearAlgebra/SymmetricPower/Basis.lean)
and [symmetric-algebra basis comparison](https://github.com/TauCetiProject/TauCeti/blob/1f9b4414105d86e487a4ac4c3d3397076a44d0d2/TauCeti/LinearAlgebra/SymmetricAlgebra/BasisComparison.lean)
support a new proved symmetric-tensor/polynomial equivalence, rather than
serving as an assumed semantic bridge. Mathlib supplies flat tensor-map
injectivity and the Clifford contractions used as coordinate probes. The
[mixed audit](../../Math/Algebra/Jets/Audit/AuditMixedJetIBP.lean) checks the actual
source connections, derivative-free recovery, internal covariance, IBP
descent and complete mixed quotient consumer. This adds no paper-wide
counting, Lorentz or EOM comparison claim; see the
[reconciled source register](../topics/derivative-ibp/references.md#ab-implementation-source-reconciliation).

The [direction/EOM extension](current/core/Math/DIRECTIONAL_JET_EOM_IBP.md)
also uses those proved factor covariance and symmetric-power basis inputs.
It constructs covariant currents, actual equation quotients and EOM/IBP
source/representation equivalences locally. Physlib's pinned
[SL(2,ℂ)/Lorentz source](https://github.com/leanprover-community/physlib/blob/5bbbb30d08b8e151406a10affbc8a369b74b32c6/Physlib/Relativity/SL2C/Basic.lean)
informed inspection of the Hermitian/Pauli construction. The
[physical consumers](current/core/Physics/LORENTZ_SCALAR_EOM_IBP.md) instead
prove a narrow local Pauli adapter from the existing Weyl action, including
the dual derivative convention and massless scalar trace relations. The
larger Physlib Lorentz/SM closure and equality with its coordinate map remain
outside the verified connection. The scalar EOM defines the algebraic model;
no paper-wide counting, variational or amplitude equivalence is certified.
See the [final source roles](../topics/derivative-ibp/references.md#cde-implementation-source-reconciliation).

The [linear-system/Weyl extension](../topics/linear-eom-weyl/results.md) reuses
the pinned exterior and attributed symmetric derivations on the actual quotient
generators. Mathlib supplies exterior-map and tensor-map surjectivity and the
quotient linear algebra. The scalar relation module and shifts are recovered
by equality/equivalence. The Weyl seed uses the repository Pauli action and a
proved dual contraction/frame intertwiner; its covariance is not a supplied
physical premise. The source register distinguishes this connection from the
separate mixed ideal-presentation, conjugate/interacting EOM and amplitude
boundaries. No literature comparison coverage row is added.

The [mixed kernel and conjugate extension](../topics/jet-eom-completion/results.md)
uses Mathlib two-sided ideals, congruence quotients, projective linear splitting
and semilinear quotient maps. It proves the actual mixed projection kernel
presentation and a complete positive-order single-field null IBP source.
The existing local exterior Hermitian conjugation is extended to commuting
formal derivatives and the actual linear divergence quotient; the right-Weyl
consumer proves its physical covariance inputs. These are local algebraic
results, with the inherited literature inspection limits and unchanged pins.

The [free Abelian field-strength extension](../topics/abelian-field-strength/results.md)
constructs actual tensor-square component and tensor equation actions using
Mathlib bases. Its metric bridge is derived from the existing Pauli quadratic
invariance. Antisymmetry, Maxwell and Bianchi covariance, full descendants,
wave consequences and null-symbol probes are local proofs. The existing common
linear EOM kernel and EOM/IBP theorems apply without an extra physical premise.
Inspected Physlib pointwise Maxwell equations and gauge-realization field
strengths occupy different domains; no equivalence with them is certified.

The [polynomial EOM and formal gauge extension](../topics/nonlinear-eom-gauge-jets/results.md)
uses mathlib ideal spans, quotient kernels and surjective derivation transport
to prove the full differential ideal and inverse linear EOM/IBP comparison.
Associativity and proved entrywise ordinary jet derivatives give curvature,
covariant commutators and Bianchi locally. The scalar interaction proves its
actual Pauli Lorentz inputs; the matrix Yang–Mills consumer constructs its
nonlinear equations and both ordinary and covariant descendant closure.
Tong supplies convention guidance, without an imported physical covariance
or completeness premise. Local gauge classes, analytic dynamics, general
normal forms and operator counts remain separate boundaries.

The [gauge/trace/engineering extension](../topics/gauge-covariance-engineering/results.md)
proves nonconstant internal-unit gauge covariance and its identity/composition
laws, trace IBP in the actual linear quotient, and positive engineering-degree
finite sources. The complete four-direction scalar degree-two image has basis
the field square and dimension one for every complex coupling; its detecting
functional annihilates the full unbounded EOM ideal and divergence range.
Mathlib supplies trace cyclicity and polynomial/finite basis APIs. Local gauge
orbit quotients, general Yang–Mills counts and all Lagrangian/first-variation
derivations remain outside the result; no new comparison premise is imported.

The [formal first-variation extension](../topics/formal-first-variation/results.md)
now derives normalized scalar and matrix Euler coefficients and explicit
boundary currents locally, and proves equality with the existing full
polynomial differential EOM ideals. This reopens the earlier formal deferral;
analytic actions and quantum equivalence remain outside the result.

| Source | Inspection and role | Local connection |
| --- | --- | --- |
| J. C. Criado and M. Pérez-Victoria, *Field redefinitions in effective theories at higher orders*, [arXiv:1811.09413v2](https://arxiv.org/pdf/1811.09413v2) | Selected introduction and Section 3 inspection. Scope guidance distinguishing the first-order EOM response from higher-order effects; no equivalence or matching theorem is imported. | [Source roles](../topics/formal-first-variation/references.md); [actual epsilon substitution and first variation](current/core/Physics/LAGRANGIAN_EOM_CONNECTION.md) |
| G. Sardanashvily, *Grassmann-graded Lagrangian theory of even and odd variables*, [arXiv:1206.2508v1](https://arxiv.org/pdf/1206.2508v1) | Selected Section 6, formula (31) and Theorem 16/(37) inspection. The algebraic local-polynomial specialization has actual left partials, multiindex adjoints and explicit first variation. No manifold, cohomology, regularity or literature theorem premise is imported. | [Source roles](../topics/local-lagrangian-helper/references.md); [independently proved finite-expression helper](../topics/local-lagrangian-helper/results.md); [semantic Euler comparison](../topics/euler-naturality/literature-validation.md); [shared-input regression scope](../topics/model-input-connections/literature-validation.md) |

The [additive derivative-input connection](../topics/derivative-interface-adapters/results.md)
reuses these proved local relation, mixed-jet and nonlinear-EOM results.
Its explicit contraction map transports additional source relations into the
published finite-local coordinate quotient; zero jets recover the old source
and full EOM inputs retain cross-grade relations. This is a local API/theorem
connection with [inherited source roles](../topics/derivative-interface-adapters/references.md),
not a new literature comparison or completeness premise.

The same adapter topic now provides a single mixed coefficient entry for all
natural-number derivative degrees, including zero. Its zero-jet inverse source
connection is proved for arbitrary direction actions; this uses existing local
jet/action theorems and introduces no further literature premise.

The adapter topic additionally supplies purpose-specific graded/EOM factories
with common operations and a proved invariant-subspace/full-quotient-image
connection. This reuses the existing local source and covariance theorems;
it introduces no new external reference or literature premise.

## Bounded Derivative-Interface Comparisons

The [reopened foundation work](../topics/derivative-literature-foundations/README.md)
now proves the gaugeless Higgs helper/direct Euler and full-relation
identification, actual paired field/dual dictionary and global SM/Lorentz
input stability. Grzadkowski et al. Eq. (5.3) guides the relation; the chosen
a,b normalization is independently derived. The
[source roles](../topics/derivative-literature-foundations/references.md)
retain the pinned primary versions. No full Warsaw basis, local gauge action,
Yukawa restoration or new literature theorem premise follows from this input.

The same bounded topic adds a complete free-scalar zero-derivative image,
global separating coefficients and a target-specific exact cubic-value
condition. Its paired Weyl kinetic helper is connected to both actual
Lorentz equation maps, full two-sided EOM/IBP and inverse coefficient
transport with off-shell Higgs spectators. These are independently proved
local foundations; positive-derivative invariant counts and the C5 physical
current dictionary remain partial after both routes. The finite certificate
requires actual source and relation-span proofs, not a paper count premise.

The subsequent [six-case recheck](../topics/derivative-literature-foundations/literature-recheck.md)
reinspects those primary versions and uses persistent Lean consumers of the
obtained foundations. Grzadkowski et al. Eqs. (2.1),(5.3) now have the exact
real-parameter a=-m2, b=lambda specialization in the actual generated
quotient. The Li current transcription passes a Pauli-divergence identity
using both generated Weyl equations, with arbitrary-product and symmetric
current EOM/IBP controls. Murphy's old raw separator is rejected on the new
free represented input. Scalar finite-row, zero-degree and second-order
substitution controls are rerun. These are scoped input/relation checks;
the remaining complete-basis and physical-current bridges are not closed.

The [nonderivative input checks](../topics/derivative-literature-foundations/nonderivative-recheck.md)
use actual old exterior/symmetric and finite-local coefficients through the
integrated interface. Henning's zero-derivative scalar terms and Grzadkowski's
rho squared/Q_phi representatives guide the corresponding actual model
tests. Li Eqs. (4.20)–(4.21) motivate a two-odd/five-even statistics control
only; its Unit symmetry is not a physical operator dictionary. The source
register records the reinspected locations. No additional paper-basis
completeness or selected-coefficient extension premise is used.

The [additional four-part verification](../topics/derivative-literature-foundations/extended-checks.md)
reinspects Henning's C1 Eq. (3.11) and C2 Eq. (6.3). It gives complete C1
d=0 images and a zero full (1,1),d=2 image, together with actual Weyl old/new,
presentation and supported real-source controls.

The [finite C1/C2 successor](../topics/scalar-derivative-completeness/results.md)
reinspects those same pinned equations. Independent Lean proofs complete the
three remaining selected C1 positive-degree sectors, with actual-image and
coefficient equivalences giving bounded counts (1,1,0)/(1,1,1). For C2 the
whole actual Lorentz order-two coefficient space vanishes; K squared is
nonzero in the full order-four EOM/IBP quotient, and the three specified
metric contractions reduce to its line. The
[order-four successor](../topics/scalar-quartic-four-completeness/results.md)
proves the complete selected invariant coefficient line, its normalized
inverse and extraction through K-squared evaluation. It checks all finite
wave moments in Lean and proves grade invariance under every actual Lorentz
group element. A complete Euclidean/Lorentz coefficient-space bridge and
arbitrary-degree series remain outside the result. Exact group-coordinate
checks are diagnostics, not Lean premises. The
[source register](../topics/scalar-derivative-completeness/references.md)
records the inherited roles. The successor's
[three-source recheck](../topics/scalar-quartic-four-completeness/literature-validation.md)
reinspects the pinned C2 equation and representative, Cao's normalized
densities and chosen combination, and Lehman–Martin's low-order scalar
examples. Every selected coefficient is reconstructed from either K-squared
or chosen-density evaluation. Dependency pins remain unchanged.

The [derivative necessary-condition connection](../topics/derivative-prohibition-input/results.md)
reuses the existing scalar-detection and common-irreducible theorems, actual
quotient interfaces, quadratic comparison and Lorentz scalar equation.
Its [source register](../topics/derivative-prohibition-input/references.md)
records those inherited roles. It imports no new paper premise and claims
no additional paper-basis comparison; C1–C5 retain the gaps recorded below.

The [subsequent usage survey](../topics/derivative-input-literature-review/review.md)
reinspects the same six pinned primary sources through these new input
conditions. Actual support change, cross-count coefficient constraints and
the constructed scalar coupling restriction supply worked examples;
remaining action/dictionary, descent and completeness obligations stay
explicit. Its [inspection register](../topics/derivative-input-literature-review/references.md)
records selected locations. This documentation review adds no proof coverage
or external theorem premise.

The [comparison results](../topics/derivative-literature-comparison/results.md)
process all six fixed sources. The
[pinned register](../topics/derivative-literature-comparison/references.md)
and [coverage ledger](../verification/derivative-interface-coverage.md)
distinguish proved algebraic subsets from remaining invariant-basis and
physical-dictionary bridges. The one-dimensional quadratic scalar count,
actual Lorentz scalar relation, component Higgs EOM identity and mixed
Grassmann/IBP controls are proved. Five comparisons remain partial; the
chosen quartic scalar substitution/helper-input contract is proved through
order two. Neither exact diagnostic counts nor literature completeness
statements are Lean premises. No complete derivative SMEFT basis is certified.

| Source | Final comparison role and limits | Result |
| --- | --- | --- |
| C. W. Murphy, *Dimension-8 Operators in the Standard Model Effective Field Theory*, [2005.00059v6](https://arxiv.org/abs/2005.00059v6) | Table 2's free ordinary-derivative Higgs contractions give complete coordinates for all admitted invariant coefficients on the entire actual grade (4,4), with normalized inverse and dimension 3. Full global covering-SM/Lorentz actions and complete free EOM/linear IBP are proved. No full SMEFT or interacting EOM claim; Table 5's fixed free one-flavor current also gives a complete scalar coordinate on the entire actual mixed grade (2,4,1), with normalized inverse, both inverse laws, nonzero full-quotient support and complex dimension one; the block/Pauli dictionary is proved. | [C4 theorem](../topics/higgs-quartic-four-completeness/results.md); [validation](../topics/higgs-quartic-four-completeness/literature-validation.md); [C5 current validation](../topics/weyl-higgs-current-completeness/literature-validation.md) |
| H.-L. Li, Z. Ren, J. Shu, M.-L. Xiao, J.-H. Yu, Y.-H. Zheng, *Complete Set of Dimension-8 Operators in the Standard Model Effective Field Theory*, [2005.00008v3](https://arxiv.org/abs/2005.00008v3) | Eq. (4.8)'s native higher-derivative Higgs values are proved equivalent to (4q3,q1,q2-q1-q3) modulo full free EOM/IBP, yielding complete native selected-coefficient coordinates. Separately, Eqs. (4.23)–(4.26) guide fixed-flavor current tests; the fixed free one-flavor charged-lepton (4.24) row now gives a complete native scalar coordinate on the whole actual mixed grade, with normalized inverse, both inverse laws, complex dimension one and generated/component agreement. The actual group and full unbounded EOM/IBP bridges are proved. No whole-paper completeness premise is imported. | [C4 validation](../topics/higgs-quartic-four-completeness/literature-validation.md); [C5 input/current result](../topics/weyl-higgs-current-completeness/results.md); [C5 validation](../topics/weyl-higgs-current-completeness/literature-validation.md) |
| O. J. P. Eboli, M. C. Gonzalez-Garcia, *Mapping the genuine bosonic quartic couplings*, [1604.03555v1](https://arxiv.org/abs/1604.03555v1) | Eq. (16) and footnote 2 supply the three-density order (q2,q3,q1) in the free/gaugeless specialization. Complete selected-coefficient extraction and an omitted-O_S,2 nonzero control are proved. Gauge-boson coupling formulas, nonlinear realizations and phenomenological bounds are outside the check. | [C4 validation and source register](../topics/higgs-quartic-four-completeness/literature-validation.md) |


## Interacting All-Order Coefficient Transport

The [general all-order presentation](current/core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md)
is proved independently from actual monomial bases and generated differential
relations. It imports no literature completeness premise. The
[source-specific consumers](../topics/interacting-lagrangian-classification/literature-validation.md)
retain the gaugeless Higgs relation of Grzadkowski et al. (1008.4884v3,
Eqs. (2.1),(5.3)) and the constructed scalar first-variation specialization
of Criado–Pérez-Victoria (1811.09413v2, §3 Eq. (3.2)). Infinite coordinate
transport does not establish higher-order field-redefinition equivalence.

| Source and inspected location | Role and verified scope | Evidence |
| --- | --- | --- |
| D. Tong, *Lectures on Quantum Field Theory*, [HTML §5.6, Eq. (5.475)](https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S5.html) | The literal four-component interaction -g phi sum_a(barPsi_a Psi_a), all nine left-Grassmann Euler components, and complete all-order generated-input transport. Barred/unbarred labels are independent; the consumer has trivial group action. Full kinetic, Lorentz, scattering and rate dictionaries are outside this comparison. | [Interaction and Euler consumers](../../Physics/FieldTheory/Jets/Lagrangian/InteractingLagrangianLiterature.lean), [comparison scope](../topics/interacting-lagrangian-classification/literature-validation.md) |

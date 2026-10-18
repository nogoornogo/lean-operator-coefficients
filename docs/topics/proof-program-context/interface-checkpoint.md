# Archived Interface Catalogue

Scoped catalogue of declarations and verification evidence. This is not the
current general theorem's input package; use the [current proof index](../../proof/README.md).

This index links declaration catalogues and implementation maps stored alongside
their Math, Physics and GUT proof dossiers. Topics own progress and verification;
these maps explain interfaces, not a second current-status database.

Each individual map follows the [seven-section proof format](../../proof/TEMPLATE.md):
result, inputs, conventions, proof structure, Lean entry points, limitations,
and sources/verification. Detailed declaration names and historical audit
records are retained; checkpoint counts and pending notes are not a current queue.

## Checked baseline

- The [graded naturality integration](../graded-completeness-naturality/results.md#master-integration)
  records the merged-tree full build (6,547 jobs) and strict focused audit.
  The [upgrade verification](../tauceti-lean-upgrade/README.md#warning-cleanup-verification)
  is earlier checkpoint evidence; committed pins and the [build guide](../../architecture/BUILD.md)
  govern the environment. Topic records own verification, not this index.
- The earlier [Takagi merged-state check](../majorana-congruence-interface/README.md#integration)
  and [historical baseline](checkpoints/verified-baseline.md) are
  checkpoint evidence, not the current toolchain. This documentation pass
  did not rerun Lean or establish a new proof baseline.
- Kernel trust means the relevant declarations build without `sorryAx` in the
  stated scope. The E6 simple-connectedness implication has an explicit external
  premise; a clean axiom audit does not prove that premise. Literature-based
  named-E6 interpretation and unconditional Lean identification are distinguished.

TauCeti is now a pinned project dependency.  Its one-parameter subgroup
classification and Trotter results close the continuity-only embedding regularity
bridge; project-specific specialization remains in this repository.

## Domain index

The rows describe each interface's own scope. Exclusions such as a missing
global comparison are not project-wide task statuses: later stages in the same
table may supply additional results. Consult the linked dossier and owning topic.

| Domain | Contents |
| --- | --- |
| [Self-dual chirality](../../proof/current/inputs/Math/interfaces/self-dual-chirality.md) | Zero source/radical dual index, positive SM target exclusion after forgetting charges, and actual standard-chain evaluator/model bridge |
| [Compact symplectic chirality](../../proof/current/inputs/Math/interfaces/compact-symplectic.md) | Actual compact carrier, paired orthonormal diagonalization, all-element torus/inverse conjugacy, zero character/mass index on arbitrary subgroup restrictions, and positive exact SM target exclusion |
| [Compact Spin chain](../../proof/current/applications/GUT/interfaces/spin-chain.md) | Actual SU(5) -> compact Spin(10) closed embedding and common continuous/scalar-family selection-rule endpoint checked |
| [Compact half-spin source](../../proof/current/applications/GUT/interfaces/spin-half-spin.md) | Actual continuous unitary 16, central character, exact exterior action, and all-SU(5) character `1 + 10 + bar5`; inhabited continuous zero-mass model with derived positive target, exact torus/residual spectrum, and nonzero mode support |
| [E6 feasibility audit](../e6-global-topology/decisions/E6_FEASIBILITY.md) | Closed audit with 38 pinned algebraic declarations and concrete API tests; later candidate SU(5) inclusion and positive-target model are checked below, while named global E6 remains a target |
| [E6 matrix prototype](../../proof/current/inputs/GUT/E6_MATRIX_PROTOTYPE.md) | Adjoint/traceless generators, actual SU(27) exponentials, invariant D5 coordinate subspaces of dimensions 16/10/1 and the still-open compact/global contract; the initial external basis experiment is superseded by the certificate below |
| [E6 finite Lie certificate](../../proof/current/inputs/Math/E6_LIE_CERTIFICATE.md) | Actual generated matrix Lie dimensions 78/45, finite span equality, linear independence and injective matrix D5 inclusion; sound generic certificate checker |
| [E6 Geck comparison](../../proof/current/inputs/Math/E6_GECK_COMPARISON.md) | Generator-preserving E6/D5 Lie equivalences over algebraically closed characteristic-zero fields; faithful actual 27 matrix actions and numbered D5 inclusion; compact/global bridges remain open |
| [E6 real forms](../../proof/current/inputs/Math/E6_COMPACT_REAL_FORM.md) | Actual skew-Hermitian real dimensions 78/45, Lie complexifications to the Geck carriers, compatible injective real D5 inclusion, and SU(27) exponentials for all real-form elements; global groups remain targets |
| [E6 matrix normalizer](../../proof/current/inputs/Math/E6_MATRIX_NORMALIZER.md) | Scalar commutant of actual generators, exact trace-zero complex and skew-Hermitian real Lie-normalizer bounds; no group-normalizer/tangent identification |
| [E6 compact normalizer](../../proof/current/inputs/Math/E6_COMPACT_NORMALIZER.md) | Actual closed compact SU(27) normalizer and exact all-real-time exponential criterion for the 78-dimensional real form; no manifold tangent or global E6 identification |
| [E6 identity component](../../proof/current/inputs/Math/E6_IDENTITY_COMPONENT.md) | Connected compact candidate with the same exponential directions, an order-27 central element in the full normalizer, and compiled ambient matrix log/exp inverses; component center/global form remain open |
| [E6 local logarithm](../../proof/current/inputs/Math/E6_LOCAL_LOG.md) | Derived local real-form logarithm and positive radii; open identity component equals the algebraic subgroup generated by real-form exponentials; manifold/global identification remains open |
| [E6 local chart](../../proof/current/inputs/Math/E6_LOCAL_CHART.md) | Actual open exponential chart with ambient-log inverse on its full target |
| [E6 smooth atlas](../../proof/current/inputs/Math/E6_SMOOTH_ATLAS.md) | Analytic transitions, smooth manifold and ambient exponential derivative at zero |
| [E6 candidate Lie group](../../proof/current/inputs/Math/E6_CANDIDATE_LIE_GROUP.md) | Smooth matrix inclusion and actual smooth group operations; global identification remains open |
| [E6 tangent image](../../proof/current/inputs/Math/E6_TANGENT_IMAGE.md) | Actual matrix differential is injective with image exactly the real form |
| [E6 tangent Lie algebra](../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md) | Geometric tangent Lie algebra is Lie-equivalent to the actual E6 real form; simple connectedness and global identification remain open |
| [E6 SU(5) coordinates](../../proof/current/applications/GUT/E6_SU5_COORDINATES.md) | Signed equivalence to actual scalar/defining/dual/exterior modules, raising/lowering/Cartan and compact-generator action comparison, and fixed Hermitian identity; not a group inclusion or an E6 endpoint |
| [E6 candidate SU(5) group map](../../proof/current/applications/GUT/E6_SU5_GROUP_MAP.md) | Actual continuous injective closed SU(5) inclusion into the candidate, all-time exponential compatibility, real Lie-image membership and group-level 27 intertwining; common conditional consumer audited, named-E6 identification still open |
| [E6 candidate positive-target model](../../proof/current/applications/GUT/E6_POSITIVE_TARGET.md) | Actual continuous unitary 27 and derived positive dual index, preserved by invariant symmetric masses; zero-mass/trivial-residual continuous inhabitant and actual SM modes; vectorlike pair remains light, not a named global E6 or SM-only full-spectrum theorem |
| [E6 order-three center](../../proof/current/inputs/Math/E6_CENTER_THREE.md) | Constructed central element of exact order three in the identity component, center-order lower bound and actual 27 non-descent to the center quotient |
| [E6 cubic and exact center](../../proof/current/inputs/Math/E6_CUBIC_CENTER.md) | Kernel-checked nonzero cubic, actual exponential and group invariance, center isomorphism to the cube roots of unity, and nonmembership of the ambient order-27 scalar; simple connectedness/global identification remain open |
| [E6 actual maximal torus](../../proof/current/inputs/Math/E6_COMPACT_TORUS.md) | Closed six-circle embedding and exact Cartan period lattice, cubic-based diagonal reconstruction, self-centralizer and maximality among Abelian subgroups; no fundamental-group computation |
| [E6 candidate topology](../../proof/current/inputs/Math/interfaces/e6-topology.md) | Actual torus-loop contractions and trivial induced map; conditional simple connectedness from an explicit maximal-torus surjectivity input. The general input theorem and named-group comparison are not formalized; see the [literature boundary](../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md) |
| [Flipped character](../../proof/current/applications/GUT/interfaces/flipped-character.md) | Normalized Laurent model, swap action, finite-virtual character obstruction |
| [Representation certificates](../../proof/current/applications/GUT/interfaces/representation-certificates.md) | Constructive representations and flipped-obstruction audit certificates |
| [Semisimple embedding classification](../../proof/current/applications/GUT/interfaces/embedding-classification.md) | Complete reducibility, low-dimensional blocks, differential bridge |
| [Hypercharge centralizer](../../proof/current/applications/GUT/interfaces/hypercharge-centralizer.md) | Physical centralizer, topology, cocharacters, matrix tangent |
| [Hypercharge character rigidity](../../proof/current/applications/GUT/interfaces/hypercharge-character-rigidity.md) | Finite weights, Weyl invariance, fifth-moment bridge |
| [Standard-branch assembly](../../proof/current/applications/GUT/interfaces/standard-branch-assembly.md) | Charge-orbit bridge, operator neutrality, anomaly cross-check, and scoped assemblies |
| [Shared selection rules](../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md) | SU(6)-independent charge, weight, signature, and tensor foundation; not the SU(5) source bridge |
| [Standard SU(5) embedding](../../proof/current/inputs/GUT/interfaces/su5-embedding.md) | Actual continuous covering map, exact central cyclic kernel, and closed topological quotient embedding |
| [SU(5) matter and branching](../../proof/current/inputs/GUT/interfaces/su5-matter.md) | Actual continuous unitary 5/bar5/10, full-group branching, quotient descent, and algebraic/unitary constituent irreducibility |
| [SU(5) ordinary-Abelian source](../../proof/current/inputs/GUT/interfaces/su5-source.md) | Full U centralizer, exhaustive character sectors, actual field support, neutral signatures, and nonzero invariant ordered internal tensors |
| [SU(5) final assembly](../../proof/current/applications/GUT/interfaces/su5-final.md) | Universal charge-prohibition obstruction, per-slot choices, exact quotient tensor actions, one-generation inhabitant, and final audits |
| [Scalar-dependent masses](../../proof/current/inputs/Physics/interfaces/scalar-dependent-mass.md) | GUT-independent families, finite multilinear sources with mixed/conjugate slots, joint continuity, fixed-vacuum evaluation, and exact legacy compatibility |
| [Scalar-dependent model](../../proof/current/applications/GUT/interfaces/scalar-dependent-model.md) | Scoped SU(6) source-to-mass-to-selection-rule adapter, exact old-model recovery, nonlinear nonzero 15-mode example, and zero-VEV control |
| [Finite charge profiles](../../proof/current/applications/GUT/interfaces/finite-charge-profiles.md) | Finite distributions, actual radical vectors, source-derived hypercharge/profile equalities, continuous model endpoint, scalar-family/legacy compatibility, actual SU(5) profiles, and a derived two-charge SU(6) example; all planned gates checked |
| [Standard SU(5) chain](../../proof/current/applications/GUT/interfaces/standard-su5-chain.md) | Checked shared mass spectrum, actual SU(5) source, ambient wrappers and inhabitants, retained SU(5) and canonical SU(6) model conversions with full spectrum compatibility |
| [Standard SU(N) family](../../proof/current/applications/GUT/interfaces/standard-su-n.md) | Universal continuous injective block inclusion, conditional standard-chain endpoint for every N >= 5, exact N = 5/6 comparisons and actual SU(7) positive-target continuous source |

## Operator And Stabilizer Interfaces

The domain catalogue above primarily covers the earlier GUT foundations.
Use the owning topic records for subsequent interfaces and their verification:

- [Four-sector common completeness](../operator-completeness-interface/integration.md).
- [Delta L one total residual product](../delta-l-one-completeness/results.md#complete-residual-product).
- [Six-quark physical residual Hom](../delta-b-two-model-interface/flavor-hom.md).
- [Weinberg and Majorana forms](../delta-l-two-weinberg/results.md).
- [Dipole model-author interface](../clfv-dipole-model-interface/model-author-guide.md).
- [Specified VEV group, cover and Hom transport](../vev-stabilizer/global-group.md).
- [Specified flavor stabilizers](../flavor-stabilizer/results.md).
- [Full unitary Majorana classification](../majorana-unitary-stabilizer/results.md)
  and [Takagi existence](../majorana-congruence-interface/existence.md).

The former [open-obligations snapshot](formalization/open-obligations.md)
is archived, not a current task list. Current assumptions and boundaries belong
in [ASSUMPTIONS](../../proof/ASSUMPTIONS.md) and each topic record.

## Reading and update rule

Routine work reads `git status`, the selected [topic record](../README.md),
and its linked domain dossier. Plans and results stay in the same topic;
historical milestone records are not routine session inputs. The
[SU(5) roadmap](../su5-foundations/plans/SU5_FORMALIZATION.md) is complete in its declared
retained-spectrum scope, separately from the SU(6) index models. This index changes only when the
toolchain, trust boundary, audit baseline, or domain map changes.  Claim-level
scope belongs in the dossiers reached through [the proof index](../../proof/README.md);
logical implications belong in [the dependency map](proof-dependencies.md).

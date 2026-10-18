# Compact E6 feasibility audit

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../proof/README.md).

See the [proof-document conventions](../../../proof/TEMPLATE.md) for citation roles and build prerequisites.

External reference roles and the stage 02 bibliographic checks are recorded
in the [individual reference review](../../../proof/REFERENCE_REVIEW.md).

## 1. Result and status

Updated: stage 01

## 4. Proof structure

### Reusable Ingredients

The persistent [Lean audit](../../../../Math/LieGroups/E6/Audit/AuditMinusculeCarrier.lean)
checks concrete type signatures and a fixed allowlist of transitive axioms.
Build results are recorded below; source inspection alone is not a build.
Names in this table are in TauCeti unless otherwise stated.

| Ingredient | Declarations checked by the audit | Boundary |
| --- | --- | --- |
| Integral E6 root datum | `DynkinType.e6SimplyConnectedRootDatum`, `hasCartanType_e6SimplyConnectedRootDatum` | A root datum, not a Lie group |
| 27 weights | `e6MinusculeWeight_injective`, `range_e6MinusculeWeight`, `ncard_orbit_e6MinusculeWeight` | The Weyl orbit of the first fundamental weight |
| Full character lattice | `span_range_e6MinusculeWeight_eq_top` | Lattice generation, not compact group identification |
| Integral/rational matrices | `E6Minuscule.isSerreSystem`, `isSerreSystemQ`, `serreRepresentation`, `rationalSerreRepresentation` | Representations of the Serre presentation |
| Admissible lattice | `rep_serreKostantForm_mem_lattice` | Kostant-form invariance |
| Algebraic matrix carrier | `groupScheme`, `points`, `mem_points_iff`, `isClosedImmersion_carrierι` | Subgroup scheme of GL(27) over the integers |
| Simple-root subgroups and torus | `isClosedImmersion_rootSubgroup`, `isClosedImmersion_weightTorus`, named-root conjugation equations | Twelve numbered simple-root subgroups and a split rank-six torus |
| Matrix points and scalar maps | `pointsPresentation`, `coe_rootSubgroupPoints`, `coe_weightTorusPoints`, `map_rootSubgroupPoints`, `map_weightTorusPoints` | Algebraic points, including specialization to complex scalars |
| Geck comparison | `DynkinType.serreLift_surjective`, `geckLieEquiv` | Surjection from the presentation to the concrete split Lie algebra, not an equivalence from the presentation |
| Killing form | `DynkinType.instIsKillingLieAlgebra`, `instIsKillingLieAlgebraBaseChange` | Nondegenerate on the concrete rational algebra and its characteristic-zero scalar extensions; not yet a comparison with the 27 matrices |

The complex-points smoke tests instantiate the group, its injective map to
GL(27), the split torus, and the additive root maps without extra certificates.
They do **not** instantiate a compact group or a unitary action.

### Bridge Ledger

These were missing from the initially inspected APIs, not claims that the
statements are false. E6-0d now closes M1 at the complex Lie-algebra level;
M2/M3 and the intended global-group identifications remain open; M4/M5
have the candidate-group specializations recorded below.
[E6-0e](../../../proof/current/inputs/Math/E6_COMPACT_REAL_FORM.md) additionally closes the
skew-Hermitian real-form/complexification step, not the global group step.

1. **M1: identify the Lie algebra acting on the 27. COMPLETED over Complex.**
   [E6-0d](../../../proof/current/inputs/Math/E6_GECK_COMPARISON.md) constructs generator-preserving Lie
   equivalences between the checked matrix algebras and the actual
   scalar-extended E6/D5 Geck carriers, hence faithful 27-dimensional
   matrix actions. The proof combines matching bases, a proper-product
   theorem, target simplicity, and dimensions. The separate surjection
   from the Serre presentation is not assumed injective. No general
   rational/integral presentation theorem or algebraic-group tangent
   identification is claimed.
2. **M2: justify a compact real group of the intended global form.**
   The actual real forms now have proved dimensions 78/45, complexification
   Lie equivalences and SU(27) exponentials for all real-form elements.
   [E6-0f](../../../proof/current/inputs/Math/E6_MATRIX_NORMALIZER.md) proves the scalar commutant and exact
   trace-zero Lie-normalizer bounds. [E6-0g](../../../proof/current/inputs/Math/E6_COMPACT_NORMALIZER.md)
   constructs a closed compact SU(27) normalizer and identifies its
   all-time matrix-exponential directions exactly with the real form.
   [E6-0h](../../../proof/current/inputs/Math/E6_IDENTITY_COMPONENT.md) passes the criterion to its closed
   compact connected identity component and constructs an order-27 central
   element in the full normalizer. The latter cannot be a group with
   center of exponent dividing three; its order-27 scalar is now proved
   outside the component by the later cubic package.
   [E6-0i](../../../proof/current/inputs/Math/E6_LOCAL_LOG.md) proves local real-form logarithms,
   openness of the identity component and its exact algebraic generation
   by exponentials. [E6-0j](../../../proof/current/inputs/Math/E6_LOCAL_CHART.md) constructs an actual open
   exponential chart with ambient-log inverse. [E6-0k](../../../proof/current/inputs/Math/E6_SMOOTH_ATLAS.md)
   supplies a smooth atlas and the ambient exponential derivative at zero.
   [E6-0l](../../../proof/current/inputs/Math/E6_CANDIDATE_LIE_GROUP.md) proves smooth group operations and the
   actual `LieGroup` instance. [E6-0m](../../../proof/current/inputs/Math/E6_TANGENT_IMAGE.md) computes the
   injective matrix differential and its exact real-form image.
   [E6-0n](../../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md) identifies the actual geometric tangent
   Lie algebra with the real form. [E6-0p](../../../proof/current/inputs/Math/E6_COMPACT_CENTER.md) proves that
   the component center is finite cyclic of order dividing 27. The later
   [center package](../../../proof/current/inputs/Math/E6_CENTER_THREE.md) constructs a central element of exact
   order three and proves that the actual 27 does not descend to the center
   quotient, so `3 divides |Z| divides 27`. The subsequent
   [cubic package](../../../proof/current/inputs/Math/E6_CUBIC_CENTER.md) proves actual group invariance of a
   nonzero cubic and the exact order-three center. The later
   [torus package](../../../proof/current/inputs/Math/E6_COMPACT_TORUS.md) constructs a closed six-circle
   subgroup, exact Cartan period lattice and self-centralizer, supplying
   the actual maximal torus but not the fundamental-group comparison. Simple connectedness
   and global identification remain unproved; further
   work on this full realization route is deferred.
   `GroupScheme.lean` and `RootDatum.lean` explicitly do not prove reductivity,
   smoothness, maximality of the torus, or identification of the carrier's
   root datum. Complex algebraic points are not the compact real group.
   A compact realization must be justified independently, with its Lie type,
   connectedness and global form addressed. Intersecting with U(27), or
   taking a closure of generated matrices, does not by itself prove these
   identifications. A finite Lie-algebra calculation does not alone identify
   the Lie algebra of that closure.
3. **M3: actual Spin(10) inclusion.** Construct a continuous injective map
   from the existing `GUT.CompactSpin.Group 10` into the justified carrier.
   A D5 subdiagram or a Lie-algebra inclusion is not this map. If using the
   larger subgroup, prove the diagonal central kernel of
   `Spin(10) x U(1)` rather than declaring it a direct-product subgroup.
   The direct SU(5) route now constructs the required SU(5) map into the
   candidate without this intermediate Spin map. M3 itself remains open.
4. **M4: continuous unitary 27 and actual restriction.** Derive the group
   action and the restriction `27 = 16 + 10 + 1`, with the half-spin/dual
   orientation matched to the project's positive SM target. A finite
   weight table becomes a group character calculation only after the
   compatibility with the actual action has been proved. The separately
   checked SU(5) inclusion now supplies the actual group restriction
   `1 + 1 + 5 + bar5 + bar5 + wedge^2(5)`, not just its infinitesimal
   generators. `UnitaryRepresentation` and `MinusculeBenchmark` now construct
   the actual continuous unitary 27 and derive its positive exact dual light
   target. Spin(10) module and named global-group identifications remain open.
5. **M5: endpoint and inhabitant.** Reuse the checked standard-chain
   selection rule once a justified carrier and actual chain are available.
   The candidate-group map instantiates the common conditional consumer,
   and the positive-target 27 now supplies an actual continuous inhabitant
   with zero mass and trivial residual action. M2 is still required for the
   intended global E6 name. Vectorlike terms and singlets cancel in the dual
   index, not in the full zero-mode spectrum; the example retains 27 modes.
   This is not a dynamical mass or vacuum theorem.

### Search Coverage and Alternatives

The alternatives below record the original investigation, not an active
implementation queue. The audit's negative feasibility finding is a valid
completion; it does not authorize implementing every missing foundation.

Source inspection covered both `Algebra/Lie/E6/{Minuscule,DoubledMinuscule}`
trees, E6 root-datum modules, the generic Serre/Geck comparison, and the
nearby topology, representation, algebraic-group and manifold APIs.
No ready-to-use compact-E6 or Spin-to-E6 map was located there. This is a
bounded search result, not a formal nonexistence theorem.

- **Matrix/minuscule route: preferred next experiment.** Reuse the integral
  27 matrices. Check adjoint relations, a finite Lie-basis/root-space
  description, and the D5 restriction in explicit coordinates. A later
  compact-group identification is still indispensable.
- **Algebraic group scheme route: keep as an alternative.** The current
  carrier has useful point/torus APIs, but its identification plus the
  compact-real/topological bridge would add substantial foundations.
- **Albert/Jordan route: not a ready substitute.** The pinned
  `Algebra/AlbertAlgebra.lean` constructs the split model and explicitly
  leaves the Jordan identity and F4 derivation identification unproved.
  It is source-inspected, not included in the compiled E6 audit. Changing
  constructions would add octonionic/real-form work rather than automatically
  remove M2.
- **General integration route: no applicable theorem located.** Mathlib's
  `Geometry/Manifold/GroupLieAlgebra.lean` constructs a Lie algebra from an
  already given Lie group. It is not the reverse existence/integration
  theorem. TauCeti's `RepresentationTheory/Compact/Integrated.lean` concerns
  Haar-integrated operators on already given representations, not integration
  of a Lie-algebra representation.

SageMath's [branching API](https://doc.sagemath.org/html/en/thematic_tutorials/lie/branching_rules.html)
and GAP/SLA's [subalgebra and branching API](https://gap-packages.github.io/sla/doc/chap6.html)
are optional candidate generators. Exact integer/rational witnesses must
be checked in Lean; neither agreement between tools nor a data digest proves
M1-M4. No installation or external computation was needed for this audit.
Keep compiler-trusting evaluation outside the accepted proof boundary.

The user-suggested [chirality project](https://github.com/emad-ii/chirality-standard-model)
was consulted only through its public overview, verification notes and license.
No source, data, certificates or manuscript passages were copied into this
repository. Future mathematical constructions should be developed independently
from standard references; do not translate restricted code as a workaround.

### Feasibility Gate and Revised Estimate

**Current control:** [E6_ENDPOINT_PLAN.md](../plans/E6_ENDPOINT_PLAN.md) supersedes
the earlier continue-with-foundations recommendations and estimates below.
The concrete order-three step has been completed separately; the larger
global construction remains deferred, even if another lemma looks tractable.
There is no reliable end-to-end estimate for the named E6
application. The common theorem itself is already proved; its concrete
source bridge is the relevant remaining objective.

**Historical E6-0o follow-up:** the [global-form audit](E6_GLOBAL_FORM_AUDIT.md)
records the pinned APIs and remaining global bridges after E6-0n closed
the geometric tangent Lie-algebra comparison. It proposed bounded
scalar-center and Cartan-table proofs; general integration/classification retained
the separate cost-review gate. Simple connectedness and actual Spin
inclusion are not consequences of the local comparison alone.

**E6-0d follow-up:** [generator-preserving comparison](../../../proof/current/inputs/Math/E6_GECK_COMPARISON.md)
closes M1 over algebraically closed characteristic-zero fields, including
Complex. It uses the E6-0c 78/45 dimension certificates and existing
mathlib Lie-basis/root-space theorems. M2-M5 remain open; no estimate for
general integration is inferred from this successful bounded comparison.

**E6-0b follow-up is complete:** the
[matrix prototype and compact-carrier contract](../../../proof/current/inputs/GUT/E6_MATRIX_PROTOTYPE.md)
record checked adjoint equations, SU(27) exponentials and invariant D5
coordinate blocks, plus an explicitly external Lie-basis candidate. M1-M5
are not thereby closed. The historical estimate below is retained for context.

**Historical recommendation: proceed with a bounded matrix-level prototype;
do not treat full E6-1 as an available-library specialization.** The main risk is M2/M3, not enumerating
27 weights. The theorem's physical scope need not change to pursue this path.

- **E6-0b, 1-3 workdays:** test the adjoint/compact-generator equations and
  size/shape of a finite Lie-basis and D5-branching certificate. Report which
  parts are kernel-checked, which are external calculations, and a proposed
  precise compact-carrier identification contract. Stop at that contract;
  this is not permission to implement general Lie integration or reductive
  group classification.
- **E6-1:** no reliable end-to-end estimate yet. The previous conditional
  15-40+ workdays is not validated by this audit and is not an upper bound.
  If M2 needs general foundations, a separate weeks-to-months plan and a
  review checkpoint are required before undertaking them.
- **E6-2:** retain a provisional 5-15+ workdays only *after* an actual
  compact inclusion and a usable 27 action are available. Generator discovery
  and model identification are not included in that conditional estimate.

These are planning judgments, not measured proof times or credit budgets.
Defining a carrier named E6 and assuming its missing properties is not an
acceptable way to close the gate. The previous SU(N), symplectic and Spin
results remain independently valid and are not waiting for E6.

## 6. Scope and limitations

### Checkpoint and Scope

Rollback checkpoint: annotated tag `pre-e6-audit-stage 01`, commit
`checkpoint 01`. It contains the completed
SPIN-2c positive-target compact half-spin model, before this audit.
The tag is local; no remote push or reset is part of the audit.

**E6-0 is complete as an implementation-feasibility audit, not an E6 no-go theorem.**
The original Spin-based E6-1 (inclusion into the intended compact E6) and
E6-2 on that named global group remain **TARGET**. The alternative SU(5)
map and an actual positive-target 27 model on the existing candidate are
now checked; the intended global identification is not, as described below.
No new physical hypothesis, axiom, dependency revision,
or external calculation is admitted as a proof.

**Scope correction after E6-0p:** the audit is closed. Preserve the checked
matrix/local-group/center-bound results. The order-three step was later
completed in a separately scoped [center package](../../../proof/current/inputs/Math/E6_CENTER_THREE.md), after
the actual-model milestone. A later [cubic package](../../../proof/current/inputs/Math/E6_CUBIC_CENTER.md)
proves exact center; simple connectedness and general
global realization remain deferred. The remaining ledger
claims are not tasks that must be completed to finish this audit; later
candidate-group results below close only their stated interfaces.
The [endpoint-first plan](../plans/E6_ENDPOINT_PLAN.md) now controls any continued
work toward the physical selection-rule result. Deferred foundations
require a separate bounded proposal and explicit user approval.

**Direct-bridge follow-up:** the single permitted two-route inspection is
[complete](E6_DIRECT_BRIDGE_DECISION.md). A subsequent, separately approved
[coordinate implementation](../../../proof/current/applications/GUT/E6_SU5_COORDINATES.md) constructs the signed
SU(5) module equivalence and proves generator/Hermitian compatibility.
The subsequent bounded [group-map implementation](../../../proof/current/applications/GUT/E6_SU5_GROUP_MAP.md)
proves represented exponentials, subgroup membership and an actual
continuous injective SU(5) inclusion in `compactIdentityComponent`, with
the actual group restriction on the 27. The separately scoped
[positive-target model](../../../proof/current/applications/GUT/E6_POSITIVE_TARGET.md) now derives the dual light
target and constructs a zero-mass continuous inhabitant on that candidate.
Global naming remains open. This does not reopen the completed feasibility
phase or its center/global sequence.

Historical audit pins (not the current build configuration): Lean `4.34.0-rc2`, mathlib
`30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, TauCeti
`355c248fa848acd70c2a4b412ca5f53d37b0402a`.

## 7. Sources and verification

The versions and build counts below belong to this audit checkpoint. For the
current checked source, use the [baseline entry point](../../proof-program-context/interface-checkpoint.md#checked-baseline).

### Verification

The pinned carrier/root-subgroup modules built successfully (3728 jobs).
The persistent audit built successfully (3843 jobs) and checked all 38 listed
declarations using `Lean.collectAxioms`. Every reported axiom is one of
`propext`, `Classical.choice`, and `Quot.sound`; the file fails on any other
axiom. Its examples check the concrete complex-point and rational/complex
Killing APIs. The audit module has no warnings.

Full regression also passed: **5395 jobs, 2050 axiom reports** (2049
axiom-list reports plus one axiom-free report), standard axioms only.
Unrelated existing linter warnings are unchanged. The larger job count
includes newly reached pinned algebraic-geometry/Geck dependencies; no new
package was added. Disposable logs are `.lake/e6-0-audit.log` and
`.lake/e6-0-full-build.log`; the source audit and this record are tracked.

The audit is imported by `GUT.lean` for normal regression. Reproduction:

```sh
lake build Math.LieGroups.E6.Audit.AuditMinusculeCarrier
lake build
```

### Mathematical References

- [Britto, A Mathematical Construction of an E6 Grand Unified Theory, chapter 3](https://arxiv.org/html/2102.13465v1):
  a source for the compact group, finite central quotient and branching targets;
  not an imported Lean bridge.
- [Bernardoni, Cacciatori, Cerchiai, Scotti, Mapping the geometry of the E6 group](https://arxiv.org/abs/0710.0356):
  a concrete compact construction to compare with the minuscule route,
  not a formal library implementation.

The approved [ambient-group roadmap](../../self-dual-chirality/plans/SELF_DUAL_AND_AMBIENT_GROUP_PLAN.md)
continues to determine the final acceptance criteria.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

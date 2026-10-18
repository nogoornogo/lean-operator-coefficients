# Self-dual chirality and further ambient groups

Archived checkpoint; not a current work queue. Consult the current topic records.

Updated: stage 01

## Status and Scope

**DUAL-1/2, SP-1/2, and SPIN-1/2 are LEAN-CHECKED. E6-0 is complete as a
feasibility audit. Proofs through E6-0p are preserved; E6-0q and further
center/simple-connectedness/global-form construction are DEFERRED by user
decision. E6 physical endpoints remain TARGET, not proved.**
The [endpoint-first plan](../../e6-global-topology/plans/E6_ENDPOINT_PLAN.md) supersedes the automatic
continuation of E6 foundations below. Focus on the minimal actual
SU(5)-chain bridge needed by the existing selection-rule theorem; do not
make completion of all E6 mathematics the audit's exit condition. See the
[E6 feasibility dossier](../../e6-global-topology/decisions/E6_FEASIBILITY.md),
[compact symplectic result](../../../proof/current/applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md),
[checked scope](../../../proof/current/applications/Physics/SELF_DUAL_CHIRALITY.md) and
[declaration record](../../../proof/current/inputs/Math/interfaces/self-dual-chirality.md).
This roadmap follows the completed [standard SU(5) chain](../../standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md).
Its starting baseline is `checkpoint 01`, tagged
`standard-sun-chain-complete-stage 01`. Dependencies and toolchain remain pinned.

There are two separate objectives:

1. **Chirality obstruction:** a self-dual gauge source, restricted to an
   unbroken subgroup and equipped with an invariant complex-bilinear
   symmetric mass, cannot have the specified nonzero SM dual light index.
2. **Selection-rule obstruction:** connect actual compact Spin(10), then
   E6, to the existing theorem for the chosen SM -> SU(5) -> G chain.

The first excludes a specified spectrum in a finite-dimensional linear
mass model. The second excludes complete ordinary Abelian protection of
the supported Delta B = 1 signatures under the existing target hypotheses.
Neither asserts a nonzero coupling, amplitude, finite proton lifetime,
exact SM vacuum, or a classification of all SM embeddings. Finite Abelian
residual groups remain included. Non-Abelian residual protection and
strongly coupled/composite realizations are not added to the scope.

## Reuse and Remaining Bridges

The following project results are already available:

- [Character restriction](../../../../Math/RepresentationTheory/Characters/CharacterRestriction.lean):
  trace invariance under an actual ambient conjugation, including finite
  virtual characters. No source Laurent realization is required.
- [Symmetric mass index](../../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean):
  `radical_dual_character_eq` preserves the dual character difference
  between the source and its mass radical.
- [Finite charge profiles](../../../../Physics/StandardModel/Spectrum/FiniteChargeProfiles.lean)
  and [SM dual coefficients](../../../../Physics/StandardModel/Spectrum/ProfileChiralIndex.lean):
  forgetting charges sums multiplicities, and oriented SM weights are
  separated from their negatives and from singlets.
- [Ambient standard chain](../../../../GUT/Common/StandardChain/StandardChain.lean):
  the core already accepts an arbitrary group G and a supplied SU(5)
  homomorphism. `ContinuousModel` additionally requires injectivity,
  continuity, and a continuous product action. A trivial homomorphism
  alone is not a physical embedding or an inhabited positive-target model.

Source inspection at the pinned TauCeti revision
`355c248fa848acd70c2a4b412ca5f53d37b0402a` found these candidates. That initial
inspection was not a compilation or transitive axiom audit of the candidate modules;
the later E6-0 verification is recorded in the focused dossier:

| TauCeti module (under `TauCeti/`) | Available ingredient | Still to establish for this project |
| --- | --- | --- |
| `Algebra/Lie/HighestWeight/Dual.lean` | `nonempty_lieModuleEquiv_dual_iff` | Its application to actual continuous compact-group representations |
| `RepresentationTheory/ClassicalGroups/Symplectic.lean` | Self-duality of the defining symplectic representation | All source representations of compact USp(2n), not just the defining one |
| `RepresentationTheory/SU2/TorusConjugacy.lean` | Concrete conjugacy to a torus and inversion | Useful small control, not an SM-compatible GUT example |
| `Topology/Algebra/CliffordAlgebra/Spin/{Basic,Compact,Covering}.lean` | Topology, compact real Spin groups, double-cover infrastructure | A continuous injective SU(5) inclusion in compact Spin(10) |
| `RepresentationTheory/Spin/{HalfSpin,Dimension}.lean` | Group half-spin actions and dimensions | Compact-real to complex-spinor transport, unitarity, and SU(5) branching |
| `Algebra/Lie/E6/Minuscule/{Basic,GroupScheme,RootDatum}.lean` | A 27-dimensional Serre representation and algebraic carrier data | Identification with the desired compact E6 and its Spin(10) inclusion |

In particular, an algebraic E6 carrier is not automatically the compact
real Lie group used in the physical statement. The inspected root-datum
module explicitly limits its identification claims. Do not rename such
a carrier as the required group without proving the missing connection.

## Ordered Milestones

### DUAL-1: Shared Zero-Index Theorems

Prove that a supplied equivariant self-duality of a finite-dimensional
complex representation survives restriction at the character level.
Combine it with `radical_dual_character_eq` to obtain a zero dual index
for every invariant symmetric mass on the unbroken subgroup.

Also expose the weaker sufficient input: for the tested subgroup or torus,
each image element is conjugate in the ambient group to its inverse. A
single explicit normalizer element implementing inversion is a convenient
special case. This proves character equality directly, without constructing
an irreducible decomposition or a self-duality isomorphism for every source.

Acceptance: general theorems with no assumed zero radical index, positive
controls with zero and nonzero invariant mass, and a non-self-dual U(1)
character control showing why the extra hypothesis matters. Do not assert
that zero index implies a zero radical or that every pseudoreal field
admits a nondegenerate symmetric mass. Finite signed source-character sums
may have a companion lemma, but physical masses act on actual vector spaces.

### DUAL-2: Contradiction with the Positive SM Target

Prove that the charge-forgotten dual target for a positive SM profile family
is nonzero. Use a separated oriented SM weight with coefficient equal to
the common positive generation total; singlets and duals cannot cancel it.
Connect this to DUAL-1 and the current exact dual radical target interface.

Gauge-source self-duality need not hold as a representation of gauge times
residual symmetry. Restrict the mass and representation to the gauge action
and evaluate residual characters at the identity, equivalently summing
their coefficients. Do not infer that each charge-resolved index vanishes.

Acceptance: a no-target theorem for the declared linear mass model,
including arbitrary finite charge supports and torsion charges. Audit a
ZMod 2 charge example, the zero-generation boundary (no contradiction),
singlets, and added vectorlike pairs. A zero index on the physical SM torus
must be related to the faithful target evaluator, not assumed to be a
coefficient equality. No hypothesis about proton operator support is needed.

### SP-1: Actual Compact Symplectic Torus

First perform a bounded API/axiom audit (0.5-1 workday within this milestone).
Choose an actual compact USp(2n) model compatible with existing matrix
symplectic and unitary APIs. Distinguish it from Sp(2n, R) and the full
complex algebraic symplectic group.

Construct the standard torus `diag(z_1,...,z_n,z_1^-1,...,z_n^-1)` and an
actual group element implementing inversion. Instantiate DUAL-1 for
arbitrary finite-dimensional source representations on this torus, not
just tensor samples of the defining representation. Where a chosen SM
embedding is used, supply its torus factorization and the target evaluator
compatibility needed by DUAL-2.

Acceptance: actual group membership, torus homomorphism, continuity and
normalizer equation, with the exact scope of any SM specialization stated.
A theorem for the chosen torus is an independent milestone; it is not yet
the claim about every possible SM embedding into USp(2n).

### SP-2: Arbitrary Symplectic Restrictions

**Completed:** the [spectral proof](../../../proof/current/applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md#sp-2-spectral-foundation)
constructs a complete paired orthonormal eigenbasis using a maximal finite
frame and its invariant orthogonal complement. The change-of-basis matrix
is proved symplectic, giving actual torus conjugacy and arbitrary-element
inverse conjugacy. DUAL-1/2 now apply to arbitrary subgroup restrictions.
The original acceptance criteria below are retained for traceability.

Prove conjugacy to the chosen torus, or an equivalent pointwise
conjugate-to-inverse theorem, for all elements of compact USp(2n). Deduce
zero gauge dual index for arbitrary subgroup restrictions and the DUAL-2
obstruction whenever an exact positive SM target is supplied.

Acceptance: no unproved torus-conjugacy or all-representations-self-duality
certificate remains. A highest-weight route is an alternative only if the
compact-group/Lie-algebra bridge is actually available. If this requires
new general compact Lie theory, record it as pending and proceed with the
independent Spin(10) branch; do not weaken the theorem silently.

### SPIN-1: Compact Spin(10) Standard Chain

The [SPIN-1a/b/c/d foundation](../../../proof/current/applications/GUT/SPIN_STANDARD_CHAIN.md) is now checked: actual
compact real carrier/double cover, realification SU(n) -> SO(2n), and
unique continuous homomorphic lifting under explicit source-topology
conditions. SU(n) local path-connectedness and the topological identification
of the last-vector stabilizer with SU(n-1) are now proved. Explicit local
sections give an open local product atlas over the entire complex unit
sphere for rank at least two. Two-open-set gluing now proves SU(n)
simple-connectedness in every rank. `CompactSpin.SU5Inclusion` now uses these
proofs to give an unconditional continuous injective closed embedding in
compact Spin(10), uniquely lifting the actual realification map. The shared
standard-chain theorem and its continuous/scalar-family wrappers are
specialized with the physical model inputs unchanged. **SPIN-1 is checked**;
the actual half-spin model is still the separate SPIN-2 acceptance gate.

Original acceptance gate (now met): after a bounded API/axiom audit, fix
the compact real Spin(10) carrier. Construct SU(5) -> Spin(10), for example
by realifying its defining action into SO(10) and proving the required
lift through the double cover, or by an equivalent explicit construction.
An SO(10) map or a Lie-algebra map alone is not the desired inclusion.

Prove injectivity and continuity, then specialize `StandardChain` and its
continuous wrapper. The selection-rule argument itself is already proved.
Acceptance: the actual inclusion is constructed, and the resulting theorem
lists the unchanged mass, residual action, and dual target assumptions.

### SPIN-2: Actual Spinor Model

**SPIN-2a is checked:** the [compact half-spin construction](../../../proof/current/applications/GUT/SPIN_HALF_SPIN.md)
restricts a real-to-complex even Clifford map to the actual compact Spin
carrier. The even module has dimension 16, has continuous coefficients,
and admits an equivalent continuous unitary model. The central element
`-1` acts as `-Id`, and the representation does not descend to SO(10).
**SPIN-2b is also checked at character level:** the actual lifted action
equals the exterior action and has character `1 + 10 + bar5` on every
SU(5) element. This transfers to the unitary model, with singlet cancellation
in its dual index. No branching certificate is assumed.
**SPIN-2c is checked:** `HalfSpinBenchmark` derives the positive target from
actual traces and constructs a continuous zero-mass model with trivial
residual action. Faithful evaluation proves its full torus/residual spectrum
is one SM generation plus one neutral singlet. All 15 SM weights have
positive dual index and actual nonzero radical witnesses; the common
selection-rule theorem applies. Finite Z/3 and Circle inhabitants are audited.

Full acceptance goal (now met): construct the complex 16-dimensional half-spin representation of the chosen
compact group, with continuous unitary action. Establish the SU(5)
restriction `16 = 10 + bar5 + 1`, with conjugation/orientation conventions
explicit, and connect it to the existing positive-target model.

Acceptance: an actual inhabited continuous model, not a supplied branching
or light-target certificate. A trivial residual action and zero invariant
mass are the checked first controls; neither proves a realistic vacuum or
that unwanted modes dynamically become massive. More elaborate mass and
charge benchmarks are separate additions, not prerequisites for SPIN-1.

### E6-0: Compact E6 Feasibility Gate

**Completed as an audit, not a compact E6 theorem.** The persistent check
compiles 38 selected declarations with only the three standard axioms.
The [dossier](../../e6-global-topology/decisions/E6_FEASIBILITY.md) distinguishes actual algebraic ingredients
from missing Lie-algebra descent, compact/global identification, Spin inclusion,
and continuous branching. Full E6-1 is not a ready library specialization.

Audit the pinned E6 carrier, real-form/topology APIs, candidate subgroup
maps, and transitive axioms. Determine exactly which parts of compact E6,
Spin(10) inclusion, and the continuous 27 representation are available.
Produce an explicit missing-lemma list and revise E6 effort estimates.
This gate must not turn into an unbounded foundational implementation.

**Closure decision after E6-0p:** it did expand into substantial additional
proofs. Preserve them, but close the audit now with the recorded missing
bridges and uncertain global cost. Neither E6-0q nor full E6-1 is needed to
complete E6-0. The completed checkpoints below are records, not permission
to append another foundational milestone. Reopening deferred work requires
an endpoint dependency, bounded plan and explicit user approval.

### E6-0b: Bounded Matrix Prototype

**Completed within the bounded scope.** Adjoint/traceless generator equations,
SU(27) exponentials and actual invariant D5 coordinate blocks are checked.
The finite Lie-basis candidate is external, not a formal dimension theorem.
The [matrix dossier](../../../proof/current/inputs/GUT/E6_MATRIX_PROTOTYPE.md) specifies the still-open
compact-carrier acceptance contract and proposes bounded E6-0c certificate
verification before any general compact-group foundation work.

Check adjoint/compact-generator equations using the existing 27 matrices;
assess a finite Lie-basis/root-space and D5-restriction certificate. External
exact computation may generate candidates, but Lean must check the claimed
mathematics. Specify the missing compact-carrier identification contract.
Do not count a dimension, a weight table or the closure of a generated
subgroup as that identification. Review the foundation cost before expanding
into general integration or reductive-group classification.

### E6-0c: Finite Matrix Lie Certificate

**Completed within the bounded scope.** The actual generated matrix Lie
subalgebras have proved dimensions 78/45, with checked spanning sets,
linear independence, and injective matrix D5 inclusion over characteristic-zero
fields. The reusable checker proves soundness and uses kernel reduction for
the concrete witnesses. See the [finite certificate](../../../proof/current/inputs/Math/E6_LIE_CERTIFICATE.md).

### E6-0d: Generator-Preserving Geck Comparison

**Completed at the Lie-algebra level.** The actual E6/D5 matrix algebras
are Lie-isomorphic to the scalar-extended pinned Geck carriers over
algebraically closed characteristic-zero fields. The faithful 27 matrix
actions and D5 inclusion preserve all numbered generators. Matching
Cartan bases, target simplicity, and a proper-product theorem supply the
structure beyond dimension equality. See the [comparison](../../../proof/current/inputs/Math/E6_GECK_COMPARISON.md).

### E6-0e: Actual Skew-Hermitian Real Forms

**Completed at the real Lie-algebra level.** The actual matrix real forms
have dimensions 78/45, complexify to the pinned Geck carriers, and carry
an injective real D5 inclusion compatible with the complex inclusion.
Every real-form element exponentiates into SU(27). See the
[real-form proof and pinned global-API review](../../../proof/current/inputs/Math/E6_COMPACT_REAL_FORM.md).

### E6-0f: Scalar Commutant and Lie Normalizer

**Completed algebraically.** Distinct weights and kernel-checked raising
paths force the commutant of the actual E6 generators to be scalar.
Mathlib's inner-derivation theorem then proves that the trace-zero complex
normalizer is exactly the E6 matrix algebra, and that no extra traceless
skew-Hermitian directions normalize its real form. See the
[normalizer proof and negative controls](../../../proof/current/inputs/Math/E6_MATRIX_NORMALIZER.md).

### E6-0g: Closed Compact Matrix Normalizer

**Completed at matrix/topological-group level.** The actual SU(27)
normalizer is closed and compact, and its all-real-time exponential
directions are exactly the 78-dimensional real form. The proof combines
the algebraic bound with TauCeti's commutator exponential and a derivative
argument; a time-one negative control is checked. See the
[compact normalizer record](../../../proof/current/inputs/Math/E6_COMPACT_NORMALIZER.md).

### E6-0h: Connected Candidate and Scalar Center

**Completed as a bounded audit.** The closed compact identity component
is connected and retains the exact all-time exponential criterion. The
full normalizer has a central element of exact order 27, excluding any
order-three-center identification of that full group. The component's
center is not determined. Ambient matrix log/exp inverse identities are
compiled; subgroup chart/global APIs are separately source-inspected. See
the [component and global-form record](../../../proof/current/inputs/Math/E6_IDENTITY_COMPONENT.md).

### E6-0i: Local Logarithm and Exponential Generation

**Completed at the matrix/topological-group level.** The actual matrix
logarithm of nearby normalizer elements lies in the real form and
exponentiates back to them. Positive radii are derived. The identity
component is open and equals the algebraic subgroup generated by real-form
exponentials; the unrestricted time-one converse is still refuted. See
the [local-logarithm record](../../../proof/current/inputs/Math/E6_LOCAL_LOG.md).

### E6-0j: Actual Local Exponential Chart

**Completed.** The checked local inverse laws give an open partial
homeomorphism with zero/one in its source/target, actual exponential as
forward map and actual ambient logarithm on the entire target. The
logarithm is analytic there. See the [local-chart record](../../../proof/current/inputs/Math/E6_LOCAL_CHART.md).

### E6-0k: Translated Smooth Atlas

**Completed.** Translation covers the connected compact candidate;
analytic transition formulas give a smooth manifold instance on its
existing topology. The ambient exponential derivative at zero equals the
real-form inclusion. See the [smooth-atlas record](../../../proof/current/inputs/Math/E6_SMOOTH_ATLAS.md).

### E6-0l: Smooth Group Operations

**Completed.** The matrix inclusion is smooth and injective; actual matrix
multiplication and star give smooth multiplication and inversion on the
atlas. The candidate is now a checked connected compact Lie group. See
the [Lie-group record](../../../proof/current/inputs/Math/E6_CANDIDATE_LIE_GROUP.md).

### E6-0m: Exact Tangent Image

**Completed at the linear level.** The actual inclusion's identity
differential is injective with real-form image. The pinned Lie functor
and units bracket theorem are kernel-audited prospective ingredients.
See the [tangent-image record](../../../proof/current/inputs/Math/E6_TANGENT_IMAGE.md).

### E6-0n: Geometric Tangent Lie Algebra

**Completed.** The actual units inclusion, audited Lie functor and units
commutator identify the geometric tangent Lie algebra with the existing
E6 real form. The invariant-vector-field bracket is explicitly checked.
See the [tangent Lie-algebra record](../../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md).

**E6-0o** completed the [global-form feasibility audit](../../e6-global-topology/decisions/E6_GLOBAL_FORM_AUDIT.md).
**E6-0p** proved the [component scalar-center upper bound](../../../proof/current/inputs/Math/E6_COMPACT_CENTER.md).
The proposed E6-0q lower bound and subsequent global work are now deferred.
The global part of M2 and M3-M5 remain mathematically open, not unfinished
conditions for closing the audit.

### E6-1 and E6-2: Inclusion and Actual Model

**Deferred original construction route.** The goals remain unproved, but
are not an automatic queue. The [endpoint-first plan](../../e6-global-topology/plans/E6_ENDPOINT_PLAN.md)
tests a bounded direct SU(5) bridge before any new foundational project.
The original requirements below describe the full Spin-based realization,
not additional inputs to the already proved common selection-rule theorem.

Conditional on E6-0, construct a justified compact E6 carrier and a
continuous injective Spin(10) inclusion, then compose the SU(5) chain.
Handle finite centers explicitly: the larger subgroup is
`(Spin(10) x U(1))/Z4`, not an unqualified direct product.

Separately construct a continuous unitary 27 and verify its restriction
`27 = 16 + 10 + 1`. Connect the resulting SM dual index to the common
theorem, including singlets and vectorlike contributions. Start with a
trivial residual action: a pair that is vectorlike for the gauge group
need not cancel charge by charge for a nontrivial residual action.

Acceptance: distinguish the conditional chain specialization (E6-1) from
the actual model inhabitant (E6-2). Do not use an arbitrary group with an
assumed Spin(10) inclusion as a substitute for constructing compact E6.

## Effort Estimate and Gates

The initial estimates below are historical, not a renewed authorization
or a remaining-work forecast. E6-0 has ended; the [new plan](../../e6-global-topology/plans/E6_ENDPOINT_PLAN.md)
and [endpoint/stop gate](../../../architecture/WORKFLOW.md#endpoint-and-stop-gate) control
future work. No end-to-end E6 completion date has been established.

These are engineering planning ranges from source inspection, not timed
proof prototypes, deadlines, or usage/credit estimates. One workday means
roughly 6-8 hours of focused proof development; access limits, large cold
dependency builds, and external reviews add elapsed time. Targeted checks,
normal regression, documentation, and a milestone commit are included.
Ranges are incremental, assuming preceding prerequisites are available.

| Milestone | Initial effort | Estimate confidence / principal risk |
| --- | --- | --- |
| DUAL-1 | 0.5-2 workdays | Relatively high; mostly existing character and mass APIs |
| DUAL-2 | 1-3 workdays | Medium-high; gauge-only evaluation and target nonvanishing |
| SP-1 | 2-6 workdays | Medium; compact carrier and concrete matrix identities |
| SP-2 | 5-15+ workdays | Low; symplectic torus conjugacy / spectral decomposition |
| SPIN-1 | 5-15 workdays | Low-medium; continuous double-cover lift and global identification |
| SPIN-2 | 3-10 workdays | Low-medium; compact-real/complex transport and actual branching |
| E6-0 | 1-3 workdays | Bounded audit, not an E6 formalization estimate |
| E6-0b | 1-3 workdays | Bounded matrix prototype and compact-carrier contract, not completion of E6-1 |
| E6-1 | Re-estimate after E6-0b | E6-0 did not validate the old provisional 15-40+ workdays; the compact/global bridge remains the principal risk |
| E6-2 | Provisional 5-15+ workdays | Very low; depends on E6-1 and actual 27 APIs |

The recommended first checkpoint is **DUAL-1 + DUAL-2**, roughly **2-5
workdays**. It gives a reusable, explicitly conditional chirality theorem
without requiring any new compact-group classification. SP-1 gives the
next concrete family-level torus result. SPIN-1 + SPIN-2 is a separate
roughly 8-25 workday project once its prerequisites are accessible.

Do not sum the whole table into a promised completion date. E6 is currently
a weeks-to-months research risk; if its foundations are missing, E6-0 must
produce a separate plan rather than treating 40 days as an upper bound.
Likewise, all-Dynkin-type self-duality and all global forms are deferred,
unpriced extensions, not prerequisites for these milestones.

At each gate, continue autonomously within the agreed mathematical scope.
Report a counterexample, a changed conclusion, a necessary new physical
assumption, or a major foundational/dependency expansion before adopting it.
An API obstacle alone is not permission to replace a bridge by an axiom.

## Implementation and Verification Policy

Keep the generic additions under `Math/RepresentationTheory/`,
`Physics/FieldTheory/`, and `Physics/StandardModel/`; put concrete adapters under
group-specific directories only once their carriers are fixed. Preserve
existing imports, theorem statements, SU(6) flipped results, and the
standard SU(N) family. No dependency upgrade or upstream submission is
part of this plan, and the local LLM remains disabled.

For each proof milestone: compile targeted modules and persistent audits,
inspect `#print axioms` for new endpoints, run full `lake build`, and reject
`sorryAx`, new opaque assumptions, or nonstandard axioms. The accepted
baseline axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Update the focused dossier, move completed items from ACTIVE to COMPLETED,
record the actual verification, and commit by theme. Never label a
documentation-only plan or a library source inspection as a proof build.

## Mathematical References

- [Etingof, Lie Groups and Lie Algebras, section 33.2](https://math.mit.edu/~etingof/lnlg.pdf):
  dual highest weights and the self-dual types; compact-group application
  still requires its own formal bridge.
- [Baez and Huerta, The Algebra of Grand Unified Theories](https://arxiv.org/abs/0904.1556):
  the SU(5)/Spin(10) chain and spinor realization.
- [Britto, A Mathematical Construction of an E6 Grand Unified Theory](https://arxiv.org/abs/2102.13465):
  compact E6 construction and the finite central quotient in its subgroup.

These references justify mathematical targets, not imported Lean proofs.

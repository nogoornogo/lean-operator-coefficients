# Coefficient-program checkpoint

The accumulated sector statements below describe earlier proof checkpoints.
Their "current", "now" and "latest" wording is local to those checkpoints;
this is not the maintained project overview. Branch names are provenance,
not required tooling. Use the [current result guide](../../proof/current/RESULTS_AND_SCOPE.md)
for the present endpoints. Retention does not renew any build or scope claim.

# Sector statements

## Classified Dossiers

- [Mathematical foundations](../../proof/current/inputs/README.md).
- [General physics and Standard Model interfaces](../../proof/current/applications/README.md).
- [GUT applications and model-specific boundaries](../../proof/current/applications/README.md).
- [Common document and citation conventions](../../proof/TEMPLATE.md).
- [Individual external-reference review](../../proof/REFERENCE_REVIEW.md).
- [Archived plans and checkpoint reviews](plans/README.md).

The dashboard below remains a cross-domain navigation aid, not a universal
theorem. The [assumptions index](../../proof/ASSUMPTIONS.md) links the Math, Physics and
GUT ledgers; its legacy section anchors remain navigation-compatible.

This file is the short proof dashboard. Detailed arguments, historical notes,
and audit trails live in the linked dossiers under `docs/proof/`.

## Current theorem scope

The [qque coefficient classification](../qque-coefficient-completeness/results.md)
proves a linear equivalence between the independently specified degree-(2,1,1)
invariant exterior sector and `Hom_H(Sym^2 V_Q, V_uc tensor V_ec)`.
Gauge and spinor uniqueness, surjectivity and transport through actual-field
identifications are proved. This is a necessary-and-sufficient test for the
fixed derivative-free qque sector, not all baryon-violating operators.
The existing source theorems below remain sufficient-condition routes into
that sector; their compactness, spectrum and conjugation hypotheses are not
silently removed by the classification.

Latest local-target refinement: [four-weight qque](../../proof/current/applications/Physics/FOUR_WEIGHT_QQUE.md) retains
actual light support (Abelian) and nonzero ordered internal coefficients
(finite non-Abelian), requiring matching only at weights 0, 3, 8, 14. The
two-conjugation pair result still uses its fifteen-weight target.

The [compact continuous extension](../../proof/current/applications/Physics/COMPACT_LIGHT_QQUE.md) now supplies the same
qque internal coefficient for compact H without finiteness or commutativity,
assuming continuity of the residual source action and of the nonzero Q target.
The finite pair result is retained; no compact duql endpoint is claimed here.

The [explicit SM x H adapter](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md) combines this
coefficient with the full SM gauge tensor, conditional on compatible
decompositions of actual light fields. It proves a nonzero ordered internal
SM x H functional, not Lorentz/Grassmann nonvanishing or automatic full-SM
decomposition of an arbitrary radical.

The [spinor/exterior extension](../../proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md) closes the algebraic
Lorentz-spinor/fermionic-alternation step under those same explicit-decomposition
inputs: a qque coefficient has nonzero descent to the fourth exterior power of
the sum of actual participating light fields, invariant under SM-cover x H x
SL(2,C). It does not assert generation of that interaction or a decay amplitude.

The [species-index connection](../full-sm-light-bridge/implementation.md)
derives those actual field identifications from a compatible continuous
SM-cover x H action on the radical and three species indices, alongside the
four-weight conditions. It proves nonzero alternating descent without a
supplied decomposition, common quotient or splitting. This alternative input
package does not turn torus data alone into a full-SM action or spectrum.

The [exact-spectrum entry](../exact-sm-spectrum-qque/results.md) derives
both the species and four-weight inputs from an SM-only equivalence of the
actual radical with n > 0 full generations plus singlets. Its residual targets
and their actions are extracted, not supplied. This is a spectrally narrower
application theorem retaining the same compatible action and conjugations.

The [signed virtual-index entry](../virtual-index-qque/results.md)
permits negative coefficients in a supplied finite normalized irreducible
presentation, with positive total Q dimension. Common split quotients and
the actual-field exterior coefficient are derived from character-index
matching. That interface retains supplied normal forms; the automatic species
entry below constructs them. No end-to-end signed GUT example is supplied.

The [shared-positive-constituent entry](../shared-positive-qque/results.md)
requires only one strictly positive irreducible coefficient in each of the
three species indices. Whole-index equality and positive total dimension are
unnecessary. With the compatible continuous action and actual species-index
equations, it derives the same actual-field exterior conclusion without
separate torus matching or conjugation premises. The old common-index package
is proved to imply this sufficient condition.

The [pairwise-positive entry](../pairwise-positive-qque/results.md)
further allows Q/up and Q/e to share different positive constituents. The
two-pair coefficient is symmetrized and its actual-field exterior descent
is proved nonzero. Compact continuity and normalized species character
equations remain inputs; no new ambient-GUT source is exhibited.

The [automatic species-index entry](../normalized-virtual-presentation/results.md)
constructs a normalized finite irreducible family and signed profiles from
actual multiplicity representations, proving their character-index equations.
It retains compactness, compatible continuity and pairwise positive support
of the constructed indices. It is noncomputable, not a classification program.

The intended final theorem concerns exact proton protection by an unbroken
ordinary **Abelian** internal symmetry whose unitary matter action commutes
exactly with the full ultraviolet `SU(6)` action.  Its low-energy hypothesis is
equality of the exact massless chiral index with Standard Model generations
plus gauge singlets, not equality of the complete zero-mode spectrum.  The
checked physical-model adapters cover both the Dirac/Yukawa class and a
finite-dimensional all-left-handed symmetric linearized mass class with an
explicit **dual** light-index target. The latter includes continuous geometry
and general cocharacters. Its newer wrappers also accept jointly continuous
equivariant scalar-dependent mass families and finite nonnegative SM charge
profiles with common positive total. Scalar-linearity and a single charge
per species are no longer required; the profile equalities and actual
radical support are derived from the source and its exact dual target.
The old negative-generation conclusions and signed Dirac-index endpoints
remain separate. General Lagrangian
semantics and realistic flavor/CKM reconstruction are not established. See
[current assumptions and relaxations](../../proof/ASSUMPTIONS.md) and the
[physical model boundary](../../proof/current/applications/GUT/MODEL_INTERFACE.md).  The theorem does not
cover general non-Abelian finite symmetries at the same full physical endpoint;
a separate [finite-group internal-coefficient theorem](../nonabelian-light-source/results.md)
is checked. It does not cover gauge-twisted or
gauge-normalizing Abelian actions, R symmetries, generalized symmetries, or
non-invertible symmetries.

The three obstruction mechanisms are logically separate:

1. The standard-branch route is `charge-orbit bridge -> operator neutrality`; it includes finite Abelian charge
   groups and is the intended main route.
2. The continuous `U(1)` anomaly factorization is an auxiliary
   cross-check only.
3. The flipped Weyl obstruction is an independent representation-theoretic
   argument using the ambient Weyl element `(3 6)`.

The Dirac-type model-class theorem and its charge-orbit source adapter are Lean-checked.
A concrete one-generation benchmark now proves non-vacuity of the full model
interface for every Abelian group acting trivially on matter. Its mass and
Yukawa data are zero, so vectorlike zero modes are not removed. An exact
SM-only full zero-mode spectrum is not claimed for that Dirac benchmark.
The separate symmetric-mass extension is described below. Semisimple embedding
classification and the finite-dimensional jointly continuous character-rigidity bridge are closed in their stated
scopes.

The concrete `6`, `bar6`, and `15` now have checked continuous-unitary
realizations equivalent to their existing algebraic weight certificates.
These provide the matter building blocks of `ConcreteDiracBenchmark.model`.
Their actual trace characters satisfy `15 + bar6 - 6 = 10 + bar5` on the
standard SU(5) torus. The match to the charge-resolved physical SM target is
now checked: the signed source has one generation and no net singlets, with
a uniform charge in any additive Abelian group. This is not equality of the
complete zero-mode spectrum. The benchmark constructs the strict residual
action, standard continuous geometry, and zero mass sector, and proves its
exact light chiral-index condition. Its persistent audit also regression-tests
the corrected representation fields described in the physical model dossier.
The off-diagonal Dirac bilinear on all-left-handed fields, its radical, and
the relation between its dual chiral difference and the signed Dirac index
are also checked. The general symmetric Weyl/Majorana foundation now proves
an invariant radical, a self-dual nondegenerate quotient, and conservation
of the dual chiral character. A checked order-two example shows why this
does not recover the full light spectrum or the signed Dirac index. The
dual SM target's oriented charge profiles and their standard charge-orbit bridge -> Abelian proton-operator neutrality connection are
now checked, including the conditional actual-mass/charged-source endpoint.
UV field/source identification is now derived for canonical fields with
nonnegative actual matter multiplicities. `StandardWeylModel` proves Abelian
proton-operator neutrality at the fixed standard branch, with its radical dual-SM target
explicit. Its one-generation non-vacuity witness is now constructed from
actual `15 + 2 bar6` with neutral action and zero mass, retaining 27 zero
modes. `WeylZeroModeSupport` now derives actual radical support at all fifteen
SM weights for positive generation index and constructs the existing
supported `qque`/`duql` operator-class witnesses without a UV support premise.
Negative indices yield conjugate zero modes and explicitly conjugated
operator signatures with inverted residual characters. For every nonzero
index one of the two orientations is supported and invariant; this does not
identify a negative-baryon-number signature with a positive one.
`ConcreteWeylNonzeroMass` constructs a nonzero rank-one symmetric mass on
the same matter, preserving the one-generation dual target with radical
dimension 26. `ConcreteWeylFullMass` now lifts all twelve extra modes on
that same matter: its radical has dimension 15 and its full actual character
is exactly one SM generation, with no extra singlets. The proved invariance
is under the physical torus times the neutral residual action, not a new
full non-Abelian gauge-tensor assertion.
The hypercharge character rigidity/standard charge-orbit bridge coefficient bridge now works with dual differences at arbitrary
integral cocharacters: the odd fifth moment fixes `(-2,3)`, and the same
charge-resolved dual target supplies standard charge-orbit bridge -> Abelian proton-operator neutrality, including finite Abelian
charges. `PhysicalWeylMassSource` now derives that target from actual canonical
fields and the mass radical. `ContinuousWeylModel` assembles semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality
and the actual supported-operator endpoint for the declared symmetric
linearized class. `ContinuousWeylBenchmark` supplies a one-generation
zero-mass inhabitant. `ContinuousWeylMassTransport` now preserves an existing
standard mass and its radical representation exactly along equality of the
canonical fields. `ContinuousWeylFullMass` therefore supplies a nonzero-mass
inhabitant with precisely the full 15-mode SM spectrum in that same continuous
interface. See the [precise model scope](../../proof/current/inputs/GUT/WEYL_MODEL.md).
`ContinuousWeylYukawaModel` now derives the symmetric mass from primitive
bare-mass, scalar-linear Yukawa, and invariant-vacuum data. A nonzero Yukawa
example preserves that exact 15-mode radical, and an independent invariant
tensor example uses the full SU(6) action. This does not yet realize the
proton operator as a full non-Abelian tensor on the radical; see the
[Yukawa and tensor boundary](../../proof/current/inputs/Physics/WEYL_YUKAWA.md).
`ContinuousWeylFamilyModel` drops scalar-linearity while preserving old masses
and spectra; `ContinuousProfileModel.ScalarModel` combines that extension
with positive family-dependent profiles. Its SU(5) compatibility and actual
two-charge SU(6) realizability gates are complete. These additions do not
turn the general radical-signature theorem into a full-gauge tensor or
nonzero-amplitude theorem; see [the profile endpoint](../../proof/current/applications/GUT/PROFILE_MODEL.md).
Nonzero ordered `qque`/`duql` tensors on the standard SM representations,
with full covering-gauge invariance and the Abelian proton-operator neutrality residual characters, are
now checked separately. The arbitrary-model full-gauge upgrade and fermionic
quotient remain separate; see [the tensor milestone](../../proof/current/applications/Physics/SM_GAUGE_TENSOR.md).
The [full-gauge mass benchmark](../../proof/current/applications/GUT/SM_GAUGE_MASS.md) now realizes
those tensors on the computed radical of a decomposed 27-dimensional
post-breaking representation and now pulls that mass and its tensors back
to the actual analytic SU(6) `15 + 2 bar6` direct-product representation,
with neutral residual action and an exact 15-dimensional SM radical.
The actual continuous covering-group map and its exact physical-torus
compatibility are checked, together with full-group `6`, `bar6`, and `15`
branching and the 27-field assembly. A proved torus/residual equivalence
now constructs a compatible continuous SU(6) extension on `ordinaryFields`.
The new continuous-model inhabitant retains this nonzero mass, complete SM
spectrum, and nonzero invariant ordered tensors on its actual radical.
No identification with an independently specified natural full charge-sector
action or with the older torus-eigenbasis mass is claimed;
see [the branching bridge](../../proof/current/inputs/GUT/SM_BRANCHING.md).
The same full-gauge mass now has a continuous-unitary full-SU(6)
scalar/Yukawa/VEV existence realization with zero bare mass. The universal
scalar space consists of symmetric bilinear forms; its selected VEV
reproduces the previously constructed mass exactly. This does not determine
a preferred Higgs sector, a scalar potential, or the full VEV stabilizer.
The [stabilizer audit](../../proof/current/inputs/GUT/SM_VACUUM_STABILIZER.md) now proves that
the current VEV's stabilizer is strictly larger than the SM image, using an
explicit signed color/weak exchange. This rules out an exact-SM vacuum
claim for this example, without altering the scoped assembly or the mass/radical results;
see [the scalar boundary](../../proof/current/inputs/Physics/WEYL_YUKAWA.md).
The reviewed `kilo` additions prove only conditional UV supported-operator
statements, with an explicit UV orbit-support assumption. They do not close
radical support by themselves. The new actual-spectrum lemmas supply that
missing bridge for positive index. The proposed nonzero-mass impossibility
argument used the wrong invariance group and is now formally refuted in the
current model interface; see the
[scope audit](../mass-profile-foundations/plans/MASS_SUPPORT_REVIEW.md).

## Proof responsibility dashboard

The [actual group-free counterexample](../group-independent-assumptions/spectrum-bridge.md)
now shows that the finite mass/SM-target assumptions alone, without the UV
unification/orbit inputs, do not force a neutral supported signature in the
specified dimension-six class. Its zero-mass 45-dimensional SM source has a
commuting order-three residual action. This is not a quantum-anomaly theorem
and does not change any of the scoped unification-group results below.

| Responsibility | Current status | Detailed dossier |
| --- | --- | --- |
| Self-dual source chirality | `LEAN-CHECKED` zero restricted/radical dual index and positive SM target exclusion after forgetting charges, including the actual standard-chain evaluator/model bridge | [Self-dual chirality](../../proof/current/applications/Physics/SELF_DUAL_CHIRALITY.md) |
| Compact symplectic chirality | `LEAN-CHECKED` actual USp(2n) all-element torus/inverse conjugacy; arbitrary subgroup restrictions of finite-dimensional sources have zero dual index for invariant symmetric masses. Excludes the positive exact SM target with its faithful evaluator; no SU(5) chain required | [Symplectic scope](../../proof/current/applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md) |
| Compact Spin standard chain | `LEAN-CHECKED` SPIN-1/2: actual continuous injective SU(5) -> compact Spin(10), with the common supported-signature theorem under unchanged general model inputs. The actual continuous unitary 16, all-SU(5) character `1 + 10 + bar5`, and positive-target continuous inhabitant are checked. Its zero mass and trivial residual action give one SM generation plus one neutral singlet, with actual supported modes; no realistic-mass or vacuum claim | [Spin scope](../../proof/current/applications/GUT/SPIN_STANDARD_CHAIN.md), [half-spin source](../../proof/current/applications/GUT/SPIN_HALF_SPIN.md) |
| Compact E6 extension | `LEAN-CHECKED` on `compactIdentityComponent`: actual SU(5) inclusion, continuous unitary 27, derived positive one-generation dual target and zero-mass/trivial-residual model with supported selection-rule conclusion. All 27 modes remain light; full-spectrum equality with the 17-dimensional SM-plus-singlets target is disproved. Named-E6 interpretation is now literature-assisted mathematics, not an unconditional Lean global identification | [Actual positive-target model](../../proof/current/applications/GUT/E6_POSITIVE_TARGET.md), [candidate-group map](../../proof/current/applications/GUT/E6_SU5_GROUP_MAP.md), [literature boundary](../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md) |
| E6 candidate global-form constraints | `LEAN-CHECKED` nonzero cubic invariant under the actual connected group; center exactly the cube roots of unity, of order three; non-descent of the actual 27 to the center quotient. The ambient order-27 scalar is outside the component, while its ninth power belongs. These facts alone do not prove simple connectedness; the conditional topology result is recorded below | [Exact center via cubic](../../proof/current/inputs/Math/E6_CUBIC_CENTER.md), [order-three element and quotient](../../proof/current/inputs/Math/E6_CENTER_THREE.md) |
| E6 candidate maximal torus | `LEAN-CHECKED` actual closed six-circle embedding, exact Cartan exponential kernel `2 pi Z^6`, reconstruction of all diagonal candidate elements and self-centralizer. The torus is maximal among Abelian subgroups. The geometric coroot/fundamental-group bridge is not proved | [Actual compact torus](../../proof/current/inputs/Math/E6_COMPACT_TORUS.md) |
| E6 candidate coroot loops | `LEAN-CHECKED` actual based null-homotopies of all six Cartan coordinate loops, with exact torus comparison and nonconstant-loop controls; extended to arbitrary torus loops below | [Actual loop contractions](../../proof/current/inputs/Math/E6_COROOT_LOOPS.md) |
| E6 candidate torus fundamental-group map | `LEAN-CHECKED` actual contractions of every identity-based torus loop in the candidate, including all integer windings; induced map `pi_1(T) -> pi_1(K)` is trivial. Unconditional surjectivity remains unformalized | [All torus loops](../../proof/current/inputs/Math/E6_TORUS_LOOPS.md) |
| E6 literature-assisted topology | `LEAN-CHECKED CONDITIONAL`: actual compact-Lie/maximal-torus inputs and exact map comparison; an explicit Proposition-38 input implies surjectivity and candidate simple connectedness. No custom axiom, placeholder or unconditional instance. Named-E6 interpretation additionally uses external compact-real-form classification and Lie correspondence | [Literature boundary](../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md), [current status](../e6-global-topology/checkpoints/e6-reviewed-status.md) |
| Semisimple embedding classification | `LEAN-CHECKED` for continuous injective `SU(3) x SU(2) -> SU(6)` homomorphisms with a nontrivial commuting continuous circle; differentiability is derived automatically | [Embedding classification](../../proof/current/inputs/Math/EMBEDDING_CLASSIFICATION.md) |
| Hypercharge centralizer geometry | `LEAN-CHECKED` for the actual centralizer, two-torus, real form, and cocharacter lattice | [Hypercharge centralizer](../../proof/current/inputs/Math/HYPERCHARGE_CENTRALIZER.md) |
| Bounded branching cross-check | `BOUNDED` plus `DERIVED-UNVERIFIED` evidence | [Branching cross-check](../../proof/current/applications/GUT/BRANCHING_CROSSCHECK.md) |
| Hypercharge character rigidity | Degree-five core and finite-dimensional jointly continuous actual-character bridge are `LEAN-CHECKED`; physical model assumptions enter at the charge-orbit and scoped-assembly layers | [Character rigidity](../../proof/current/applications/GUT/HYPERCHARGE_CHARACTER_RIGIDITY.md) |
| Standard charge-orbit bridge | Dirac and symmetric linearized mass adapters are `LEAN-CHECKED`, including canonical UV/source identification at general cocharacters | [Charge-orbit bridge](../../proof/current/applications/GUT/STANDARD_CHARGE_ORBIT_BRIDGE.md) |
| Abelian proton-operator neutrality | `LEAN-CHECKED` for arbitrary additive Abelian charge groups, conditional on standard charge-orbit bridge | [Abelian proton-operator neutrality](../../proof/current/applications/Physics/ABELIAN_PROTON_OPERATOR.md) |
| Continuous U(1) anomaly cross-check | `LEAN-CHECKED` continuous/family-universal anomaly cross-check; not the main proof | [Anomaly cross-check](../../proof/current/applications/Physics/CONTINUOUS_ANOMALY_CROSSCHECK.md) |
| Historical standard-branch route | Historical route; unused claims remain unverified | [Historical route](../standard-chain-foundations/plans/HISTORICAL_STANDARD_ROUTE.md) |
| Flipped Weyl obstruction | `LEAN-CHECKED` at the finite-virtual character level; conventional Grothendieck packaging remains | [Flipped obstruction](../../proof/current/applications/GUT/FLIPPED_WEYL_OBSTRUCTION.md) |
| Scoped physical-model assembly | `LEAN-CHECKED` for the declared Dirac/Yukawa and symmetric linearized mass classes, with continuous geometry, actual non-vacuity witnesses, and explicit index conventions | [Scoped assembly](../../proof/current/applications/GUT/SCOPED_NO_GO_THEOREM.md), [Weyl model](../../proof/current/inputs/GUT/WEYL_MODEL.md) |
| SU(5) retained-matter selection rule | `LEAN-CHECKED` for positive copies of actual 10 + bar5 and any commuting unitary Abelian action; supported neutral signatures and nonzero ordered internal tensors on the exact SM quotient | [SU(5) theorem](../../proof/current/applications/GUT/SU5_SELECTION_RULE.md) |
| Georgi-Glashow exterior benchmark | `LEAN-CHECKED` actual n(10 + bar5), zero mass, n > 0, continuous compact unitary centralizer action; derived positive support and nonzero actual qque exterior coefficient, without Abelianity. One- and three-generation controls; no vacuum/Yukawa/dynamics claim | [Source and scope](../../proof/current/applications/GUT/GEORGI_GLASHOW_QQUE.md) |
| Balanced species extensions | `LEAN-CHECKED` H-equivariant balanced multiplicity decompositions relative to an exact-SM reference derive positive support and actual qque exterior descent; not an automatic global vectorlike decomposition | [Statement and boundary](../../proof/current/applications/Physics/BALANCED_SPECIES_EXTENSION.md) |
| Full vectorlike spectrum | `LEAN-CHECKED` a global SM x H decomposition K = K0 + X + X.dual derives multiplicity certificates, positive support and actual exterior qque. A nonzero-extra SU(5) control is proved outside the old exact-spectrum entrance | [Inputs and results](../../proof/current/inputs/Physics/VECTORLIKE_SPECTRUM.md) |
| Scalar-dependent mass families | `LEAN-CHECKED` arbitrary-group evaluation, finite multilinear sources with mixed/conjugate slots, joint continuity, and a scoped SU(6) model adapter preserving the exact-index hypothesis; old linear models and a nonlinear nonzero benchmark are recovered exactly | [Mass families](../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md), [Model endpoint](../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md) |
| Finite family-dependent charge profiles | `LEAN-CHECKED` positive-orientation continuous SU(6) model endpoint with source-derived hypercharge/profile equalities and actual neutral signatures; actual SU(5) adapter and derived two-charge SU(6) example complete | [Model endpoint](../../proof/current/applications/GUT/PROFILE_MODEL.md), [SU(5) adapter](../../proof/current/inputs/GUT/SU5_CHARGE_PROFILES.md), [Nonuniform example](../../proof/current/applications/GUT/NONUNIFORM_PROFILE_MODEL.md) |
| Scope boundary | Explicit exclusions and unresolved extensions | [Scope](../../proof/current/applications/GUT/SCOPE.md) |
| Standard SU(5) chain generalization | `LEAN-CHECKED`: shared core, actual SU(5) source, ambient wrappers, legacy SU(5)/SU(6) adapters, and standard block SU(N) family for every N >= 5. Exact low-rank compatibility and an actual continuous SU(7) positive-target example are checked. The chosen chain and exact dual light target remain explicit | [Plan](../standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md), [Declarations](../../proof/current/applications/GUT/interfaces/standard-su5-chain.md), [SU(N) family](../../proof/current/applications/GUT/interfaces/standard-su-n.md) |

The [structural conjugation criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md) is also
`LEAN-CHECKED`: [two actual ambient conjugations](../../proof/current/inputs/Physics/TWO_CONJUGATIONS.md) on the fixed SM weight torus
suffice for the supported-signature endpoint with an invariant mass and actual
dual-index matching only at the fifteen SM weights, for every residual character.
Only restricted unitarity and separate positive Q/down totals are needed;
ambient unitarity, a common species total and a global dual target are not. It recovers
known SU(5) chains and excludes compatible extensions of
the actual triality counterexample; it does not establish new physical model
coverage or a group-free obstruction.
The Q-only endpoint needs support only for appearing qque fields. Under the
retained fifteen-weight target, the same two moves also recover down/lepton
compatibility and preserve both full-support signatures (and the finite
non-Abelian pair of residual internal coefficients) with positive Q/down targets.

## Status labels

- `STANDARD`: textbook/group-theoretic input still needing a citation or local formalization.
- `BOUNDED`: verified only up to a finite search bound.
- `DERIVED-UNVERIFIED`: derived previously but not independently checked.
- `NEEDS-AUDIT`: a critical bridge requiring careful reconstruction.
- `LEAN-CHECKED`: accepted by Lean's kernel in the explicitly stated scope.
- `TARGET`: theorem still intended, not yet established.
- `OUT-OF-SCOPE`: intentionally excluded from the current theorem.

## Working state

Read the selected [topic record](../README.md) for its task and
verification commands. The update policy is in
[the workflow](../../architecture/WORKFLOW.md). This dashboard changes only
when a claim's public status, scope, or dependency changes.

Historical milestones and build evidence are preserved in
[the thematic archive](checkpoints/README.md). The
[scoped standard SU(5) roadmap](../su5-foundations/plans/SU5_FORMALIZATION.md) is now
complete, with actual `n(10 + bar5)` matter, `n > 0`, and ordinary Abelian
selection rules. The [endpoint](../../proof/current/applications/GUT/SU5_SELECTION_RULE.md) is
`LEAN-CHECKED`; the SU(6) claims above are unchanged.
Its [shared algebra/tensor prerequisite](../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md)
is checked independently of SU(6). This extraction neither enlarges the
SU(6) theorem's scope nor by itself establishes the SU(5) endpoint.
The [standard SU(5) embedding and global kernel](../../proof/current/inputs/GUT/interfaces/su5-embedding.md)
are now checked too: the kernel is exactly the central cyclic group of order
six, and the quotient is topologically isomorphic to the closed image.
The covering map itself is provably noninjective.
The [actual SU(5) matter milestone](../../proof/current/inputs/GUT/interfaces/su5-matter.md) now
constructs continuous unitary realizations of `5`, `bar5`, and `10`, full-group
branching equivalences, dimensions, and quotient descent. Irreducibility of
all three actual SU(5) actions and their unitary realizations is now checked
by sign projections and corrected permutations, separately from the
dimension-based inequivalence. The
[ordinary-Abelian source bridge](../../proof/current/inputs/GUT/interfaces/su5-source.md) is now
checked for retained `n(10 + bar5)` matter, `n > 0`: every commuting unitary
Abelian action yields actual supported neutral signatures and nonzero
invariant ordered internal tensors on the selected field spaces. The full
U centralizer and character sectors are derived; finite groups, repeated
characters, and generation mixing are included. The final predicate permits
independent charge choices at all four operator slots. A supported neutral
choice refutes universal charge prohibition, without asserting all choices
are neutral. Field/tensor actions descend to the exact SM quotient times H,
and an actual one-generation model proves non-vacuity. Neither a
Grassmann/Lorentz nonvanishing theorem nor a proton-decay amplitude is asserted.

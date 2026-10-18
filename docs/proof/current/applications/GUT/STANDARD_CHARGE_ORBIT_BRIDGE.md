# Standard charge-orbit bridge

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

The following label records an earlier checkpoint, not the final status of
all adapters described in this dossier. The later proof-structure paragraphs
record the concrete benchmark and Weyl-model connections.

`LEAN-CHECKED THROUGH THE DIRAC-TYPE PHYSICAL MODEL ADAPTER; CONCRETE BENCHMARK AND GENERAL WEYL/MAJORANA ADAPTER REMAIN`

## 2. Inputs and conclusion

For the standard SU(5)-chain embedding, charge-resolved SU(5) Weyl-orbit arguments imply that any SM-only chiral index at fixed residual Abelian charge has the form

\[
I_t=n_{10,t}(Q+u^c+e^c)+n_{\bar5,t}(d^c+L)+s_t 1.
\]

Equivalently, charge-resolved multiplicities obey

\[
a_t=b_t=c_t,\qquad d_t=\ell_t.
\]

## 4. Proof structure

**Lean update:** `GUT/SU6/Branching/StandardU5Group.lean` constructs the actual injective
block homomorphism
`U(5) -> SU(6), A |-> diag(A, det(A)^-1)`, proves that its torus is the full
determinant-one diagonal `SU(6)` torus, and proves the corresponding trace-
character restriction identities for actual and finite virtual
representations.

`GUT/SU6/SelectionRules/StandardBranch/StandardAbelianCharge.lean` then replaces the exposed shift-indexed
syntax by the canonical charge-resolved `Finsupp` model
`(ReducedWeight x A) ->₀ Integer`, for an arbitrary additive commutative
charge group `A`.  It separates the normalized `SU(5)` weight from the
integer central degree and pushes that degree through any homomorphism
`Integer ->+ A`.  The push-forward uses non-injective `Finsupp.mapDomain`, so
all integer lifts that become the same finite residual charge are summed.
It proves full charge-profile equalities for `Q,u^c,e^c` and for `d^c,L`,
including explicit `ZMod N` specializations.

`GUT/SU6/SelectionRules/StandardBranch/StandardPhysicalSource.lean` removes an overrestrictive zero-offset
assumption from this interface.  An ordinary Abelian action may combine a
common central `U(5)` component with an independent charge of each ultraviolet
`SU(6)` source multiplet.  Its weight charge is therefore modeled as
`offset + centralCharge(totalDegree)`.  For a finite virtual collection of
actual finite-dimensional jointly continuous unitary `SU(6)` sources, Lean
now constructs the charge-resolved chiral character with these independent
offsets and proves it `S_5`-invariant at every charge.  Non-injective
`mapDomain` still sums collisions, so the construction and the downstream
theorems apply to arbitrary additive Abelian, finite Abelian, and `ZMod N`
charge groups.

The checked result handles both a pure SM profile and family-dependent
profiles: if the `10` and anti-fundamental profiles are nonempty, it selects
occupied common-charge sectors containing all fields needed by the two
gauge-mediated contractions.  Composing with Abelian proton-operator neutrality proves both contractions
neutral in arbitrary, finite Abelian, and finite cyclic charge groups, with
no anomaly equation.

`GUT/SU6/SelectionRules/StandardBranch/FiniteAbelianChargeSectors.lean` supplies the character-sector part
of the offset construction.  For an arbitrary Abelian residual group `H`, Lean
uses the physical additive charge-label group
`Additive (H ->* Circle)`, decomposes every supplied unitary `H` action
commuting with an actual jointly continuous unitary `SU(6)` source into its
full character eigenspaces, and proves that each eigenspace is an `SU(6)`
subrepresentation.  Distinct active eigenspaces are independent, span the
whole source, and their direct sum is representation-equivalent to the
original source, hence has exactly the same trace character.  Finiteness of
`H` is not needed: finite-dimensional unitarity supplies invariant orthogonal
complements, and irreducible complex representations of an Abelian group are
one-dimensional.  The construction uses full eigenspaces, so it allows
`SU(6)` to mix repeated copies carrying the same character.
Each sector becomes a charged physical source with its character as offset;
combining it with a common central character gives the affine phase
`offset(h) * eta(h)^degree`.  The standard charge-orbit bridge-to-Abelian proton-operator neutrality zero-charge conclusion is also
proved equivalent to pointwise trivial proton-operator phases on `H`, with
explicit finite-group specializations retained.

`GUT/SU6/Hypercharge/StandardCentralGauge.lean` constructs the actual continuous standard
central circle `z |-> diag(z,z,z,z,z,z^-5)` in `SU(6)` and proves that its
action on an ambient Laurent monomial is `z^totalDegree`.  Thus the common
central-degree term in the affine charge model is tied to a concrete gauge
transformation, not introduced as an unrelated grading.

`GUT/SU6/SelectionRules/StandardBranch/FiniteResidualActionFactorization.lean` proves the physical-action
factorization under an explicit gauge-lift certificate.  If a unitary
residual action conjugates the `SU(6)` action by a homomorphic lift, removing
that lift gives a unitary action commuting with all of `SU(6)` and the gauge
part times the external part recovers the original action.  In the standard
central case Lean proves, on every basis vector of the actual hypercharge character rigidity Laurent
model, that the physical phase is exactly
`offset(h) * eta(h)^totalDegree`.  If the physical action and central
character are continuous, all selected sector characters are continuous;
for residual `U(1)` each has a unique integer charge.  The resulting exact
pure-SM certificate proves trivial proton characters for arbitrary Abelian,
continuous Abelian, and finite Abelian residual groups by standard charge-orbit bridge followed by Abelian proton-operator neutrality,
without using continuous U(1) anomaly cross-check.

For the narrowed **ordinary Abelian internal symmetry** scope, the common
gauge lift is no longer an assumption.  A strict ordinary action is represented
by `FiniteAbelianChargeSectors.CommutingAction`: a unitary Abelian action on an
actual finite-dimensional continuous-unitary `SU(6)` summand which commutes
with the full gauge action.  `GaugeTwistedAction.ofCommuting` constructs the
canonical identity lift and proves that removing it recovers the original
action.  `OrdinaryAbelianSummand` and `OrdinaryAbelianSource` perform this
conversion for a finite virtual source.  Since the identity lift lies in every
physical centralizer, neither existence of a homomorphic lift nor a separate
centralizer certificate remains in this strict ordinary scope.  Those data
remain explicit only in the broader gauge-twisted interface, which is not
needed by the narrowed final theorem.

`GUT/SU6/Branching/StandardSMCharacterTarget.lean` now realizes the charge-resolved standard charge-orbit bridge
target itself as an actual finite virtual representation of the product of
the physical compact four-torus and an arbitrary Abelian residual group `H`.
The normalized `SU(5)` weight maps injectively to the standard physical-torus
exponent, and the explicit fifteen weights agree exactly with the hypercharge character rigidity Standard
Model target.  Dedekind linear independence of distinct product-group
characters makes the evaluator faithful, including when `H` is finite.
Arbitrary finite virtual gauge singlets with arbitrary residual characters
are allowed at zero gauge weight and are proved not to affect any of the five
SM charge profiles.  Consequently, whole-character equivalence of an actual
source with this SM-plus-singlets target implies the exact standard charge-orbit bridge profile,
`k_Q = k_u = k_e`, `k_d = k_L`, and triviality of both proton-operator
characters by standard charge-orbit bridge followed by Abelian proton-operator neutrality.  Explicit finite-Abelian and
standard-central gauge-factorized specializations are checked; no anomaly
equation is used.

`GUT/SU6/SelectionRules/StandardBranch/StandardPhysicalCharacterBridge.lean` now constructs the source side
of that actual character comparison.  At the standard pair `(-2,3)`, Lean
proves that every ambient weight splits into its normalized physical-torus
exponent and its standard-central total degree.  On each actual full residual
character sector it combines the physical torus action, the standard-central
gauge action, and the independent sector character into a representation of
the product group.  Its trace is proved exactly equal to the faithful
charge-resolved evaluator, and these representations assemble with the source
virtual coefficients.  On residual elements `(1,h)` the reconstructed action,
after inclusion into the original source space, is proved equal to the
supplied gauge-twisted physical action.  Thus the source-side
`IsCharacterModel` witness is derived rather than postulated.  Assuming only
the remaining actual target-character equivalence, Lean recovers the exact
resolved normal form, the standard charge-orbit bridge charge equalities, and the Abelian proton-operator neutrality proton-character
conclusion for arbitrary, continuous, and finite Abelian residual groups,
without using continuous U(1) anomaly cross-check.

`GUT/SU6/SelectionRules/Models/StandardPhysicalSpectrumBridge.lean` replaces that last whole-
character hypothesis by a coefficient-level physical spectrum certificate.
It proves that the fifteen explicit non-singlet SM weights are distinct and
nonzero, then proves equivalence between the following local chiral-index
conditions and the canonical resolved-character equality: every SM weight has
the stated generation multiplicity, the zero gauge weight has the supplied
finite residual-charge singlet index, and every other nonzero gauge weight has
zero chiral index.  Vectorlike pairs may still cancel in the virtual chiral
index.  These local conditions now construct the actual target-character
equivalence, so the packaged arbitrary, continuous, and finite Abelian source
theorems contain neither an `IsCharacterModel` field nor a whole-character-
equivalence field.  They derive the exact standard charge-orbit bridge charge equalities and both Abelian proton-operator neutrality
proton characters without continuous U(1) anomaly cross-check.

`GUT/SU6/SelectionRules/StandardBranch/StandardBlockGaugeCancellation.lean` removes the unnecessary and in
general false requirement that an arbitrary finite residual character admit a
reduction through the standard-central circle.  The physical centralizer has
independent color and weak block characters (with the determinant fixing the
singlet block), while the `Y5/X` basis spans an index-five sublattice.  Lean
proves directly, in every additive Abelian charge group, that the induced
block shifts
`(Q,u^c,d^c,L,e^c) = (c+w,2c,-c,-w,2w)` cancel from both proton
functionals.  It extracts `c` and `w` from the checked actual compact
centralizer, constructs external character sectors from finite collections of
actual gauge-twisted continuous-unitary summands sharing one lift, and composes
the local SM-only coefficient certificate with standard charge-orbit bridge and Abelian proton-operator neutrality.  The resulting
theorem gives trivial physical proton characters for arbitrary and finite
Abelian residual groups without character roots or continuous U(1) anomaly cross-check.

`GUT/SU6/SelectionRules/StandardBranch/StandardBlockChargeProjection.lean` strengthens that result without
assuming that the physical five field charges are externally supplied as one
common `twistCharges` assignment.  It retains the unnormalized rank-five hypercharge character rigidity
Laurent weight until the actual color/weak block characters have been
evaluated, and only then passes to the normalized SU(5) weight.  This order is
essential because the `Y5/X` lattice has index five and a finite character
group need not contain the required fifth roots.  The projection uses
non-injective `Finsupp.mapDomain`, so all finite-charge collisions are summed.
Raw Weyl invariance proves equality of the three corrected `10` profiles and
of the two corrected anti-fundamental profiles.  From a local exact-SM
coefficient certificate Lean constructs the untwisted SU(5)-orbit relations
and proves both physical proton functionals vanish for every additive Abelian
charge group.  The packaged actual common-gauge-source theorem extracts its
color/weak characters from the checked compact centralizer and gives trivial
proton characters for arbitrary and finite Abelian residual groups.  Its
axiom dependency is audited in `GUT/SU6/SelectionRules/Audit/AuditStandardChargeOrbitBridge.lean`.

The same file now specializes this construction to the strict ordinary
source.  It proves that the canonical identity lift has zero color and weak
charges, so the exact coefficient-level source obtains the **direct physical
relations** `k_Q = k_u = k_e` and `k_d = k_L`, not merely gauge-corrected
relations.  It then proves both additive proton functionals and both
circle-valued operator characters trivial.  The occupancy-level and exact
spectrum theorems are stated for arbitrary Abelian `H` and separately for
finite Abelian `H`; finite character collisions continue to be summed by the
same `Finsupp.mapDomain` construction.

`GUT/SU6/SelectionRules/StandardBranch/StandardBlockPhysicalCharacterBridge.lean` proves the corresponding
trace statement.  In standard diagonal coordinates it realizes a compact
block triple as the ambient torus point `(c,c,c,w,w)`, proves that every raw
hypercharge character rigidity monomial has exactly the `colorDegree*c + weakDegree*w` residual
character, constructs the actual product-group representation on each
continuous-unitary source sector, and identifies its trace with the faithful
`blockResolved` evaluator.  This is extended to finite virtual sources.  For
an arbitrary actual semisimple embedding classification embedding, the file exposes one geometric dependency
as `ActualBlockDiagonalization`: a fixed `SU(6)` conjugator simultaneously
putting the common centralizing lift into those standard coordinates.  Given
that certificate, Lean constructs representation equivalences sector by
sector, proves that restoring the gauge lift agrees with each originally
supplied physical action, decomposes its trace over all full Abelian character
sectors, and proves that the complete supplied physical virtual trace equals
the raw block-resolved evaluator.  `PureSMActualBlockTraceSource` combines
this trace theorem with the local exact-SM coefficient certificate and the
standard charge-orbit bridge-to-Abelian proton-operator neutrality proton-character conclusion, including finite Abelian groups.
For a strict ordinary source, the identity-lift conversion is definitionally
the original commuting action on each summand; Lean now exposes its finite
virtual trace directly and identifies it with
`ordinaryAbelianResolvedCharacter`.

`GUT/SU6/Hypercharge/ActualBlockConjugacy.lean` discharges the previously explicit
`ActualBlockDiagonalization` input.  From the actual semisimple embedding classification weak-doublet data it
proves that the color, weak, and singlet coordinate ranges form an orthogonal
internal direct sum of dimensions `3`, `2`, and `1`; chooses orthonormal bases
in that fixed order; and obtains one unitary basis matrix intertwining every
actual compact-centralizer element with its standard diagonal block-torus
point.  A one-column unitary phase correction makes this matrix determinant
one and commutes with every diagonal block point.  Lean therefore constructs
a single `SU(6)` conjugator uniformly for the whole centralizer, proves that
every supplied centralizing gauge lift satisfies the required conjugacy, and
promotes every `PureSMActualBlockProjectedSource` to the physical trace
theorem without an additional conjugator hypothesis.  This standardizes the
centralizer action; it does not claim a stronger classification of the full
semisimple embedding up to source automorphisms.
It also proves that an exact strict ordinary source's originally supplied
residual-action trace equals the canonical SM-plus-singlets target, so the
ordinary resolved character is tied to the physical action rather than being
an unaudited auxiliary polynomial.

`Physics/StandardModel/Operators/StandardModelLocalOperator.lean` gives the two Abelian proton-operator neutrality functionals an
explicit EFT local-operator meaning.  It defines the physical-field
signatures `q_L q_L u_R e_R` and `d_R u_R q_L l_L`, with the sign conversion
from the stored left-handed conjugate charges.  Kernel-checked finite
calculations prove hypercharge neutrality, canonical dimension six,
`Delta B = Delta L = 1`, and the required three-color, two-weak, two-left-
spinor, and two-right-spinor slot counts.  Explicit injective slot plans
select the corresponding epsilon contractions.  The determinant epsilon
tensor is proved invariant under every complex special-linear action and
nonzero in dimensions three and two.  Finally, the residual characters of
the two operator classes are proved equal to `protonFirstCharacter` and
`protonSecondCharacter`.

`SupportedInvariantOperator` packages a supported physical charge assignment,
one of these two checked local operator classes, and a proof that its residual
character is trivial.  `GUT/SU6/SelectionRules/StandardBranch/StandardAbelianProtection.lean` now constructs
such a positive witness from every exact or occupied standard charge-orbit bridge source and derives the
selection-rule refutation from it.  This closes the local operator-class
interpretation at the stated finite-signature and epsilon-tensor level for
arbitrary and finite Abelian residual groups.  It does not construct an
operator-valued distribution, Wilson coefficient, or decay amplitude.  The
separate propositions `firstPresent` and `secondPresent` are retained only for
the optional stronger present-channel corollary.

The broad predicate
`ForbidsEverySupportedPhysicalDeltaBOneOperator` literally quantifies over
every supported four-fermion signature satisfying the declared physical
operator predicate.  Lean now classifies their field multiplicities from the
integer color, weak, chirality, hypercharge, baryon, and lepton constraints.
Up to slot order the only possibilities are `(Q,Q,u_R,e_R)` and
`(d_R,u_R,Q,L)`, so every admissible signature has one of the two canonical
residual characters.  Consequently the universal protection predicate is
equivalent to the two-class predicate, and the constructed
`SupportedInvariantOperator` refutes both directly.  Thus the final wording
"cannot forbid every physically admissible operator" is justified within the
declared finite-signature model rather than inferred from an unproved
exhaustiveness claim.

The family-dependent physical-profile version is now checked as well.
`GUT/SU6/SelectionRules/StandardBranch/StandardBlockChargeProjection.lean` proves that translations of a
finite charge profile are injective in every additive Abelian group.  From a
raw Weyl-invariant source and merely nonempty physical `Q` and `d^c` profiles,
it selects charges supported by all five SM profiles after the actual
color/weak block twist and proves both proton functionals zero.  This no
longer assumes one family-universal charge assignment.  The theorem is
composed with `actualBlockResolvedCharacter`, and an explicit finite-Abelian
specialization retains the non-injective finite-charge collision sums.

`GUT/SU6/SelectionRules/StandardBranch/StandardAbelianProtection.lean` separately defines
`ForbidsEverySupportedProtonOperator`, the statement that the Abelian charge
rule by itself charges both standard proton-operator classes nontrivially for
every charge assignment supported by the chiral profiles.  The new standard charge-orbit bridge-to-Abelian proton-operator neutrality
theorem refutes this property for arbitrary and finite Abelian residual
groups, both for the exact projected source and directly for any actual
common-gauge source with occupied `Q` and `d^c` profiles.  This is logically
weaker than proving a particular amplitude nonzero.  The refutation now
factors through the positive `SupportedInvariantOperator` witness above.  A
nonzero dynamical channel is required only by the separately exposed
present-channel corollary.

The refutation is now also stated directly for strict ordinary Abelian
sources, both at occupancy level and for the exact coefficient-level source,
with finite-Abelian specializations.  No chosen gauge lift and no continuous
`U(1)` anomaly premise occurs in these theorem signatures.

`Physics/FieldTheory/Mass/EquivariantMassIndex.lean` now formalizes the vectorlike-decoupling
step that had previously appeared only in the interpretation of the chiral
index.  For an equivariant map between arbitrary finite-dimensional unitary
complex representations, Lean constructs the invariant orthogonal
decompositions by its kernel and range.  The kernel complement is proved
representation-isomorphic to the range, so trace additivity gives

```
character(kernel) - character((range)^⊥)
  = character(source) - character(target).
```

Both sides are packaged as the project's actual finite virtual group
representations and proved character-equivalent.  Thus integrating out the
paired range preserves the virtual character without taking exactness or
vectorlike cancellation as an informal premise.

The same file now bridges the usual Lagrangian formulation to this interface.
`InvariantMassPairing` assumes invariance of
`inner (rhoW g w) (M (rhoV g v))`; target unitarity and nondegeneracy of the
Hermitian inner product then prove `M (rhoV g v) = rhoW g (M v)`.  Lean bundles
this theorem as the required `IntertwiningMap`, constructs the invariant
pairing back from every intertwiner, and checks the round trip.  Thus
equivariance need not be duplicated as a model assumption once an invariant
mass pairing is supplied.

`Physics/FieldTheory/Mass/UnitaryVirtualRealization.lean` now closes the corresponding
realization step for arbitrary finite integer combinations of unitary
representations.  Each coefficient is split canonically into its positive and
negative natural parts, repeated summands are assembled with the Hermitian
`L2` product, and Lean proves that the resulting two actual
finite-dimensional unitary representations have character difference equal
to the original virtual character.  In particular, no separately postulated
ultraviolet source-minus-target character equality is needed once the
unitary virtual source is supplied.

`GUT/SU6/SelectionRules/StandardBranch/PhysicalChargeResolvedEvaluation.lean` proves the required faithful
joint evaluator for the more general physical normal form
`PhysicalExponent x ChargeLabel`.  Distinct physical four-torus weights and
residual characters give distinct product-group monoid homomorphisms, so
Dedekind linear independence recovers every integral coefficient even when
the residual Abelian group is finite.  It also realizes every such `Finsupp`
as an actual finite virtual sum of one-dimensional representations.

`GUT/SU6/SelectionRules/Models/PhysicalChargedCharacterBridge.lean` further reconstructs the
product action of the physical compact four-torus and the residual Abelian
group directly on every actual charged sector of the continuous-unitary
`SU(6)` source.  The inherited Hermitian form is proved invariant, its trace
is proved equal to the physical weight-and-charge evaluator, and the finite
charged source is bundled into the unitary virtual realization above.  Hence
the canonical ultraviolet mass index is now theorem-level
character-equivalent to the actual charged `SU(6)` source.

`GUT/SU6/SelectionRules/Models/PhysicalMassSpectrumBridge.lean` now also provides the weaker and
more direct physical-spectrum interface `OrdinaryChiralIndexSource`.  Its
infrared input is a single statement that the light virtual character of an
actual equivariant mass map equals the exact SM-plus-singlets target.  It does
not require separately chosen equivalences from the kernel and orthogonal
cokernel to positive and negative target aggregates.  The faithful joint
torus/residual evaluator upgrades that character equality to the exact local
coefficient spectrum, after which the already checked hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality chain
fixes `(-2,3)` and proves both proton characters trivial.  The result is
checked for arbitrary and finite Abelian residual groups.

Using these results, `GUT/SU6/SelectionRules/Models/StandardMassSpectrumBridge.lean` derives the
standard coefficient spectrum and the standard charge-orbit bridge-to-Abelian proton-operator neutrality proton-character conclusion
from an actual equivariant mass map and character identifications.
`GUT/SU6/SelectionRules/Models/PhysicalMassSpectrumBridge.lean` performs the same argument before
the hypercharge pair is known.  Its strict ordinary specialization now
constructs the ultraviolet representation and its character identification
from the actual charged source.  `GUT/SU6/SelectionRules/Models/PhysicalLightSpectrumBridge.lean`
also unitary-realizes every physical resolved target key.  The strict source
therefore takes the equivariant mass map and actual representation
equivalences from its unmatched kernel/cokernel to the positive/negative
SM-plus-singlets target aggregates; their light-character equality is a
theorem, not a field.  These mode-space data remain model inputs.  Its checked
proof term is

```
equivariant mass index -> faithful physical resolved character
  -> hypercharge character rigidity fixes (-2,3) -> standard charge-orbit bridge coefficient spectrum -> Abelian proton-operator neutrality.
```

The reusable audit `GUT/SU6/SelectionRules/Audit/AuditPhysicalMassSpectrumBridge.lean` reports only
`propext`, `Classical.choice`, and `Quot.sound` for this complete chain.

`Physics/FieldTheory/Mass/UnitaryBlockMass.lean` now constructs those mass-index data from a
more primitive normal form.  Given unitary representation equivalences

```
UV_positive ~= light_positive ⊕ paired,
UV_negative ~= light_negative ⊕ paired,
```

with the same actual heavy representation `paired`, Lean constructs the
equivariant block mass, proves that its kernel is representation-isomorphic
to `light_positive`, and proves that the orthogonal complement of its range
is representation-isomorphic to `light_negative`.  These statements remain
valid after conjugating the block mass by the supplied unitary equivalences.
`PhysicalLightSpectrumBridge.BlockDecomposition` specializes this normal form
to the faithful charge-resolved SM-plus-singlets target, and
`PhysicalMassSpectrumBridge.BlockSource` derives hypercharge character rigidity, standard charge-orbit bridge, and Abelian proton-operator neutrality without taking
a mass map or either kernel/cokernel equivalence as a field.

`Physics/FieldTheory/Yukawa/DiracYukawaMass.lean` and
`GUT/SU6/SelectionRules/Models/DiracPhysicalModel.lean` now close this source adapter for the
explicitly scoped finite-dimensional Dirac-type class in
[MODEL_INTERFACE.md](MODEL_INTERFACE.md).  An invariant bare mass, equivariant
Yukawa family, and invariant VEV construct the equivariant post-vacuum mass
map.  The model may legitimately supply its candidate exact strict commuting
unitary Abelian action and `HasExactSMChiralIndex`; these remain applicability
conditions rather than conclusions about every SU(6) Lagrangian.  Separate
kernel/cokernel equivalences or a unitary light-plus-heavy block decomposition
are optional stronger ways to prove the index equality.  Equality of the
chiral index permits additional vectorlike zero-mode pairs and is not equality
of the complete light spectrum.

The corresponding Dirac-model theorem constructs the existing
`ContinuousInvariantMassPairingSource` and obtains the complete
`semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality` selection-rule conclusion, including a direct finite-
Abelian specialization.  A persistent axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. The non-vacuity audit is now checked by
`ConcreteDiracBenchmark.model`: standard continuous geometry, actual
`15 + bar6 - 6` matter, neutral residual action, and a zero mass sector give
generation index one. Its source character and canonical light index are
proved, not assumed. This does not remove vectorlike zero modes. See
`MODEL_INTERFACE.md` for the representation-field correction discovered by
this concrete construction and its permanent regression tests.
General invariant Weyl/Majorana bilinears remain outside that Dirac adapter,
but their radical/self-dual-quotient foundation is checked in `InvariantWeylMass`.
`StandardWeylDualTarget` now connects the conserved dual index to standard charge-orbit bridge: the
normalized dual reverses both gauge and residual labels, and the fifteen
SM weights do not overlap their negatives. Their oriented charge profiles
are therefore unchanged by antisymmetrization, yielding `k_Q = k_u = k_e`
and `k_d = k_L`, followed by Abelian proton-operator neutrality, including finite Abelian groups. A persistent
audit checks standard axioms and `ZMod 2` cases. This does not reconstruct
self-dual singlets, the signed Dirac index, or the full zero-mode spectrum.
The generic actual-mass endpoint exposes UV field/source identification and
the radical's dual SM target. `StandardWeylMassSource` now derives the former
for canonical fields built from nonnegative ordinary SU(6) matter via full
charge-sector decomposition and finite orthogonal sums. `StandardWeylModel`
has no source character hypothesis and proves Abelian proton-operator neutrality neutrality, with the dual
light target still explicit and the standard hypercharge branch fixed.
`ConcreteWeylBenchmark` now supplies a nonzero-generation witness using
actual `15 + 2 bar6`, neutral action, and zero mass. Its dual target is
derived, and its radical dimension is 27. `AbelianActualSpectrum` and
`WeylZeroModeSupport` now derive actual radical support, not just UV support:
nonnegative multiplicities and the dual target force all fifteen oriented
SM weight/charge sectors when the generation index is positive. The existing
supported operator API then applies without the extra `nonzeroOrbitProfiles`
premise used by the earlier conditional UV-support lemmas; see the
[archived mass/support review](../../../../topics/mass-profile-foundations/plans/MASS_SUPPORT_REVIEW.md). Negative index forces conjugate
zero modes, handled separately. `ConcreteWeylNonzeroMass` also supplies a
nonzero symmetric mass on the same source with radical dimension 26.
`PhysicalWeylMassSource` and `ContinuousWeylModel` now complete the
general-cocharacter embedding/character-rigidity/scoped extension for the declared symmetric linearized
class. One actual radical dual target supplies hypercharge character rigidity, standard charge-orbit bridge, and actual zero-mode
support; see [the Weyl model dossier](../../inputs/GUT/WEYL_MODEL.md). This is not a general
Lagrangian or full non-Abelian gauge-tensor semantics.
The supported neutral field assignment is now realized as a checked `qque`
or `duql` EFT operator-class witness with explicit epsilon contraction data.
Proving the explicit `firstPresent ∨ secondPresent` input from gauge and flavor
dynamics is an optional stronger route to the present-channel corollary and is
not a premise of the target selection-rule theorem.  A homomorphic inner gauge
lift and its centralizer property
remain prerequisites only for the strictly broader gauge-twisted formulation,
not for the intended ordinary internal-symmetry theorem.
The jointly continuous finite-dimensional hypercharge character rigidity source bridge is now independent
and complete in its stated analytic scope.  The old fieldwise
`physicalCharges_eq` certificate and the standard-central reduction are no
longer needed by the new algebraic route, but the remaining trace/source inputs
must not be hidden in the final theorem.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

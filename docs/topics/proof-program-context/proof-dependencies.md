# Proof dependency map

Role: semantic dependencies between named results, not a current-achievements
dashboard, task queue or build baseline. Follow the [proof index](../../proof/README.md)
for dossier navigation and the [interface index](interface-checkpoint.md#checked-baseline)
for the recorded checked source.

This is the semantic proof graph, not a directory tree. Shared mathematics now
lives in `Math/`, shared field theory/SM interfaces in `Physics/`, and model
consumers in `GUT/`. Declaration namespaces and the implications below are
unchanged; see [the source layout](../../architecture/MODULE_LAYOUT.md) for paths and layer checks.

## E6 Literature Boundary

`MaximalTorusFundamentalGroup` defines the external input, not a proved theorem.
`TorusCentralizer + CompactTorus` instantiate its actual torus data;
`TorusFundamentalGroup + CompactPathConnected + hLiterature` give
`compactSimplyConnected_of_literature`. `AuditLiteratureTopology` is imported
by `GUT.lean` and rejects placeholder axioms. No L5-L7 draft is imported.
The candidate's physical theorem has no edge from `hLiterature`; named-E6
interpretation additionally uses external classification as recorded in
[the ledger](../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).

## E6 Lie Comparison

The bounded E6 route is independent of the completed physical endpoints:
`LieCertificateChecks -> MatrixLieAlgebra -> MatrixLieBasis`, together with
`RootSpaceDimension -> PinnedGeckBasis` and `BasedLieComparison`, gives
`GeckComparison`. This constructs faithful 27-dimensional actions of the
actual scalar-extended E6/D5 Lie algebras and the numbered D5 Lie inclusion.
`RootSpaceDimension` wraps TauCeti's existing public dimension formula;
`BasedLieComparison` directly calls mathlib's internal projection equivalence.
Neither maintains a separate proof of those library results.
`MatrixCompactRealForm` adds a generic fixed-point Lie complexification
theorem, reusing TauCeti's conjugation linear equivalence. Together with
`CompactExponentials` and `GeckComparison`, it gives `CompactRealForm`:
real dimensions 78/45, compatible complexification and real D5 inclusion,
and SU(27) exponentials for every real-form element. No edge to a compact
E6 physical endpoint is established by these Lie results alone. Global
identification and actual Spin inclusion remain open; the separate direct
SU(5) group-map route is recorded below.
See [E6-0e](../../proof/current/inputs/Math/E6_COMPACT_REAL_FORM.md).

`MatrixCommutant` uses distinct Cartan weights and checked raising paths.
`MatrixLieNormalizer` reuses mathlib's inner-derivation theorem; together
with the Geck Killing form and trace result these give `MatrixNormalizer`.
This closes the trace-zero complex and skew-Hermitian real Lie-normalizer
bounds, not by itself a group or global-form identification.
See [E6-0f](../../proof/current/inputs/Math/E6_MATRIX_NORMALIZER.md).

`LieNormalizerExponential` reuses TauCeti's commutator-exponential theorem
and differentiates conjugation at zero. Together with
`SpecialUnitaryExponentialCriterion`, it gives the exact all-time criterion
for `MatrixLieGroupNormalizer`, a closed compact subgroup of SU(n).
Combining this with `MatrixNormalizer` gives `CompactNormalizer` and the
exact 78-dimensional exponential-direction result; see
[E6-0g](../../proof/current/inputs/Math/E6_COMPACT_NORMALIZER.md).

`MatrixLieGroupComponent` uses connected real-parameter exponential curves
to retain this criterion on the connected compact identity component.
`MatrixLieGroupScalar` and mathlib's primitive roots give `NormalizerCenter`:
an order-27 central element of the full normalizer and the consequent
center-exponent obstruction. Its membership in the identity component is
not proved. The pinned ambient matrix log/exp inverses are compiled in
the audit. See
[E6-0h](../../proof/current/inputs/Math/E6_IDENTITY_COMPONENT.md).

`LieNormalizerLocalLog` applies those inverse identities to the commutator
operator on invariant subspaces. `SpecialUnitaryLocalLog` removes local
skew/trace ambiguities; together they give `MatrixLieGroupLocalLog`.
The exact E6 normalizer bound then gives `CompactLocalLog`: local
real-form logarithms, an open identity component and equality with the
algebraic exponential-generated subgroup. `LocalInverseChart` and these
local inverse laws give `CompactChart`, including an ambient-log inverse
on the entire target. `CompactAtlas` translates it using `Homeomorph.mulLeft`;
analytic coordinate changes give a smooth manifold on the original topology.
`CompactLieGroup` transfers smoothness from actual matrix coordinates to
derive smooth multiplication/inversion. `CompactTangent` computes the
identity differential and proves its image is exactly the real form.
`CompactLieAlgebra` bundles the actual units inclusion and applies the
audited Lie functor/units bracket to identify the geometric tangent Lie
algebra with the real form. Global form and the Spin inclusion remain open;
the direct SU(5) inclusion below uses the already checked exponential
criterion. See [E6-0n](../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md).

`CompactCenter` differentiates actual centrality using `CompactAtlas` and
extends commutation through the real-form complexification. `MatrixCommutant`
and the SU determinant give an injection into the 27th roots and a finite
cyclic center of order dividing 27, not an exact center computation. See
[E6-0p](../../proof/current/inputs/Math/E6_COMPACT_CENTER.md).

`D5Blocks`' checked grading and `CompactChart.compactExp` give `CenterThree`:
an actual order-three scalar in the identity component. It combines with
`CompactCenter` to bound the center order by `3 divides |Z| divides 27` and
with `NormalizerCenter` to locate the ambient order-27 scalar's ninth power.
`CentralQuotientObstruction` uses `UnitaryRepresentation` to prove that the
actual 27 does not descend to the center quotient. No maximal-torus,
covering/classification or simple-connectedness theorem is used or proved;
see [the bounded result](../../proof/current/inputs/Math/E6_CENTER_THREE.md).

`SparseCubicCertificate` checks `CubicInvariant` on all 78 actual basis
matrices. `matrixLieAlgebra_span` extends this to the full Lie algebra,
and `CubicExponential` proves invariance along actual exponential orbits.
`CubicGroupInvariant` then uses `CompactLocalLog`'s algebraic exponential
generation. `ExactCenter` combines that invariant's nonvanishing and degree
three with `CompactCenter` and `CenterThree`: the center is exactly the
cube roots of unity. No global classification is used; see
[the cubic/exact-center result](../../proof/current/inputs/Math/E6_CUBIC_CENTER.md).

`TorusCoordinates` checks a six-weight integral basis against the pinned
weights. `CompactTorus` uses `compactExp` and the actual Cartan matrices to
embed six circles in the candidate and computes the full period lattice.
`CubicTorusReconstruction` extracts 21 relations from `cubic_invariant` and
recovers any diagonal candidate element from six seed phases. Differentiated
torus commutation and `MatrixCommutant` then prove `TorusCentralizer.centralizer_eq`
and maximality among Abelian subgroups. This supplies an actual maximal torus,
not a fundamental-group or simple-connectedness theorem; see
[the torus result](../../proof/current/inputs/Math/E6_COMPACT_TORUS.md).

`RotationExponential` proves the real Banach-algebra rotation formula by
differentiation. `CorootRotations` combines it with sound sparse checks
against the pinned simple-root matrices. `CorootLoops` uses those
half-period and quarter-turn identities inside actual `compactExp` group
elements, producing based contractions for all six coordinate loops.
`hLine_torus` connects their parametrization to `Torus.hom`. No assumed
SU(2) inclusion or simply connected group is used; see
[the coroot-loop result](../../proof/current/inputs/Math/E6_COROOT_LOOPS.md).

`CircleLoopLift` uses the pinned circle exponential cover and path-lifting
theorem, deriving integral normalized endpoints. `TorusLoopContraction`
extends the actual coroot filling to every integer winding and forms an
ordered product of six lifted-coordinate fillings. This contracts every
identity-based torus loop inside the candidate. `TorusFundamentalGroup`
compares those path images to `FundamentalGroup.mapOfEq`, then uses
quotient induction to prove the whole induced map trivial. Its surjectivity
remains unproved; see [the all-torus-loop result](../../proof/current/inputs/Math/E6_TORUS_LOOPS.md).

The separate [SU(5) coordinate comparison](../../proof/current/applications/GUT/E6_SU5_COORDINATES.md)
uses `D5Blocks` and the pinned simple-root matrices in `SU5Coordinates`.
`SU5ExteriorCoordinates` ties the comparison to the actual SU(5) matter
bases, exterior functor and dual action. `SU5ModelComparison` joins these
in a signed Hermitian-preserving module equivalence and generator identities.
It does not depend on global-form identification or construct a group map.

The [actual candidate-group map](../../proof/current/applications/GUT/E6_SU5_GROUP_MAP.md) adds
`SU5GroupAction -> SU5Exponential -> SU5LieImage -> SU5Inclusion`.
The first step uses `RepresentationConjugation`; the exponential step reuses
the dimension-generic `compactOneParameter` API and TauCeti's one-parameter
uniqueness theorem. `SU5LieImage` combines the finite E6 basis certificate
with traceless decomposition and adjoints. `CompactIdentityComponent`'s
all-time criterion and `SpecialUnitaryGeneration`'s two-exponential
factorization then give membership for every SU(5) element. No general
Lie integration or global-form result enters this construction. The audit
checks the common `StandardChain` consumer with this actual map; mass and
exact light-target hypotheses are retained, not inhabited by that check.

The [actual 27 model](../../proof/current/applications/GUT/E6_POSITIVE_TARGET.md) then uses
`UnitaryRepresentation -> SU5Character -> MinusculeBenchmark`.
Matrix unitarity/continuity and the constructed restriction equivalence
give actual traces. The existing SU(5) torus matter formulas and radical
dual-index conservation derive the positive light target for every
torus/residual-invariant symmetric mass. A zero-mass continuous inhabitant
has all 27 modes light; its nonzero SM modes and supported obstruction
follow from `TorusMassSource` and `StandardChain`. No Spin(10) branching,
global E6 identification or assumed target enters this example.

## Main standard-branch route

The primary proof is organized by mathematical responsibility:

1. **Semisimple embedding classification** classifies the relevant continuous
   injective `SU(3) x SU(2) -> SU(6)` embeddings in the presence of a
   commuting circle.
2. **Hypercharge centralizer geometry** computes the compact centralizer and
   its integral cocharacter lattice.
3. **Hypercharge character rigidity** connects actual finite-dimensional
   continuous SU(6) representations to finite Weyl-invariant weight
   characters and uses the odd fifth moment to select the standard
   cocharacter.
4. **Standard charge-orbit bridge** transports the charge-resolved light
   chiral index to the SU(5) Weyl-orbit equalities.
5. **Abelian proton-operator neutrality** proves that those orbit equalities
   make the supported `qque` and `duql` operator characters trivial for an
   arbitrary additive Abelian charge group.
6. **Scoped physical-model assembly** obtains the preceding inputs from the
   declared Dirac/Yukawa and symmetric linearized mass models.

In dependency notation:

```text
Semisimple embedding classification
  -> Hypercharge centralizer geometry
  -> Hypercharge character rigidity
  -> Standard charge-orbit bridge
  -> Abelian proton-operator neutrality
  -> Scoped physical-model assembly
```

## Independent and auxiliary routes

- **Flipped Weyl obstruction** is the independent representation-theoretic
  obstruction induced by the ambient transposition `(3 6)`.  It does not use
  the Abelian proton-operator argument.
- **Continuous U(1) anomaly cross-check** is auxiliary evidence only.  It is
  not an implication from anomalous baryon number to the absence of every
  exact protecting symmetry.
- **Bounded branching cross-check** is computational evidence and is not a
  premise of the final theorem.
- **Vacuum stabilizer audit** concerns the explicit scalar realization.  It
  shows that the constructed VEV has a stabilizer larger than the Standard
  Model image and is not needed by the scoped no-go theorem.

## Reusable Generalizations

The [compact symplectic chirality route](../../proof/current/applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md)
is independent of the SU(6) classification and anomaly arguments:

```text
QuaternionicSpectral -> QuaternionicEigenbasis
  -> Sp.PairedEigenbasis -> Sp.TorusConjugacy
  -> Sp.RestrictedCharacter (with SelfDualCharacter / SelfDualMassIndex)
  -> Sp.ChiralityObstruction (with StandardModel.SelfDualChirality)
```

Actual matrices supply the quaternionic data and symplectic basis change;
all-element inverse conjugacy is proved, not assumed. The final positive
SM target exclusion uses faithful gauge-weight evaluation and exact index
matching. The standard-chain adapter is separate and is not a prerequisite
for this arbitrary-subgroup theorem.

The newer generalization labels A-C are distinct from the historical labels
below. Their focused dossiers are [character restriction](../../proof/current/inputs/Math/CHARACTER_RESTRICTION.md),
[exact-sequence index](../../proof/current/inputs/Math/CHARACTER_EXACT.md), and
[multiplicity centralizers](../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md).

For the latter, mathlib's isotypic decomposition and Schur's lemma supply
`MultiplicityCommutant -> CommutantCentralizer`. `UnitaryMultiplicity` supplies
semisimplicity from an invariant inner product, and the old SU(6) embedding
module uses its compatibility wrappers. `UnitaryIntertwiner` uses mathlib's
positive square root to normalize equivariant equivalences;
`IsometricMultiplicity` applies it to construct Hilbert multiplicity
coordinates. `UnitaryCentralizerTransport` supplies the U/SU topological
transport and determinant preservation. `MultiplicityMatrix` checks the
amplified matrix action and weighted determinant. `HilbertMultiplicityOperator`
and `HilbertMultiplicityDeterminant` identify the actual Hilbert adjoint and
determinant. `MultiplicityUnitaryCentralizer` proves exhaustiveness using
the algebraic commutant dimensions and constructs the product-U topological
equivalence. `MultiplicitySpecialCentralizer` restricts it to the full
weighted determinant kernel. `UnitaryMultiplicityClassification` constructs
all source data from the unitary representation alone. The established
SU(6) two-torus theorem remains independent of these generic endpoints.

## Shared Character and Mass Support

The [standard-chain plan](../standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md) first isolates
the group-independent mass/support route:

```text
UnitaryCharacterProfile -> UnitaryCharacterSpectrum -> AbelianMassSpectrum
CharacterExact -> SymmetricMassIndex -------------> AbelianMassSpectrum
AbelianCharacterPolynomial (faithfulness/duality) -> both spectrum modules
```

This core has no transitive SU(5)/SU(6) imports and is proved compatible
with the legacy spectrum. The arbitrary-SU(5) source and ambient-G theorem
build on it in the [standard-chain layer](#standard-chain). The existing
standard/flipped endpoints above retain their original hypotheses.

## Scalar-Dependent Mass Sources

The [generic mass-source extension](../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md) has
a checked SU(5)/SU(6)-free import closure:

```text
InvariantMassData -> WeylMassFamily -> MultilinearWeylMass
  -> MultilinearWeylMassContinuity -> WeylMassPolynomial
```

Coefficient symmetry/equivariance and real-linear slot covariance derive
an equivariant family. A fixed vacuum then derives an invariant mass;
mass invariance is not a source assumption. Finite-basis expansions give
joint continuity. The separate legacy compatibility adapter proves actual
degree-one recovery. `ContinuousWeylFamilyModel` now derives the mass and
delegates to the unchanged SU(6) symmetric-mass endpoint. Its old-model
conversion preserves the entire mass model, and the neutral quadratic
benchmark inherits the exact radical spectrum and supported signature by
mass-model equality. This [MASS-3 bridge](../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md)
retains the exact light-target hypothesis and the `CompactTorus x H`
interface; it does not upgrade that benchmark to full-gauge mass invariance.

## Shared SU(5) Prerequisites

The [shared selection-rule foundation](../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md)
has a checked SU(6)-free import closure:

```text
AbelianCharge + AbelianProtonCharge -> AbelianProtonCharacter
WeylOrbit + AbelianProtonCharge -> ChargeResolved
ChargeResolved + AbelianProtonCharacter -> StandardModelLocalOperator
ChargeResolved -> FiniteSMTarget -> FiniteChargeProfiles
FiniteChargeProfiles + StandardModelLocalOperator -> ProfileOperatorSignatures
  -> SMEpsilonTensor -> StandardSMGaugeTensor
StandardSMGaugeTensor + AbelianProtonCharacter -> ResidualGaugeTensor
```

SU(6) physical-source adapters import this core, not conversely. The
`StandardSMResidualTensor` legacy entry point additionally imports that
source and is deliberately not an independent core module. The actual SU(5)
commuting-action source bridge below is a separate proof; coefficient orbit
identities do not supply it automatically.

The [finite-profile extension](../../proof/current/inputs/GUT/FINITE_CHARGE_PROFILES.md) is a
conditional target-algebra layer: common positive totals give the uncharged
target, while separate orbit equalities give neutral occupied signatures.
Its audit also rejects transitive SU(6) imports. The old
`StandardSMCharacterTarget` imports `FiniteSMTarget` and retains its physical
evaluator and source adapters. Deriving actual radical support and orbit
equalities from the new profile target was originally PROFILE-2/3.
`SMChiralIndex -> ProfileChiralIndex` now provides the dual coefficient
bound and orbit implication. `ProfileZeroModeSupport` combines those with
faithful evaluation and actual nonnegative radical multiplicities to produce
real zero-mode witnesses. This [PROFILE-2 bridge](../../proof/current/applications/GUT/PROFILE_ZERO_MODES.md)
is conditional on the orbit equalities. `PhysicalProfileSource` now derives
those equalities and hypercharge from the actual source and the same dual
light target; `ContinuousProfileModel` assembles the positive-orientation
endpoint and scalar-family wrapper. See the [source dossier](../../proof/current/applications/GUT/PROFILE_MODEL.md)
for the completed acceptance gates. The independent SU(5) route is
`UnitaryCharacterSectors -> UnitaryCharacterProfile -> SU5.ChargeProfiles`:
actual eigenspace dimensions define the common natural profiles, and
`SupportedFields`/`SupportedTensors` retain their actual field endpoints.
`ScalarResidualSource -> NonuniformProfileModel` constructs a two-charge
actual SU(6) source and derives its dual target by trace, then consumes the
same endpoint. Its self-inverse-character condition is specific to this
example, not a hypothesis of the profile endpoint.

The [standard embedding](../../proof/current/inputs/GUT/interfaces/su5-embedding.md) is now checked,
also with a transitive SU(6)-free audit:

```text
StandardSMGaugeTensor + TauCeti unitary-group topology -> StandardModel
StandardModel + mathlib CircleAddChar -> StandardModelKernel
StandardModelKernel + mathlib strict first-isomorphism theorem -> StandardModelQuotient
```

The matrix kernel is established before the roots-of-unity identification.
Compactness and continuity justify the topological quotient, not just an
algebraic isomorphism. This does not use a matter or charge-source assumption.

The [actual matter and branching](../../proof/current/inputs/GUT/interfaces/su5-matter.md) now use:

```text
StandardModel + TauCeti exterior powers -> Matter
WeakContragredient + Matter -> Fundamental branching
ExteriorPairing + Fundamental branching -> ExteriorSquare branching
finite-basis Hilbert copy + TauCeti compact unitarization -> FiniteBasisUnitaryModel
Matter + actual continuous coefficients -> UnitaryMatter
actual branching + StandardModelQuotient -> QuotientDescent
UnitaryMatter + QuotientDescent -> Unitary branching
Matter + SU(5) sign/permutation matrices -> MonomialElements
BasisIrreducibility + MonomialElements + UnitaryMatter -> MatterIrreducibility
```

All are audited independently of SU(6). Actual and unitary `5`/`bar5`/`10`
irreducibility is now checked via coordinate projections and basis mixing,
not deduced from SM branching or dimensions. The
[actual source bridge](../../proof/current/inputs/GUT/interfaces/su5-source.md) now adds:

```text
Schur + HilbertMultiplicityOperator -> ExplicitMultiplicity
actual irreducible inequivalent matter + ExplicitMultiplicity -> MatterSource
TauCeti joint eigenvectors + unitary orthogonal complements -> UnitaryCharacterSectors
MatterSource + UnitaryCharacterSectors -> ResidualSectors
ResidualSectors + full-group branching + shared charges -> SupportedFields
SupportedFields + dual/bidual split maps + ResidualGaugeTensor -> SupportedTensors
```

`OrdinaryAction` is any homomorphism into the actual U centralizer; its
multiplicity matrices and full character sectors are derived. Actual field
injections justify the common multiplet charges. The tensor action on their
ranges is proved to agree with the ambient action. Source, trivial/finite
mixing, repeated sectors, and incompatible-IR controls have their own
SU(6)-free audit. The [SU5-5 endpoint](../../proof/current/applications/GUT/interfaces/su5-final.md) closes
the roadmap with:

```text
mathlib asGroupHom + liftOfSurjective -> RepresentationDescent
SupportedTensors + actual field kernel proof + RepresentationDescent -> SupportedQuotient
SupportedQuotient + shared physical signatures -> SelectionRule
```

The quotient tensor actions pull back exactly to the covering actions.
Universal prohibition permits independently chosen charge sectors at each
slot, whereas its counterexample selects appropriate common multiplet
sectors. `Model` supplies only positivity and the actual commuting action;
`OperatorWitness` is an output. Amplitudes and Grassmann nonvanishing are
not consequences of these bridges.

## Standard Chain

The newer [standard-chain theorem](../standard-chain-foundations/plans/STANDARD_SU5_CHAIN_PLAN.md) uses
the common mass index, an actual SU(5) torus/Weyl source, faithful SM target
evaluation, and positive finite-profile support. Ambient pullback and
continuous/scalar-family wrappers live in `GUT/Common/StandardChain`.
This path does not use the SU(6) embedding classification, fifth moment or
continuous-U(1) anomaly argument. Its chosen inclusion and exact dual light
target remain explicit. `RetainedChainSource` derives that target from the
legacy SU(5) generation-centralizer action and preserves the exact full
spectrum at zero mass, without invoking SU(6). `CanonicalChainModel` converts
the old positive SU(6) models using their proved hypercharge rigidity and
actual ambient field realization. Surjective torus descent preserves their
mass, radical and full spectrum; its transport certificate is constructed,
not an input. The [standard SU(N) family](../../proof/current/applications/GUT/interfaces/standard-su-n.md)
now supplies continuous injective block inclusions for every N >= 5, with
exact N = 5/6 comparisons and a constructed SU(7) positive-target source.
Its endpoint import closure excludes SU(6); only the legacy-side comparison
imports that model. Existing SU(6) classification, rigidity and independent
flipped routes are preserved.

## Compact Spin Chain

The [compact Spin chain](../../proof/current/applications/GUT/SPIN_STANDARD_CHAIN.md) and
[actual half-spin model](../../proof/current/applications/GUT/SPIN_HALF_SPIN.md) are another checked
standard-chain specialization:

```text
SU(5) topology + compact-real double cover -> Spin.SU5Inclusion
real-to-complex Clifford map + polarized Fock action -> Spin.HalfSpin
Clifford covariance + commutant + compact scalar characters -> exact exterior action
unitary eigenbasis + exterior trace + determinant one -> Spin.SU5Branching
actual SU(5) torus characters + invariant mass index -> HalfSpinBenchmark.hasTarget
zero mass + full-character faithfulness -> exact light spectrum and actual mode support
HalfSpinBenchmark.continuousModel + common standard chain -> inhabited selection-rule endpoint
```

The target is derived for this source with trivial residual action; the
universal endpoint still requires it for arbitrary matter. Full spectrum
equality uses zero mass, whereas dual-index conservation allows any
invariant symmetric mass. This route uses neither SU(6) classification nor
the continuous-U(1) anomaly cross-check.

## Migration from the discovery labels

| Historical label | Semantic responsibility | Active documentation name |
| --- | --- | --- |
| A1 | Semisimple embedding classification | `EMBEDDING_CLASSIFICATION.md` |
| B1 | Hypercharge centralizer geometry | `HYPERCHARGE_CENTRALIZER.md` |
| B2 | Bounded branching cross-check | `BRANCHING_CROSSCHECK.md` |
| B3 | Hypercharge character rigidity | `HYPERCHARGE_CHARACTER_RIGIDITY.md` |
| C1 | Standard charge-orbit bridge | `STANDARD_CHARGE_ORBIT_BRIDGE.md` |
| C2 | Abelian proton-operator neutrality | `ABELIAN_PROTON_OPERATOR.md` |
| C3 | Continuous U(1) anomaly cross-check | `CONTINUOUS_ANOMALY_CROSSCHECK.md` |
| C4 | Historical standard-branch route | `HISTORICAL_STANDARD_ROUTE.md` |
| D | Flipped Weyl obstruction | `FLIPPED_WEYL_OBSTRUCTION.md` |
| E | Scoped physical-model assembly | `SCOPED_NO_GO_THEOREM.md` |
| F | Scope boundary and extensions | `SCOPE.md` |

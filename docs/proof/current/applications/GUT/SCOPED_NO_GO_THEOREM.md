# Scoped physical-model assembly

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

`LEAN-CHECKED FOR THE DECLARED DIRAC/YUKAWA AND SYMMETRIC LINEARIZED MASS CLASSES`

The separate symmetric-mass endpoint is now assembled through continuous
semisimple embedding classification geometry, hypercharge character rigidity, standard charge-orbit bridge, and Abelian proton-operator neutrality, with actual radical support and a one-generation
constructor. Its dual-index convention and torus/residual-group invariance
boundary are detailed in [WEYL_MODEL.md](../../inputs/GUT/WEYL_MODEL.md). The Dirac statement
and its different signed-index convention below are retained unchanged.
`ContinuousWeylYukawaModel` additionally derives this symmetric mass from
scalar-linear Yukawa data and an invariant VEV. Its nonzero coupling example
preserves the exact 15-mode benchmark; its additional assumptions and the
remaining operator-tensor boundary are in [WEYL_YUKAWA.md](../../inputs/Physics/WEYL_YUKAWA.md).
The [profile model](PROFILE_MODEL.md) additionally extends the positive dual
target to family-dependent distributions, with actual-source-derived orbit
equalities, actual radical support, and a continuous scalar-family wrapper.
The [nonuniform example](NONUNIFORM_PROFILE_MODEL.md) derives its two-charge
target explicitly. These extensions retain the index and selection-rule scope.

## 2. Inputs and conclusion

Assuming the checked semisimple embedding classification/hypercharge character rigidity/standard charge-orbit bridge/Abelian proton-operator neutrality inputs and the scoped physical model
conditions below:

> In a 4D simple SU(6) gauge theory with a finite-dimensional Dirac-type
> linearized mass sector whose
> exact massless chiral index after SU(6) breaking and before electroweak
> breaking equals nonzero Standard Model generations plus gauge singlets, no
> unbroken unitary Abelian internal symmetry commuting exactly with the full
> ultraviolet SU(6) action can, by its charge selection rule alone, prohibit
> every Delta-B = 1 local operator class represented by the declared physical
> finite-signature model.

## 4. Proof structure

`GUT/SU6/SelectionRules/FinalNoGoAssembly.lean` now checks the **conditional branchwise
assembly**.  A strict ordinary Abelian source is first forgotten to its
underlying finite virtual `SU(6)` representation.  The structure
`OrdinaryAbelianBranchSource` then records, without hiding them, the actual
injective oriented hypercharge circle and the branch-specific physical
spectrum identifications.  Hypercharge arithmetic gives flipped or standard.
In the flipped case the supplied nonzero-generation SM-plus-singlets trace
contradicts the independent `swap36` restricted-character theorem. Hence
the pair is standard, where the supplied local coefficient spectrum constructs
the strict ordinary Abelian standard charge-orbit bridge source and standard charge-orbit bridge followed by Abelian proton-operator neutrality refutes protection.

The primary assembly now constructs a concrete supported invariant `qque`
local-operator-class witness without a channel-presence premise.  A separate
stronger corollary assumes explicitly
that at least one of the two standard gauge-mediated channels is present.
Separate finite-Abelian specializations are checked, and no
continuous-`U(1)` anomaly theorem occurs in this route.  Its reusable axiom
audit is `GUT/SU6/SelectionRules/Audit/AuditScopedNoGoAssembly.lean`; every exposed scoped theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The retained compatibility interface
`MatrixDifferentiableOrdinaryAbelianSource` now connects semisimple embedding classification to this assembly
rather than taking its decomposition as an input.  From an injective
continuous matrix embedding whose exponential-coordinate map is
`DifferentiableAt Real`, and an actual injective commuting hypercharge circle,
Lean constructs the classified `3+2+1` decomposition.  It corestricts the
actual circle to the physical centralizer, extracts its unique integer
cocharacter pair, proves pointwise reconstruction of the original `SU(6)`
circle, and transports injectivity to primitivity.  The resulting source is
then converted to `OrdinaryAbelianBranchSource`, so the checked route is
literally embedding classification -> centralizer lattice -> flipped or standard
branch -> charge-orbit bridge -> Abelian proton-operator neutrality. An
ambiently differentiable matrix extension can be used instead through the
checked constructor `ofAmbientlyDifferentiable`.  More generally,
`MatrixDifferentiableHyperchargeEmbedding.ofContinuous` proves this entire
geometry record from continuity alone, so its differentiability field is no
longer an independent source assumption.

An independently checked scoped route now uses character rigidity instead of the neutral-block/flipped
branch reduction.  Every strict ordinary source is assigned its finite virtual
ambient Laurent model by combining the already constructed models of its
continuous-unitary summands.  In
`MatrixDifferentiableB3OrdinaryAbelianSource`, pointwise equality of that
source character with the actual SM-plus-singlets character on the compact
physical torus forces the extracted pair to be `(-2,3)` by the checked hypercharge character rigidity
fifth-moment theorem.  Only after this equality is obtained does the
conditional standard charge-resolved spectrum field feed standard charge-orbit bridge and Abelian proton-operator neutrality.  Thus the
endpoint proof term genuinely follows semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality and assumes neither
oriented neutral-block data nor a flipped-spectrum equality. The flipped route is retained as
the separate semisimple embedding classification -> branch arithmetic -> flipped obstruction route above.

`GUT/SU6/SelectionRules/StandardBranch/PhysicalChargeResolvedBridge.lean` now removes the duplication in
that alternative interface.  For the actual cocharacter pair `(m,n)`, it
constructs one canonical finite `Finsupp` on
`PhysicalExponent x ChargeLabel` from the full Abelian eigensectors of every
strict ordinary source.  Forgetting the charge label is proved to recover the
restriction of the source's checked ambient Laurent character, so the same
local exact-SM coefficient certificate supplies hypercharge character rigidity.  At `(-2,3)`, the
physical normal form is proved to be the image of the normalized standard charge-orbit bridge character
under an injective key map.  hypercharge character rigidity first fixes the pair, then that injectivity
recovers the exact standard charge-orbit bridge coefficient spectrum.  Singlet charge collisions are
summed by `Finsupp.mapDomain`, including for finite Abelian groups.

The charge-forgetting statement is now also connected back to the **original**
strict ordinary source, rather than only to the auxiliary list obtained by
expanding it into Abelian eigensectors.  The reusable ambient-model
definitions have been moved to
`GUT/SU6/SelectionRules/Models/OrdinaryAbelianAmbientModel.lean`.  In
`GUT/SU6/SelectionRules/StandardBranch/FiniteAbelianChargeSectors.lean`, Lean proves by the internal direct
sum trace formula that the sum of the restricted characters on all active
full character eigenspaces is the restricted character of the original
finite-dimensional `SU(6)` representation.  This is lifted through virtual
integer coefficients and finite source concatenation in
`GUT/SU6/SelectionRules/StandardBranch/StandardPhysicalSource.lean` and
`GUT/SU6/SelectionRules/StandardBranch/StandardBlockGaugeCancellation.lean`.  Faithfulness of the common
diagonal evaluator then proves
`ordinaryChargedSource_ambientLaurentModel_poly_eq`: the sector-expanded standard charge-orbit bridge
source and `OrdinaryAbelianSource.toFiniteVirtual` have literally equal
normalized ambient Laurent polynomials after charges are forgotten.

Consequently `ordinaryCharacterOnPhysicalTorus_of_exactResolved` turns the
single local spectrum certificate into a hypercharge character rigidity function-level spectrum for the
original finite virtual source, and `ordinary_eq_standard_of_exactResolved`
applies the general hypercharge character rigidity theorem to that original source's
`ambientLaurentModel`.  Thus no unproved assertion that eigenspace refinement
preserves the hypercharge character rigidity character remains hidden in the final assembly.  These
additional bridge theorems are included in
`GUT/SU6/SelectionRules/Audit/AuditPhysicalChargeResolvedBridge.lean` and
`GUT/SU6/SelectionRules/Audit/AuditStandardChargeOrbitBridge.lean`; they report only `propext`, `Classical.choice`, and
`Quot.sound`.

The corresponding
`MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource` therefore remains
the compact coefficient-level scoped interface: it has one local physical spectrum
field, not independent uncharged-hypercharge character rigidity and charged-standard charge-orbit bridge character fields.  Its
checked proof term follows semisimple embedding classification -> charge-resolved hypercharge character rigidity -> standard-key
injectivity -> standard charge-orbit bridge -> Abelian proton-operator neutrality.
The reusable bridge audit is
`GUT/SU6/SelectionRules/Audit/AuditPhysicalChargeResolvedBridge.lean`; it and the extended scoped audit
report only `propext`, `Classical.choice`, and `Quot.sound`.

`MatrixDifferentiableChiralIndexOrdinaryAbelianSource` is now the weakest
checked mass-level scoped interface. Besides the actual embedding geometry and strict
ordinary Abelian charged source, it asks for an equivariant mass map and only
the character-level assertion that its unmatched light index is the exact
SM-plus-singlets chiral spectrum.  Lean canonically identifies the ultraviolet
index with the original charged `SU(6)` source, uses faithful evaluation to
recover the physical coefficient normal form, and then proves the complete
semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality local-operator and present-channel conclusions.  Finite
Abelian specialization is direct and does not pass through a continuous
`U(1)`.

`MatrixDifferentiableInvariantMassPairingSource` gives the same route in
Lagrangian-style language.  It takes an invariant Hermitian mass pairing,
constructs the equivariant mass map as a theorem, and reuses the full
semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality assembly.  Its primary conclusion is the literal
selection-rule statement
`not_forbidsEverySupportedPhysicalDeltaBOneOperator`; no channel-presence or
Wilson-coefficient premise occurs.  The finite-Abelian theorem is a direct
specialization.  The remaining physical input is the exact light chiral-index
identification, not equivariance of the induced mass map.

`ContinuousHyperchargeEmbedding` strips this interface down to the actual
continuous injective semisimple embedding and faithful commuting hypercharge
circle.  Its canonical conversion derives the old differentiability record.
`ContinuousInvariantMassPairingSource` then exposes the complete conditional
selection-rule theorem directly in that continuity-only geometry, together
with the standard-pair, exact coefficient-spectrum, positive local-operator,
and finite-Abelian conclusions.  All are included in `AuditScopedNoGoAssembly.lean` and report
only `propext`, `Classical.choice`, and `Quot.sound`.

There is now a more structural conditional route for the complete low-energy
zero-mode spectrum.
`PhysicalMassSpectrumBridge.OrdinarySource` replaces the primitive local
coefficient field by a finite-dimensional unitary product-group mass map and
two actual light-mode representation equivalences.  Its ultraviolet
representation is now canonically constructed by splitting the actual
charged `SU(6)` virtual
source into positive and negative Hilbert-space aggregates, and its ultraviolet
character equality is proved rather than exposed as a field.  The target is
likewise constructed as positive and negative aggregates of unitary
one-dimensional physical characters.  Equivalences of the actual kernel and
orthogonal cokernel with those aggregates prove the infrared character
identity.  Lean then uses faithful joint torus and residual-charge evaluation
to derive the single exact physical chiral index and reuses the checked
hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly.  The finite-Abelian specialization is explicit.  This
closes vectorlike decoupling and both UV/IR character conversions as
mathematics; it does not itself construct the mass map and mode-space
equivalences from underlying Lagrangian data.

The stronger `UnitaryBlockMass.BlockDecomposition` route lowers that input to
two unitary direct-product decompositions with one common paired heavy
representation.  Lean defines the standard block mass, identifies its kernel
and orthogonal cokernel coordinate by coordinate, transports all three objects
back across the unitary equivalences, and constructs the previous mass-source
certificate.  The physical specialization is
`PhysicalMassSpectrumBridge.BlockSource`.

`FinalNoGoAssembly.MatrixDifferentiableMassOrdinaryAbelianSource` now connects
this structural route to the semisimple embedding classification geometry.  The actual hypercharge cocharacter
extracted from the embedding is used to reconstruct the
charged source action and type the mass map.  The resulting checked proof term
is embedding classification -> canonical UV realization -> mass index ->
character rigidity -> charge-orbit bridge -> operator neutrality, with the flipped route
remaining the independent flipped obstruction.  Local-operator,
present-channel, and finite-Abelian conclusions are all exposed separately.
`MatrixDifferentiableBlockMassOrdinaryAbelianSource` exposes the stronger
normal-form version of the same complete conditional route: its only infrared
field is the unitary light-plus-heavy decomposition, from which the mass map
and both mode-space equivalences are theorem-level constructions.

`Physics/FieldTheory/Yukawa/DiracYukawaMass.lean` and `GUT/SU6/SelectionRules/Models/DiracPhysicalModel.lean` now
complete the Lean composition step for the finite-dimensional Dirac-type
model class described in `MODEL_INTERFACE.md`.  Such a model supplies a
candidate strict commuting Abelian action and `HasExactSMChiralIndex`; Lean
derives the invariant mass map from an invariant bare mass, an equivariant
Yukawa family, and an invariant VEV.  It need not supply separate mode-space
equivalences, and no claim is made that SU(6) alone forces the Standard Model
index.  The resulting endpoint proves the universal supported-operator
selection-rule refutation for arbitrary Abelian `H`, with a separate finite-
Abelian theorem and no use of continuous U(1) anomaly cross-check.

The primitive Dirac sector has an explicit zero inhabitant, and every earlier
continuous invariant-mass-pairing source lifts compatibly to the new model
without changing its mass map.  This checks algebraic consistency of the
adapter. Separately, `ConcreteDiracBenchmark.model` now constructs the full
one-generation certificate from the actual signed `15 + bar6 - 6` source,
corresponding to all-left-handed `15 + 2 bar6`, with neutral residual action.
Its geometry has the proved standard pair, and its source character proves
the exact canonical light-index condition rather than assuming it.
The mass sector is explicitly zero, so no claim of lifting vectorlike modes
or identifying a full SM-only zero-mode spectrum is made. The representation-
field audit correction and regression constructors are recorded in
`MODEL_INTERFACE.md`. All existing scoped-assembly proofs rebuild after that correction.
The invariant radical, self-dual quotient, and dual chiral-character
conservation for general symmetric Weyl/Majorana bilinears are now checked
in `InvariantWeylMass.lean`. `StandardWeylDualTarget.lean` now recovers the
oriented SM charge profiles from the dual target and connects them to standard charge-orbit bridge -> Abelian proton-operator neutrality.
`StandardWeylMassSource.lean` discharges UV field/source identification for
canonical fields with nonnegative actual matter multiplicities. Its
`StandardWeylModel` proves Abelian proton-operator neutrality neutrality for general symmetric masses at the
fixed standard branch. `ConcreteWeylBenchmark` constructs its one-generation
non-vacuity witness from actual `15 + 2 bar6`, neutral action, and zero mass;
the proved radical dimension is 27. Actual radical support and both operator
orientations are now checked. `ContinuousWeylModel` completes the
general-hypercharge embedding/character-rigidity/scoped assembly in the separate symmetric linearized class.
The two-torsion convention audit confirms that dual indices alone cannot
identify the full light spectrum. Separately, `ConcreteWeylFullMass` proves
a nonzero mass with the exact 15-dimensional SM radical at the fixed standard
branch. `ContinuousWeylFullMass` now transports that mass and its full radical
to the continuous-geometry interface, alongside the retained zero-mass example.
The local-operator interpretation of the supported neutral profile is now
supplied by the checked `qque`/`duql` witness.  Channel presence need not be
derived for the target result; it remains an explicit hypothesis of the
optional stronger present-channel corollary.  The
older flipped branchwise interface also retains its explicit
`standardSpectrum` and `flippedSpectrum` fields.
Exact conjugacy/source-automorphism data for the full semisimple embedding may
still be useful for that older route.  Automatic regularity from a
continuous-only embedding is now checked and consumed by the new scoped
theorem; it is no longer an exposed assumption or open extension.

---

## 6. Scope and limitations

This is the intended **SU(6) symmetry-protected proton-stability no-go theorem**.
It is not a theorem that a decay amplitude is nonzero or that the proton must
decay.  Model-dependent structural zeros remain outside its scope.  The
chiral-index premise allows extra vectorlike zero-mode pairs; excluding them
would be a stronger spectrum assumption not needed here.  The separate
present-channel result is a stronger conditional corollary and keeps
`firstPresent ∨ secondPresent` explicit.  The theorem is now kernel-checked for
the scoped Dirac-type model interface and its standard charge-orbit bridge adapter. The separately
checked symmetric linearized interface does not imply a theorem for every
Lagrangian, and neither index condition excludes extra vectorlike zero modes.
The separate concrete
non-vacuity audit is now checked with trivial residual action and zero mass
sector. It is not
necessary, and would generally be false, to derive the
Standard Model chiral index from every SU(6) Lagrangian.  The exact assumption
boundary is recorded in [MODEL_INTERFACE.md](MODEL_INTERFACE.md).
The local operator-class interpretation is now checked at the explicitly
documented EFT signature and epsilon-contraction level.
The semisimple embedding classification source bridge is now closed for every continuous injective matrix-group
homomorphism in the stated scope: automatic regularity constructs both its
one-parameter differential and the formerly assumed Frechet derivative in
source exponential coordinates.  The hypercharge character rigidity universal finite-weight-character
bridge is now closed for the explicitly stated
finite-dimensional jointly continuous analytic source scope; any later use of
a separate smooth or algebraic source type must include its forgetful bridge
to that scope.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

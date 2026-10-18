# Finite-dimensional physical model interface

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Purpose

`LEAN-CHECKED FOR THE DECLARED DIRAC/YUKAWA AND SYMMETRIC LINEARIZED MASS CLASSES`

The separate continuous-geometry symmetric-mass endpoint and its exact
assumption boundary are recorded in [WEYL_MODEL.md](../../inputs/GUT/WEYL_MODEL.md). It uses
the dual radical index, not the signed Dirac index defined below, and has an
actual one-generation constructor.

The current positive-orientation extension is
[ContinuousProfileModel](PROFILE_MODEL.md): the exact dual light target
may have finite family-dependent charge distributions, and its `ScalarModel`
also permits jointly continuous equivariant nonlinear scalar dependence.
The [current assumption table](../../../ASSUMPTIONS.md) is the concise guide to
what has been relaxed. The Dirac interface described next is retained,
not silently upgraded to these newer index/source conventions.

The first charge-orbit/scoped physical-model milestone is not a syntax or semantics for every
four-dimensional Lagrangian.  It is a finite-dimensional broken-phase
Dirac-type mass-sector interface
whose data can be converted to the already checked representation-theoretic
sources.  The intended matching stage is **after SU(6) breaking and before
electroweak breaking**.

For a model `M` in this class, the intended theorem has the logical form

```text
continuous SU(6) geometry
  + finite-dimensional SU(6) matter
  + candidate exact strict ordinary Abelian action
  + invariant bare Dirac mass, equivariant Yukawa family, and invariant VEV
  + HasExactSMChiralIndex
  -> the Abelian charge rule does not forbid every represented Delta-B = 1
     local operator class.
```

It does not assert that every SU(6) Lagrangian has the Standard Model chiral
index or possesses an Abelian symmetry.

## 3. Definitions and conventions

### Fixed terminology

#### Strict ordinary Abelian action

A strict ordinary Abelian action is a unitary action of a commutative group
`H` on every finite-dimensional matter summand which commutes **exactly with
the full ultraviolet SU(6) action**.  It is the action tested as a candidate
unbroken exact symmetry.  Invariance of the complete quantum theory is a
physical input; the finite-dimensional interface records the induced action
needed by the charge-selection argument.

This scope does not automatically include an action which normalizes SU(6),
acts through a gauge-group automorphism, or closes only after a compensating
gauge transformation.  Those cases belong to the separately retained
gauge-twisted interface.

#### Exact massless chiral index

For an equivariant finite-dimensional mass map `M : V -> W`, the project's
light index is the virtual representation

```text
[ker M] - [(range M)^perp].
```

Here `light` means an exact algebraic zero mode at the stated matching stage,
not a state below a numerical energy threshold.  The equivariant mass-index
theorem proves that this class equals `[V] - [W]`; it is therefore independent
of rank even though the complete zero-mode spectrum is not.

`HasExactSMChiralIndex` means equality of this charge-resolved virtual
character with a nonzero integer number of Standard Model generations plus
the allowed gauge-singlet chiral index.  It is an applicability condition on
the model, not a consequence of an arbitrary SU(6) Lagrangian and not a
conclusion of the scoped theorem.

This condition permits additional massless vectorlike pairs invisible to the
index.  A claim that the full zero-mode spectrum contains no such pairs is a
strictly stronger certificate.  The existing `OrdinarySource` and
`BlockSource` interfaces may be used when that stronger mode-space or
light-plus-heavy decomposition is available, but the scoped theorem must not require it.

#### Invariant mass data

##### All-left-handed convention

`DiracWeylConvention.lean` now proves the translation for the existing Dirac
mass map. Its all-left-handed field space is `F = V + W*`, and its symmetric
off-diagonal bilinear is

```text
b((v, phi), (v', phi')) = phi'(M v) + phi(M v').
```

The bilinear is invariant under the full unbroken group. Its radical is
`ker M + annihilator(range M)`, and its representation character is that of
`ker M + (coker M)*`, using the invariant orthogonal cokernel model.
Consequently, with `I(g)` the existing signed light-index character,

```text
chi_rad(b)(g) - chi_rad(b)*(g) = I(g) - I(g^-1)
                              = chi_F(g) - chi_F*(g).
```

This proves Dirac zero-mode compatibility while keeping the two index
conventions distinct. Antisymmetrization can lose self-dual contributions;
equality of dual chiral differences alone does not establish the current
`HasExactSMChiralIndex` condition. The corresponding signed benchmark uses
`15 + bar6 - 6`, with its exact index proved separately; the symmetric-mass
benchmark instead has actual all-left-handed matter `15 + 2 bar6`.
The group in these lemmas is arbitrary, so dualization
includes residual charges as well as gauge quantum numbers.

##### General symmetric mass foundation

`InvariantWeylMass.lean` now defines `SymmetricMass rho`: a complex bilinear
symmetric coefficient on the all-left-handed field space `F`, invariant
under the full unbroken group. It proves, rather than assumes, that its
radical is invariant and that the induced form on `F / rad b` is
nondegenerate. In finite dimension the quotient is equivariantly self-dual.
For a unitary action, an invariant orthogonal complement then gives

```text
chi_rad(b)(g) - chi_rad(b)*(g) = chi_F(g) - chi_F*(g).
```

`lightDualIndex_characterEquivalent_ultravioletDualIndex` packages this
identity as finite virtual-character equivalence. The group is arbitrary;
duality includes every gauge and residual factor. No mass-rank hypothesis
is used, and zero mass is an explicit inhabitant. `ofDirac` recovers the
previous radical exactly, and its light dual character is the
antisymmetrization of the signed light index.

`WeylMassTwoTorsion.lean` proves the convention limitation on a concrete
nontrivial sign action of the two-element group `Int` units. The form
`b(x,y) = x*y` is invariant and nondegenerate, while zero mass on the same
representation leaves one zero mode. Their dual chiral characters are
identical. This is a representation-level convention test, not an SU(6)
model or a counterexample to the scoped theorem. It rules out recovering the full light
spectrum from the dual difference alone, including in order-two sectors.

`StandardWeylDualTarget.lean` now connects this dual convention to standard charge-orbit bridge.
The normalized involution sends `(weight, charge)` to their simultaneous
negatives and evaluates to the actual contragredient character. The fifteen
oriented SM weights are disjoint from their negatives. Consequently the
five charge profiles used by standard charge-orbit bridge survive antisymmetrization, for any additive
Abelian charge group. The singlet coefficient instead becomes `s(q)-s(-q)`;
self-dual and two-torsion data are not recovered.

The actual mass endpoint combines radical conservation with faithful joint
evaluation and obtains standard charge-orbit bridge -> Abelian proton-operator neutrality from a dual SM light target. Its charged-SU(6)
source specialization derives the polynomial model and Weyl invariance from
the existing source theory, with central twist fixed to one. It still takes
`hSource`, identifying the all-left-handed field character with that source,
and the radical's dual target as explicit hypotheses at the generic endpoint.

`StandardWeylMassSource.lean` now discharges `hSource` for canonical fields
built from ordinary SU(6) matter with nonnegative multiplicities. Charge-sector
decomposition retains those multiplicities, and finite orthogonal sums have
exactly the source character. Nonnegative coefficients count actual
left-handed copies; conjugate representations are allowed as actual summands,
but negative Dirac-index coefficients are not interpreted as fields.
`StandardWeylModel` takes this matter, an arbitrary invariant symmetric mass,
and the radical's dual SM target and proves Abelian proton-operator neutrality without a source
character hypothesis. Its hypercharge is fixed to the standard branch.

The radical dual target remains an IR applicability condition. The signed
`HasExactSMChiralIndex` and the full light spectrum are not inferred from it.
`ConcreteWeylBenchmark.model H` now constructs a one-generation witness for
every Abelian `H` acting trivially, from actual nonnegative `15 + 2 bar6`
matter. Its dual target is proved: the difference from the old signed source
is the self-dual `6 + bar6`. The radical dual target holds for any invariant
symmetric mass on these fields; the concrete witness chooses zero mass.
Both the actual field dimension and the radical dimension are proved to be
27. In particular `singlets := 0` does not assert that actual singlet modes
are absent, and the full zero-mode spectrum is not the fifteen SM modes.
`WeylZeroModeSupport` now constructs actual nonnegative multiplicities for
the radical's Abelian action and proves that their dual difference is the
specified target. At positive generation index, all fifteen oriented SM
weight/charge sectors contain nonzero radical vectors. This supplies
`ChargesSupported` and the existing `SupportedInvariantOperator` witnesses
without a UV support hypothesis. Negative index gives conjugate sectors;
the same oriented operator conclusion is not claimed in that case.
`WeylConjugateOperator` supplies a separate conjugated witness, testing
support at `(-w,-q)` in the actual spectrum and inverting the residual
operator character. Its signed baryon number is -1. The sign-independent
statement rules out forbidding both orientations; it does not silently
relabel the conjugate as the positive-baryon-number signature.

`lightSpectrum` is the restriction of the actual finite character spectrum
to the injective integral SM lattice keys. It is not asserted to recover
the full spectrum or self-dual singlet multiplicities from the dual target.
The endpoint uses the existing operator-signature/contraction-plan API; it
does not assert a nonzero coefficient, amplitude, or a new full non-Abelian
gauge-tensor realization on the radical. The mass interface requires
invariance under `CombinedGroup H` (physical four-torus times residual H),
not full ultraviolet SU(6).

`ConcreteWeylNonzeroMass.model H` retains the original `15 + 2 bar6` matter
and neutral residual action but chooses a proved nonzero symmetric mass.
A nonzero invariant vector v exists by the actual character decomposition;
`InvariantLineMass` uses `B(x,y) = inner(v,x) * inner(v,y)`, complex-bilinear
in x and y. Its radical is the kernel of the linear functional `inner(v,-)`
and has dimension 26. This refutes uniqueness of the zero mass in the
current interface, without itself giving a fifteen-dimensional SM-only radical.

`ConcreteWeylFullMass.model H` separately strengthens the benchmark. Faithful
Abelian trace evaluation constructs a prescribed actual eigenbasis with
labels `SM + 6 + bar6`. A symmetric bilinear pairs the latter two six-element
sets, including their neutral singlets. Its radical has exactly the first
fifteen basis vectors, dimension 15, and full character equal to one SM
generation; this equality is not inferred from the dual index. Both
`fullMass_actualSpectrum` and `model_lightSpectrum` are checked. The mass is
nonzero. Residual H acts trivially, and invariance is under `CombinedGroup H`;
a full non-Abelian gauge-tensor realization remains outside this assertion.
`ContinuousWeylModel` now completes the general-hypercharge embedding/character-rigidity/scoped assembly
for the declared symmetric linearized class, including actual radical
support. In addition to the retained zero-mass benchmark,
`ContinuousWeylFullMass` now transports the above nonzero 15-mode example
to that wrapper, preserving the actual mass and radical representation.

##### Yukawa source

The weakest earlier endpoint uses an invariant Hermitian mass pairing and
derives its intertwining map.  `Physics/FieldTheory/Yukawa/DiracYukawaMass.lean` now derives that
map from an invariant bare mass and an equivariant Yukawa family evaluated at
an invariant vacuum expectation value.  Their sum is proved equivariant under
the full unbroken product group, then target unitarity constructs the earlier
Hermitian-pairing interface.

This Yukawa implementation is only a Dirac-type linearized mass sector.
The general bilinear foundation and standard-branch source adapter above
are checked separately, including the general-hypercharge assembly in
`ContinuousWeylModel`. `WeylYukawaMass` and `ContinuousWeylYukawaModel` now
give a separate scalar-linear symmetric Yukawa/VEV construction, derive its
mass, and compose it with the scoped assembly. They also construct invariant coupling tensors
for arbitrary groups and allow breaking to a vacuum stabilizer. See
[WEYL_YUKAWA.md](../../inputs/Physics/WEYL_YUKAWA.md) for concrete tests and remaining boundaries.
The current Hermitian-map API is not advertised as a general Majorana API.

##### Nonlinear scalar sources and charge profiles

`ContinuousWeylFamilyModel` no longer requires scalar-linearity. Its
equivariant symmetric coefficient is jointly continuous in the scalar and
both fermion variables; finite multilinear constructions include higher
degree and conjugate slots. Fixed-VEV evaluation derives the invariant mass.
The old scalar-linear source preserves its entire mass model under conversion.

`ContinuousProfileModel.Model` replaces one charge per species by finite
natural distributions with common positive total. The actual radical's
exact dual target is still supplied, not deduced from arbitrary couplings.
Forgetting charge labels feeds hypercharge rigidity; the same target and
actual-source Weyl invariance derive the profile equalities. Positive actual
multiplicity then supplies the required radical vectors and neutral signatures.
The `ScalarModel` wrapper composes these profiles with the nonlinear source
interface. Neither orbit equality nor operator support is a model field.

Both extensions retain `CompactTorus x H` as the general unbroken-interface
group, strict commuting unitary Abelian residual action, and complex-bilinear
fermion dependence. They do not require realistic CKM mixing or certify it.
They do not reconstruct self-dual modes, prove arbitrary full-SM radical
tensors, or derive a preferred vacuum. See [the profile dossier](PROFILE_MODEL.md)
for the legacy conversions, actual SU(5) adapter, and two-charge SU(6) example.

#### Selection-rule conclusion

The conclusion is the existence of a supported, Abelian-neutral local
operator-class witness in the declared `qque`/`duql` finite-signature model.
It says that this charge rule alone cannot prohibit every represented
`Delta B = 1` class.  It does not prove a nonzero Wilson coefficient, matrix
element, decay amplitude, or proton decay rate, and it does not claim a
complete classification of every SMEFT baryon-violating operator convention.

## 4. Proof structure

### Assumptions and derived data

The model may legitimately supply:

- the candidate exact Abelian symmetry and its action on fields;
- the assertion that the action is strict ordinary in the sense above;
- `HasExactSMChiralIndex`;
- finite-dimensional Yukawa, vacuum, and bare-mass data with their stated
  invariance properties.

Lean now derives for this Dirac-type class:

- the `OrdinaryAbelianSource` commuting-action certificate;
- the post-vacuum mass map and its equivariance/invariant pairing;
- the existing `ContinuousInvariantMassPairingSource` or the weakest suitable
  chiral-index source;
- the checked semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality selection-rule conclusion.

The stronger kernel/cokernel equivalences and block decomposition remain optional
ways to prove `HasExactSMChiralIndex`, not mandatory fields of the weakest
model class.

## 5. Lean entry points

### Checked Lean realization

`GUT/SU6/SelectionRules/Models/DiracPhysicalModel.lean` defines
`ContinuousDiracYukawaModel H`.  Its fermion spaces are the canonical positive
and negative Hilbert-space aggregates of the signed strict ordinary `SU(6)`
source.  Its scalar is a finite-dimensional unitary representation of the
unbroken physical torus times `H`.  The structure records the primitive Dirac
mass data and the exact charge-resolved chiral-index condition, but does not
record the final charge equalities or no-go conclusion.

The theorem
`not_forbidsEverySupportedPhysicalDeltaBOneOperator` constructs the checked
route

```text
Dirac/Yukawa/VEV data -> equivariant mass map -> invariant pairing
  -> semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality -> neutral supported Delta-B = 1 class.
```

The finite-Abelian specialization is explicit.  The zero sector witnesses
that the primitive Dirac data type is inhabited for arbitrary actions, and
`ofInvariantMassPairingSource` proves compatibility with the older checked
source while preserving its mass map. Neither fact alone establishes a
nonzero-generation model; that separate obligation is now proved by
`ConcreteDiracBenchmark.model`.

The concrete signed source is now available independently of these abstract
adapters: `ConcreteSU6PhysicalTarget.signedSource_resolvedCharacter` proves
that the continuous-unitary `15 + bar6 - 6` source restricts to one SM
generation and no net singlets at `(-2,3)`. All three signed summands carry
the same charge in an arbitrary additive Abelian group; in particular this
includes the neutral residual character. The theorem proves the existing
charge-resolved finite-weight equality rather than assuming it.

`ConcreteDiracBenchmark.model H` constructs the complete certificate for any
Abelian `H` acting trivially. `ConcreteStandardGeometry` supplies continuous
injective geometry and proves its extracted pair is `(-2,3)`, using the
choice-independence results in `ActualBlockChoiceIndependence`. Neutrality
survives the automatic residual-sector decomposition. The conserved mass
index transports the proved source character to the canonical positive and
negative aggregates for every invariant mass map. The chosen benchmark has
zero bare mass, Yukawa family, and vacuum; `model_massMap_eq_zero` makes this
explicit. `exists_one_generation_model` has no spectrum or model hypothesis.
The scoped theorem applies to this constructed model.

This closes non-vacuity of the stated index-based class, not the stronger
claim of an exact SM-only full zero-mode spectrum. The zero-mass witness
retains vectorlike modes, and a nonzero mass sector lifting them is a separate
optional benchmark strengthening.

#### Representation-field audit correction

Constructing the benchmark exposed unresolved type names in
`CommonGaugeSummand.rep` and `OrdinaryAbelianSummand.rep`.
With `autoImplicit` enabled, Lean had elaborated each field as
`{T : Type 1} -> T`, making those summands uninhabited. The previous
conditional proofs passed the kernel but did not certify non-vacuity.
Both fields now explicitly name
`ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation`,
and `autoImplicit` is disabled in that source file and the new modules.
All downstream proofs were preserved and rebuilt successfully.
`AuditConcreteDiracBenchmark.lean` checks actual common-gauge constructors,
full models for the trivial group and `Multiplicative (ZMod 2)`, and the
standard axiom boundary of the construction and scoped specialization.

## 7. Sources and verification

### Completion audits

Audit status for the model-class theorem:

1. **Checked:** the mass convention is explicit in the structure and theorem
   namespace.
2. **Checked:** `ConcreteDiracBenchmark.exists_one_generation_model` constructs
   a full certificate with generation index one and trivial Abelian action.
   The mass sector is zero; a full SM-only zero-mode spectrum is not asserted.
3. **Checked:** `AuditDiracPhysicalModel.lean` audits the final declarations;
   their axiom dependencies are only `propext`, `Classical.choice`, and
   `Quot.sound`.  The explicit model fields are documented above.
4. **Checked:** the finite-Abelian specialization is explicit and independent
   of continuous U(1) anomaly cross-check.
5. **Checked symmetric extension:** `AuditContinuousWeylModel.lean` checks
   the continuous semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality assembly, actual radical support,
   finite-Abelian endpoints, and actual one-generation constructors with
   standard axioms. `AuditWeylYukawa` also checks the scalar-linear Yukawa/VEV
   adapter and nonzero coupling examples. General Lagrangian semantics and
   gauge-twisted actions remain separate extensions; the final model's mass
   invariance is the declared physical torus times residual group.
6. **Checked mass/profile extensions:** the MASS and PROFILE audits close
   nonlinear scalar-source composition, positive finite-profile support,
   source-derived profile equalities, actual SU(5) compatibility, and a
   nonuniform actual SU(6) model. No CKM or nonzero-channel hypothesis is
   introduced. See the [completed roadmap](../../../../topics/mass-profile-foundations/plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

# Symmetric Yukawa source bridge

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED` for finite-dimensional scalar-linear Yukawa data,
their induced symmetric linearized mass, and a continuous-unitary full-SU(6)
scalar completion of the full-gauge 15-mode benchmark. See
[the verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md) for the recorded full-build result.

The separate [scalar-dependent mass family](SCALAR_DEPENDENT_MASS.md)
now drops scalar-linearity at the generic algebraic level and recovers this
interface by exact mass equality. MASS-2 now constructs finite multilinear
sources (including real-linear conjugate slots) and proves joint continuity;
the [MASS-3 model wrapper](../../applications/GUT/SCALAR_DEPENDENT_MODEL.md) now connects them to
the existing endpoint and preserves every old linear model by mass-model
equality. The scalar-linear and full-UV realizations below are unchanged;
the new neutral quadratic benchmark is only an unbroken-interface example.
The [profile model](../../applications/GUT/PROFILE_MODEL.md) now also combines this nonlinear source
extension with finite family-dependent charges at positive total. The
scalar-linearity statements below concern the retained `EquivariantYukawa`
interface, not a restriction of every checked source model.

## 4. Proof structure

### Primitive data and derived mass

`WeylYukawaMass.EquivariantYukawa` is a complex-linear map
`S -> BilinForm C V`. Its fermion coefficient is symmetric, and the coupling
is invariant under simultaneous scalar and fermion transformations. The
group is arbitrary; no commutativity assumption is used here.

`Sector` records an invariant symmetric bare mass, that Yukawa family, and
a vacuum fixed by the declared unbroken group. `Sector.mass` derives

```text
B(x,y) = B_bare(x,y) + Y(v)(x,y).
```

Symmetry and invariance of this mass are proved from the primitive data.
`tensorIntertwiner` realizes the coupling as an actual invariant linear map
`(S tensor V) tensor V -> C`, not only a charge sum.

`atVacuumOn` allows the vacuum to be fixed only by a specified unbroken
group homomorphism into the ambient group. `vacuumStabilizer` constructs the
stabilizer subgroup, and `atVacuumStabilizer` induces its invariant mass
without assuming the vacuum is fixed by the full ambient group.

### Universal full-SU(6) scalar completion

`SymmetricScalarYukawa` constructs, for any complex representation V of a
group G, the representation of symmetric complex bilinear forms on V:

```text
S = {B : V x V -> C bilinear | B(x,y) = B(y,x)}
(g.s)(x,y) = s(g^-1.x,g^-1.y)
Y(s)(x,y) = s(x,y).
```

The subspace is invariant and Y is a full-G-invariant Yukawa family.
Both S and Y depend only on the fermion representation, not on a chosen
mass. Given an invariant symmetric mass B for a restriction along K -> G,
`vacuum` selects B as a scalar vector. `fixed_iff` proves that the scalar
is fixed exactly when the group element preserves its bilinear form.
`inducedMass_eq` proves that this VEV with zero bare mass recovers B exactly.
This is a universal nonminimal existence construction, not a restriction
to a prescribed Higgs representation or a prediction of the mass.

`ContinuousSymmetricScalar` proves joint continuity for finite-dimensional
continuous fermion representations. Finite matrix coordinates give an
injective continuous linear embedding of a Hilbert copy of S; continuity
of bilinear evaluation proves continuity of the scalar action.
`UnitarySymmetricScalar` applies the already proved compact-SU(6) Haar
unitarization and transports the Yukawa family and VEV. Thus the scalar is
an actual finite-dimensional continuous unitary SU(6) representation, not
an abstract representation or an assumed weight certificate.

`StandardSMUVYukawa` specializes this construction to the actual analytic
27-dimensional `15 + 2 bar6`. Its `mass_eq` identifies the induced mass
with `StandardSMUVMass.mass`; zero bare mass, nonzero VEV, nonzero Yukawa
family and tensor, nonzero mass, and the 15-dimensional radical are proved.
The existing actual SM radical equivalence and spectrum are retained by
this equality. `ordinary_form` identifies the VEV coefficient's pullback
with the mass on the canonical carrier; the existing
`StandardSMOrdinaryMass.continuous_mass_heq` retains that mass in the scoped
continuous-model interface. Older masses are not redefined.

`AuditStandardSMUVYukawa` checks full ambient invariance, continuity and
unitarity, trivial and finite-Abelian neutral residual examples, and the
continuous endpoint. Its negative control keeps the same nonzero coupling
but sets the VEV to zero, giving zero mass and 27 zero modes. Audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The image of the SM covering group fixes the VEV, but is now proved
**strictly smaller** than its full stabilizer. `StandardSMUVStabilizer`
exhibits a signed color/weak coordinate exchange outside SM that preserves
the same mass and VEV; see [the stabilizer audit](../GUT/SM_VACUUM_STABILIZER.md).
Equality with SM is therefore false for this VEV, not an open proof obligation.
Scalar irreducible content,
minimality, a scalar potential and its minima, and a dynamically selected
vacuum are not supplied. This is an equivariant scalar/Yukawa realization
of a specified mass, not a complete dynamical ultraviolet theory.

## 6. Scope and limitations

### Connection to the scoped assembly

`ContinuousWeylYukawaModel.Model` replaces the mass field by scalar,
Yukawa, bare-mass, and invariant-vacuum data. Its adapter `toMassModel`
derives the mass and feeds the existing continuous semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality
endpoint, including actual radical support and both index orientations.
The radical's exact dual SM target remains an infrared applicability field.

The VEV is input data, not a minimum derived from a scalar potential. The
coupling is scalar-linear, not an arbitrary higher-degree effective
interaction. This is not a syntax or semantics for every Lagrangian, a
Grassmann field algebra, quantum anomaly analysis, or a nonzero amplitude.

### Tensor boundary

`StandardSMGaugeTensor` now constructs nonzero `qque` and `duql` internal
gauge tensors on the actual standard field representations, invariant under
the full `SU(3) x SU(2) x U(1)` covering group. `StandardSMResidualTensor`
proves their precise residual characters and connects standard charge-orbit bridge -> Abelian proton-operator neutrality to their
invariance, including finite Abelian residual groups. See the
[tensor milestone](../../applications/Physics/SM_GAUGE_TENSOR.md) for its positive and negative audits.

The general mass-model endpoint still uses the declared operator-signature
API; torus invariance alone does not prove full non-Abelian mass invariance.
The older torus-eigenbasis mass is not silently upgraded.
`StandardSMFullGaugeMass` now constructs the decomposed post-breaking
27-dimensional candidate and proves its full 15-dimensional radical.
`StandardSMRadicalTensor` realizes the tensors there, including the correct
dual right-handed slots. The actual analytic SU(6) direct-product lift is
now checked in `StandardSMUVFields` and `StandardSMUVMass`, via full-group
exterior branching. Its nonzero SM-invariant mass has the exact SM radical
and both nonzero invariant ordered tensors; see [the mass dossier](../../applications/GUT/SM_GAUGE_MASS.md).
The compatible canonical-carrier adapter is now checked in
`StandardSMOrdinaryFields` and `StandardSMOrdinaryMass`; it constructs a
continuous SU(6) extension agreeing with the existing torus action, rather
than identifying an independently specified natural full charge-sector
action. `StandardSMContinuousTensor` carries the nonzero invariant tensors
to the resulting continuous model's actual radical.
The universal scalar/VEV existence bridge for this full-gauge mass is now
checked above. Prescribed/minimal scalar content and vacuum dynamics,
stronger natural-action identification if required, and Lorentz/Grassmann
semantics and nonvanishing after fermionic antisymmetrization remain separate.
No nonzero Wilson coefficient or amplitude is needed for this tensor task.

## 7. Sources and verification

### Concrete audits

- `WeylYukawaBenchmark.AmbientPair` constructs a nonzero invariant Yukawa
  tensor on the actual full SU(6) representation `6 + 6*`, with a neutral
  scalar. Invariance is under every SU(6) element, not just its Cartan torus.
- `WeylYukawaBenchmark.FullMass` realizes the previously constructed
  continuous-geometry 15-mode example with zero bare mass, nonzero Yukawa,
  and singlet VEV one. `ofMassAsYukawa_toMassModel` preserves the entire mass
  model, so the full radical spectrum and dimension are unchanged. This is
  an algebraic post-breaking compatibility example; it does not assert
  that this particular coupling extends to a full ultraviolet SU(6) scalar
  sector or follows uniquely from dynamics.
- `AuditWeylYukawa` checks a nontrivial order-two Majorana action, finite
  Abelian model constructors, and a regression example where nonzero
  Yukawa with zero VEV gives zero induced mass. Its printed axiom boundary
  contains only the standard three axioms; no `sorry` or new axiom is used.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

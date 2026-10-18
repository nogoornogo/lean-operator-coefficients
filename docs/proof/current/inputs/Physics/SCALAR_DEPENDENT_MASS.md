# Scalar-dependent symmetric masses

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: **LEAN-CHECKED**, MASS-1 and MASS-2, stage 01. Equivariant families,
finite multilinear sources, continuity, and legacy compatibility are checked.
The separate [scalar-dependent model endpoint](../../applications/GUT/SCALAR_DEPENDENT_MODEL.md)
closes MASS-3 in the [roadmap](../../../../topics/mass-profile-foundations/plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md).

## 2. Inputs and conclusion

### Statement

Let an arbitrary group act complex-linearly on scalar space `S` and fermion
space `V`. A coefficient family assigns a symmetric complex bilinear form
`Y(s)` to each scalar value, with

```text
Y(rhoS(g) s)(rhoV(g) x, rhoV(g) y) = Y(s)(x,y).
```

There is **no linearity assumption on the function of s**. If a vacuum `v`
is fixed by the group, evaluation produces an invariant symmetric mass.
An invariant bare mass can be added. More generally, for any homomorphism
`f : K -> G`, it suffices that `rhoS(f(k)) v = v` for every `k`. The
homomorphism need not be injective. Evaluation therefore always gives an
invariant mass for the vacuum stabilizer, without asserting that it equals
the Standard Model group.

The algebra requires no group commutativity, topology, inner product,
unitarity, finite-dimensionality, or GUT embedding. Downstream physical
model classes retain their own hypotheses.

## 4. Proof structure

### Persistent Controls

The [core audit](../../../../../Physics/FieldTheory/Yukawa/Audit/AuditWeylMassFamily.lean)
rejects transitive `GUT.SU5` or `GUT.SU6` imports and checks:

- A compensating scalar/fermion action: `g` in complex units acts as `g^-2`
  on the scalar and `g` on the fermion; `Y(s)(x,y) = s*x*y` is equivariant.
- At vacuum one, the element two does not fix the scalar and the evaluated
  form fails invariance. Thus the fixed-vacuum hypothesis cannot be omitted.
- The same nonzero mass is invariant under the actual vacuum stabilizer.
  The surviving element minus one acts nontrivially on the fermion.
- The nonzero charged coupling gives zero mass at vacuum zero.
- Under trivial actions, `Y(s)(x,y) = s^2*x*y` is genuinely nonadditive in
  `s` and yields a nonzero mass at vacuum one.
- A constant invariant family can give nonzero mass at vacuum zero. The
  general interface does not inherit a linear family's zero-value law.

The complex-unit action is an algebraic control, not a proposed unitary
residual action in a physical GUT model. The separate
[compatibility audit](../../../../../Physics/FieldTheory/Yukawa/Audit/AuditWeylMassFamilyCompatibility.lean)
checks the old linear, bare-mass, singlet-Yukawa, and subgroup interfaces.

The [finite-source audit](../../../../../Physics/FieldTheory/Yukawa/Audit/AuditMultilinearWeylMass.lean)
also rejects transitive SU(5)/SU(6) imports. From actual multilinear maps it
constructs powers, `1+s+s^2`, the mixed coefficient `s1*s2`, and `s*conj(s)`.
It checks nonadditivity, nonzero induced mass, both fields being required
in the mixed example, zero-vacuum controls, and joint continuity. The
conjugate example explicitly fails the complex degree-two scaling law.
A separate charged quadratic example has scalar weight -1 and fermion
weight +1 under complex units; coefficient equivariance gives a nonzero
mass on the vacuum stabilizer and zero mass at scalar zero. Mixed and
conjugate examples use trivial group actions. No audit assumes that every
nonzero coupling yields nonzero mass.

## 6. Scope and limitations

### Implementation Boundary

[InvariantMassData](../../../../../Physics/FieldTheory/Mass/InvariantMassData.lean) isolates
the old `InvariantWeylMass.SymmetricMass`,
`DiracYukawaMass.InvariantVacuum`, and `WeylYukawaMass.vacuumStabilizer`
definitions from legacy SU(6) imports. Their names and old import access
are preserved. The new module uses mathlib only.

[WeylMassFamily](../../../../../Physics/FieldTheory/Yukawa/WeylMassFamily.lean) supplies
`EquivariantFamily`, constant/zero/sum constructions, subgroup restriction,
fixed-vacuum evaluation, and a sector with an invariant bare mass. Restricting
and evaluating a sector commute as an equality of `SymmetricMass` values.

[WeylMassFamilyCompatibility](../../../../../Physics/FieldTheory/Yukawa/WeylMassFamilyCompatibility.lean)
forgets the old Yukawa family's scalar-linearity and proves equality of the
old and new induced masses, including bare-mass, subgroup, and stabilizer
constructions. Legacy imports remain in this adapter, not the generic core.
No index theorem, actual model carrier, or existing selection-rule statement
is changed by the extraction.

### What Is Not Claimed

An arbitrary MASS-1 family remains equivariant input data; not every such
function is polynomial, continuous, or physically admissible. MASS-2
constructs a specific finite multilinear source class, not an exhaustive
Lagrangian parser. Fermion dependence is still bilinear. The checked
[MASS-3 wrapper](../../applications/GUT/SCALAR_DEPENDENT_MODEL.md) adds joint coefficient continuity,
preserves the exact light-target hypothesis, and recovers old linear models.
Its neutral power realization is an unbroken-interface compatibility result,
not a new full-SU(6) scalar geometry.

Nothing here determines a scalar potential, a preferred VEV, a light index,
or a decay amplitude. Ordinary-Abelian assumptions in the existing final
SU(5)/SU(6) theorems are not removed by the arbitrary-group mass lemma.
The existing [linear Yukawa dossier](WEYL_YUKAWA.md) remains valid.

Declarations and reproducible checks are in the
[formalization record](interfaces/scalar-dependent-mass.md).

## 7. Sources and verification

### Finite Sources

[MultilinearWeylMass](../../../../../Physics/FieldTheory/Yukawa/MultilinearWeylMass.lean) defines
`MultilinearCoupling`: a complex multilinear coefficient in a finite,
possibly heterogeneous collection of scalar slots, valued in symmetric
complex bilinear forms on the fermions. Its input equivariance is

```text
C((rhoM_i(g) m_i)_i)(rhoV(g) x, rhoV(g) y) = C((m_i)_i)(x,y).
```

Each slot is a real-linear map `l_i : S -> M_i` satisfying its own covariance
law. Substitution derives the MASS-1 family `Y(s) = C((l_i(s))_i)`.
No invariance of an evaluated mass is assumed. Repeated slots give powers;
projections from a product give mixed-multiplet couplings. Complex-linear
maps restrict to real-linear slots, and complex conjugation is an explicit
real-linear slot whose covariance still must be proved.

For compatible real/complex scalar actions, `realCoefficient` constructs
an actual real multilinear map on independent copies of `S` whose diagonal
is `Y`. The real scaling law is `Y(r*s) = r^card(slots) * Y(s)`.
This is the checked finite-source meaning of polynomial dependence; no
classification of all polynomial functions or holomorphicity theorem is
asserted. In particular, conjugate slots are not silently complex-linear.

An empty slot set recovers the constant invariant family. A single slot
recovers a complex-linear coefficient, including the old Yukawa family and
its subgroup mass by exact equality. `EquivariantFamily.sum` combines
finitely many constructed families of different arities and slot types.
Every positive-arity term vanishes at the zero scalar value, as does a
finite sum of such terms. Constants and an independent bare mass need not.

[MultilinearWeylMassContinuity](../../../../../Physics/FieldTheory/Yukawa/MultilinearWeylMassContinuity.lean)
proves a finite-basis expansion and joint continuity of `(s,x,y) -> Y(s)(x,y)`
when the spaces have the specified finite-dimensional normed structures.
The source is finite-dimensional over the reals; slot and fermion spaces
are finite-dimensional over the complexes. Compatible finite-dimensional
complex sources supply the real-dimensional hypothesis. Finite sums
preserve joint continuity. This statement does not choose a topology on
the algebraic space of bilinear forms, and needs no continuous group action.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

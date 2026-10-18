# Specified flavor symmetry: proved interfaces and boundaries

## Candidate group versus interacting symmetry

[FlavorCandidate](../../../Math/RepresentationTheory/Multiplicity/FlavorCandidate.lean)
constructs the faithful action of the actual unitary centralizer of a specified
gauge representation. `action_commutes` and `ofOperator` verify both the action
and membership of any supplied unitary gauge-commuting operator. `coordinates`
reuses the existing exact equivalence with a product of multiplicity unitary
groups. This concrete unitary interface assumes a finite-dimensional complex
inner-product space and the existing decomposition-model inputs.

This is a candidate mixing group, not yet the symmetry of an interacting
model. Scalar representations, coupling tensors and VEVs must still be
supplied. There is no claim that an arbitrary UV representation produces the
observed species, multiplicities or couplings.

## General algebraic stabilizers

[FamilyStabilizer](../../../Math/RepresentationTheory/FamilyStabilizer.lean)
constructs the exact subgroup fixing a specified family of vectors. `maximal`
states its universal inclusion criterion, `comap` transports the condition
along group maps, and `restricted_fixed` supplies the actual restricted
representation. The family may be empty or infinite. No finite-dimensionality,
unitarity or continuity assumption is imposed here.

[FlavorStabilizer](../../../Physics/FieldTheory/Yukawa/FlavorStabilizer.lean)
applies this to couplings `Y : S →ₗ[ℂ] BilinForm ℂ V`, scalar VEVs and mass
forms. Importantly, the candidate actions are not assumed to preserve `Y`:
`coupling_mem_iff` proves exactly when they do. `dataSubgroup` handles arbitrary
families of couplings, VEVs and bare forms simultaneously.

For a single specified coupling and VEV:

```
Hfull = Stab(Y) ∩ Stab(v)
Hfull ≤ Stab(Y(v))
defect(g) = couplingAction(g)(Y) - Y
```

Within `Stab(v)`, `mass_iff_defect_at_vacuum` proves:

```
g ∈ Stab(Y(v)) ↔ defect(g)(v) = 0
```

`equality_iff_no_hidden_defect` gives the exact necessary and sufficient
condition for `Hfull = Stab(Y(v)) ∩ Stab(v)`: evaluation at `v` must detect
every nonzero coupling-orbit defect for vacuum-fixing candidates. Thus mass
invariance alone does not imply invariance of the full coupling. Bare mass
terms can be included as independent constraints through `dataSubgroup`;
the evaluated-mass theorem above is for `Y(v)`, not cancellation against an
arbitrary bare form.

`defect_zero_of_generators` recovers a whole defect from its values on a
spanning set. `coupling_of_generating_masses` derives coupling invariance from
mass preservation on a generating scalar set, with the scalar-fixing conditions
explicit. No finite basis or finite generation is assumed.

## Existing mass and coefficient interfaces

For a symmetric coupling, `restrictedYukawa`, `restrictedVacuum`, and `sector`
construct the existing `WeylYukawaMass` inputs on the derived subgroup, with
zero bare mass. `sector_mass` proves that the resulting form is precisely
`Y(v)`. The symmetry proof is derived from subgroup membership, not supplied
again as a model-author invariant-coupling assumption.

`residualHomEquiv` identifies invariant linear-map tensors with intertwiners
between the actual restricted representations. It reuses Mathlib's general
invariants/intertwiner equivalence. This supplies a residual group and
representations usable by the existing coefficient-completeness consumers;
their species, gauge/Lorentz and input-field identifications remain required.
It does not assert that the four operator sectors share one flavor group or
automatically realize their model inputs. The parent's surjective-Hom and
kernel-descent interfaces remain available for covering-group presentations.

## Explicit classification and strictness control

[FlavorMajoranaLine](../../../Physics/FieldTheory/Mass/FlavorMajoranaLine.lean)
uses a complex line with the faithful Circle action and symmetric form
`B_c(x,y) = c*x*y`. It proves:

| Specified data | Exact stabilizer |
|---|---|
| `c = 0` | entire Circle |
| `c ≠ 0` | `z² = 1`, group-equivalent to `Multiplicative (ZMod 2)` |
| Neutral scalar coupling `Y_c(s)=s*B_c`, VEV `v ≠ 0` | coupling and evaluated-mass stabilizers agree |
| `c = 1`, `v = 0` | coupling stabilizer has order two; evaluated mass has entire Circle |

`cyclicEquiv` has a verified inverse via the roots-of-unity character;
`nonzero_card` proves cardinality two. `accidental_strict` explicitly exhibits
failure of coupling/mass-stabilizer equality at zero VEV, using a phase whose
square is not one. No external diagonalization or numerical test is a premise.

This pilot classifies the stabilizer inside its stated Circle candidate group;
it is not an arbitrary-dimension Takagi/SVD classification, a full simultaneous
Yukawa-matrix classification, or a vacuum-selection theorem. Full mixing within
degenerate blocks and several nonzero interacting forms remain separate extensions.

## Independent phases on a finite diagonal form

[FlavorMajoranaDiagonal](../../../Physics/FieldTheory/Mass/FlavorMajoranaDiagonal.lean)
uses a finite index set `I`, coefficient family `c : I → ℂ`, and the candidate
group `I → Circle` acting coordinatewise. For
`B_c(x,y) = ∑ i, c i * x i * y i`, `membership` proves exactly
`∀ i, c i = 0 ∨ (z i)^2 = 1`.

`productEquiv` decomposes the actual mass stabilizer into its local line
stabilizers. `mixedEquiv` supplies an explicit group equivalence, including
the inverse, with

```
(zero coefficient indices → Circle) ×
(nonzero coefficient indices → Multiplicative (ZMod 2)).
```

All-zero coefficients give the whole phase candidate group. When every
coefficient is nonzero, `nonzeroEquiv` gives the sign group and `nonzero_card`
proves order `2 ^ Fintype.card I`, including the empty-index case.

`coupling` supplies neutral scalar coordinates; `coupling_evaluation` proves
that evaluation at `v` gives `B_(c*v)`. `coupling_subgroup` identifies the full
coupling stabilizer with `Stab(B_c)`. `evaluation_le` and `evaluation_eq_iff`
prove that evaluation enlarges symmetry, with equality exactly when
`∀ i, c i ≠ 0 → v i ≠ 0`. Losing any nonzero coefficient is therefore a strict
enlargement, not just a sufficient-condition warning.

`residualHomEquiv` transports intertwiners along `mixedEquiv` without changing
their underlying linear maps. `residual_nonzero_iff` preserves existence of a
nonzero residual Hom. The consumer modules need not be finite dimensional.

This is complete **within the independent-phase candidate group**. It does
not diagonalize a supplied arbitrary form or classify its full U(n)
stabilizer. Equal nonzero coefficients can permit mixing beyond this candidate,
and zero blocks can permit a larger unitary mixing group.

## Subsequent full-unitary extensions

The later [diagonal unitary classification](../majorana-unitary-stabilizer/results.md)
handles the full candidate U(n), with U on zero blocks and real O on equal
positive absolute-value blocks. The [Takagi existence extension](../majorana-congruence-interface/existence.md)
then covers every finite complex symmetric matrix without an external
diagonalization premise, including degeneracies, and supplies residual-Hom
transport and exact fixed-target basis freedom. These extensions do not turn
the independent-phase theorem above into a full-unitary theorem, or infer
coupling invariance from evaluated-mass invariance. Simultaneous Yukawa
classification remains excluded.

## Audit

The persistent [strict audit](../../../Physics/FieldTheory/Yukawa/Audit/AuditFlavorStabilizer.lean)
now checks 60 declarations transitively, including the later
[full unitary diagonal Majorana extension](../majorana-unitary-stabilizer/README.md),
permitting only `propext`,
`Classical.choice` and `Quot.sound`. The topic overview records final builds
and integration status. Lean and dependency pins are unchanged.

# Full-group standard branching bridge

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED` for the covering-group map, physical torus
compatibility, the actual `6`/`bar6`/`15` branching, and mass/radical/tensor
transport to a direct-product realization of analytic `15 + 2 bar6`.
An actual physical-torus/residual equivalence now gives a compatible
continuous SU(6) extension on the older `ordinaryFields` carrier and carries
this mass and its radical tensors into a continuous Weyl model.

## 3. Definitions and conventions

### Actual group and actions

`StandardSMGroup.continuousHom` constructs

```text
SU(3) x SU(2) x Circle -> SU(6)
(A,B,z) |-> diag(z^(-2) A, z^3 B, 1).
```

Multiplicativity, unitarity, determinant one, and continuity are proved.
This is a homomorphism from the covering product, not an injective embedding.
`StandardSMTorus.covering_not_injective` exhibits `(I,-I,-1)` in its kernel.
The entire kernel is not classified here.

`StandardSMGroup.fundamentalEquiv` constructs the coordinate splitting
of the algebraic defining action, and `analyticFundamentalEquiv` composes
it with the previously checked continuous-unitary SU(6) realization:

```text
6 restricted to G_SM = (3,1)_(-2) + (1,2)_3 + (1,1)_0 = F.
```

Here the subscripts are integral `6Y`, and F is exactly the heavy
representation in `StandardSMFullGaugeMass`. The inverse map recombines
the first three, next two, and last coordinates. Intertwining is proved
for every group element, including off-diagonal color/weak matrices.

Restriction and contragredient dualization commute by a checked equality.
`analyticAntifundamentalEquiv` then identifies the actual analytic `bar6`
with F*. `StandardSMContragredient.leptonDualEquiv` uses the SU(2) epsilon
pairing to identify the dual of the charge +3 weak block with the charge
-3 lepton. Its `antifundamentalEquiv` therefore constructs

```text
bar6 restricted to G_SM = d_R* + L + singlet.
```

The singlet is represented on the one-dimensional dual of C, with a proved
trivial action. The color dual is retained: replacing it with the defining
color representation would be incorrect.

### Exact torus compatibility

`StandardSMTorus.hom` lifts the four physical circle coordinates into the
covering product. `hom_comp` proves equality of homomorphisms, not merely
of characters:

```text
StandardSMGroup.hom . StandardSMTorus.hom
  = PhysicalSMTorusTarget.embedding (-2) 3.
```

The lift is continuous. `restrict_eq` transfers this equality to the
restriction of any representation. `withResidual_comp` proves the same
commuting diagram after adjoining any Abelian group H acting trivially.
`neutralFundamentalEquiv H` identifies the analytic six with the precise
`heavyRho H` in the mass benchmark. This does not assert a lift of arbitrary
nontrivial residual charge assignments.

## 4. Proof structure

### Exterior square and actual 27-field assembly

`StandardSMExterior.alternating` constructs the alternating map from two
six-vectors to the five SM blocks. Color epsilon gives `u_R*`, the mixed
color/weak tensor gives Q, weak epsilon gives `e_R*`, and wedges with the
fixed sixth coordinate give the two heavy nonsinglet blocks. The universal
property of the exterior power gives `branch`.

`pair_covariant` and `branchIntertwiner` prove covariance for every gauge
element. `range_up`, `range_quark`, `range_electron`, `range_color`, and
`range_weak` exhibit all five components in the image. For Q this uses
tensor-product induction. The proved surjectivity and equal finite dimensions
give bijectivity, not an isomorphism inferred solely from characters.
`analyticEquiv` transfers the result to the existing analytic SU(6) `15`:

```text
15 restricted = u_R* + Q + e_R* + (3,1)_(-2) + (1,2)_3.
```

`StandardSMUVFields.uvRho` is the actual SU(6) direct-product action on
`(exteriorTwo.V x antifundamental.V) x antifundamental.V`, with jointly
continuous action and dimension 27. `gaugeEquiv` combines the checked
branchings and an explicit reorder map to identify its restriction with
`(Light + Heavy) + Heavy*`. One bar6 singlet supplies the heavy singlet;
the second bar6 supplies the full heavy dual. `withResidualEquiv` identifies
this with `StandardSMFullGaugeMass.rho (neutralCharges H)` for any Abelian H
acting trivially. `physicalRestriction_eq` retains the exact torus diagram.

`EquivariantWeylMassTransport` pulls back symmetric masses along arbitrary
representation equivalences, preserving nonvanishing and the radical as
a representation. `StandardSMUVMass.mass` therefore constructs a nonzero
full-SM-gauge-invariant mass on these actual SU(6) fields. Its `lightEquiv`
proves that the radical is exactly the all-left-handed SM representation,
and hence has dimension 15 and the full SM character. The ordered nonzero
`qque`/`duql` tensors are transported to this radical and its dual, with
explicit witnesses equal to one and full gauge-times-neutral-residual
invariance. The mass is not asserted invariant under the full ultraviolet
SU(6); it is a post-breaking SM-invariant mass on actual SU(6) matter.

### Canonical-carrier and continuous-model adapter

`AbelianCharacterEquivalence.ofCharacter` constructs an actual equivalence
between finite-dimensional unitary Abelian representations with equal trace
characters. It uses the proved character-sector eigenbases and multiplicity
matching; character equality is not an assumed isomorphism principle.

`StandardSMOrdinaryFields.physicalEquiv` applies this to the neutral
`ordinaryFields` realization and an orthogonal product of the analytic UV
representations. `su6Rho` transports the actual UV action to the canonical
carrier. `su6_jointlyContinuous`, `physical_restriction`, and
`gauge_restriction` prove continuity and exact agreement with the existing
physical-torus/residual action. This constructs a compatible extension;
it does not identify an independently specified natural full SU(6) action
on the charge-sector carrier. Uniqueness and preservation of that carrier's
original inner product by the chosen equivalence are not claimed.

`StandardSMOrdinaryMass` transports the full-gauge mass without changing
its bilinear form on restriction. It proves full-gauge invariance, nonzero
mass, an actual SM radical equivalence, and the complete charge-resolved
SM spectrum. A proved `PullbackCertificate` retains equality with the
original pullback form and the underlying radical map. Packaging its
proved inhabitant via `Classical.choice` prevents repeated normalization
of the large chosen eigenbasis; no certificate is assumed as an input.
The character calculation subtracts the heavy `6 + bar6`
from the proved UV trace; it is not inferred from dimension alone.
`continuousModel` uses the existing mass-preserving continuous-geometry
adapter. `StandardSMContinuousTensor` transports the full-gauge radical
action and both nonzero invariant tensors to that model's actual radical,
with a proved equality to its original torus action and witnesses equal
to one. The analogous split-projection certificates retain exact equality
with both original tensor pullbacks (`qque_form_eq`, `duql_form_eq`);
their nonzero and invariant fields are proved, not supplied as hypotheses.
All residual actions in this UV example are neutral. During tensor type
comparison, the already constructed benchmark matter is locally treated
as irreducible to avoid unfolding its charge-sector list. This changes
elaboration only, not the definitions or the kernel trust boundary.

## 7. Sources and verification

### Audit and remaining boundary

`AuditStandardSMBranching` is imported by the root build. It checks an
explicit off-diagonal SU(2) rotation, the noninjectivity result, analytic
representation equivalences, and neutral residual actions including a
two-element Abelian group. All audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry` or new axiom is used.
`AuditStandardSMUVMass` additionally checks color/weak/mixed exterior signs,
the 27-field/15-mode benchmark, finite-Abelian neutral actions, and the
negative control that zero mass instead leaves all 27 modes. All new
audited declarations have the same three standard axioms. The current full
build is recorded in [historical verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).

`AuditStandardSMOrdinaryModel` checks the continuous-model mass, complete
spectrum, tensor witnesses and invariance, and a zero-mass/27-mode negative
control. Its audit includes the generic character-equivalence and continuity
lemmas and the exact restriction equalities.

The concrete ultraviolet-to-radical bridge now includes a compatible
canonical-carrier extension and a continuous-model inhabitant. Equality
with `ConcreteWeylFullMass`'s torus-eigenbasis mass is not asserted. An
identification with an independently specified natural full charge-sector
action remains a stronger, optional task.
`StandardSMUVYukawa` now gives a full-SU(6)-invariant scalar/Yukawa/VEV
existence realization of this mass, with a jointly continuous unitary scalar
representation and zero bare mass. The scalar space consists of all
symmetric bilinear forms; the mass is chosen through its VEV, not predicted
from dynamics. Its `ordinary_form` proves the exact coefficient pullback
to this canonical-carrier mass. See [the scalar dossier](../Physics/WEYL_YUKAWA.md).
The [stabilizer audit](SM_VACUUM_STABILIZER.md) now proves strict containment
of SM in this VEV's stabilizer, without changing the mass or branching.
Arbitrary residual assignments, prescribed/minimal Higgs content, vacuum
dynamics, a different or augmented VEV with exactly SM stabilizer,
Lorentz/Grassmann nonvanishing, and decay amplitudes remain outside this
result; see [the mass boundary](../../applications/GUT/SM_GAUGE_MASS.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

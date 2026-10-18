# Full-gauge mass and radical tensors

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED` for the decomposed post-breaking model and its
pullback to actual analytic SU(6) `15 + 2 bar6` with neutral residual action.
The compatible `ordinaryFields` extension and continuous-model adapter are
now constructed, without claiming uniqueness of the full-group extension.
See [the verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md) for the recorded full-build result.

## 4. Proof structure

### Constructed mass, not assumed zero modes

`SplitWeylMass` works for any group G and representations L and F. On
`(L + F) + F*`, the projection `L + F -> F` defines a symmetric coefficient

```text
B(((l,f),phi), ((l',f'),phi')) = phi'(f) + phi(f').
```

Its invariance under the entire group follows from the contragredient
action. The kernel calculation proves `f = 0` and `phi = 0`; it does not
assume the desired spectrum. `radicalEquiv` identifies the actual radical
with L as a representation, so both dimension and full character follow.

`StandardSMFullGaugeMass` specializes this to `GaugeGroup x H`, with any
Abelian residual group H and declared field charges:

- L is the all-left-handed SM space `Q + u_R* + d_R* + L + e_R*`, of
  dimension 15. The duals are essential; this is not a sum of five
  physical right/left field spaces with their unmodified charges.
- F is `(3,1)_{-2} + (1,2)_3 + (1,1)_0`, with charges in units of 6Y and
  trivial residual action. It has dimension 6.
- Total field dimension is 27, mass is nonzero, and radical dimension is
  exactly 15. A heavy vector/covector pairing explicitly evaluates to one.

The mass exists for arbitrary residual assignments because the light
summand is unpaired. Its existence alone is not a no-go theorem and does
not imply that arbitrary assignments have an SU(6) source.

### Tensors on the actual radical

`SplitRepresentationProjection` supplies equivariant projections with
explicit right inverses, their composition and tensor products, and their
contragredient/bidual counterparts. The right inverse proves that pulling
back a nonzero tensor cannot turn it into zero.

`StandardSMRadicalTensor` uses the computed radical equivalence to obtain
these projections. Writing K for the actual all-left-handed radical, the
constructed ordered internal gauge tensors have domains

```text
qque : (K tensor K) tensor (K* tensor K*) -> C
duql : (K* tensor K*) tensor (K tensor K) -> C.
```

Right-handed slots come from K*, not K. Their projection uses the dual of
the left-handed-conjugate inclusion, followed by the canonical bidual
equivalence. The tensors have witnesses with value one and transform with
exactly the Abelian proton-operator neutrality proton characters. Trivial characters give full
gauge-times-residual intertwiners.

`source_benchmark` uses the charges of a checked standard charge-orbit bridge source to obtain these
invariant tensors in the **new benchmark**. It does not identify this
benchmark with a mass sector originally underlying that source.

`AuditStandardSMRadicalTensor` constructs the 27/15-dimensional example
with nontrivial finite-group charges and no spectrum/support assumption.
Incompatible charges instead give minus one on transformed witnesses.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

### Actual SU(6) bridge

`StandardSMUVFields.gaugeEquiv` now proves the full-gauge equivalence from
the actual analytic `15 + 2 bar6` direct-product representation, using
explicit exterior contractions and the proved `bar6` branching. Its
physical-torus and neutral residual compatibility are checked.
`StandardSMUVMass` pulls back the mass above to those actual SU(6) fields,
proves its nonvanishing and exact 15-dimensional SM radical, and transports
both ordered nonzero invariant tensors to that radical and its dual.
Neither the desired spectrum nor a representation-equivalence certificate
is an input to this construction. See [the branching dossier](../../inputs/GUT/SM_BRANCHING.md).

`StandardSMOrdinaryFields` proves a physical-torus/residual equivalence
with the `ordinaryFields` carrier and constructs a compatible continuous
SU(6) extension there. `StandardSMOrdinaryMass` transports this mass into
the standard and continuous Weyl interfaces, preserving nonzero mass and
the complete 15-mode charge-resolved SM spectrum. `fullMass` and
`mass_form_eq` retain full-gauge invariance on the canonical carrier, and
`continuous_mass_heq` records preservation of the mass in the adapter.
`StandardSMContinuousTensor` places both nonzero invariant ordered tensors
on the continuous model's actual radical and proves restriction compatibility.
The extension is constructed by conjugation, not identified with an
independently specified natural full charge-sector action.
The new mass is not asserted equal to the old torus-eigenbasis mass.
`StandardSMUVYukawa.mass_eq` now realizes it with zero bare mass, a
full-SU(6)-invariant Yukawa family on a continuous unitary scalar space,
and a nonzero SM-fixed VEV. This uses all symmetric bilinear forms as a
universal nonminimal scalar space; it does not specify a scalar potential.
The [stabilizer audit](../../inputs/GUT/SM_VACUUM_STABILIZER.md) now proves that this same
VEV has a stabilizer strictly larger than SM. The mass and 15-mode radical
are retained, but an exact-SM vacuum requires additional construction. See
[the scalar construction and audit](../../inputs/Physics/WEYL_YUKAWA.md).
Arbitrary residual assignments need not lift. All older examples and
endpoints are unchanged.

Lorentz factors, the fermionic quotient, and nonvanishing after imposing
anticommutation remain separate. No nonzero Wilson coefficient or decay
amplitude is asserted.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

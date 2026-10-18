# Finite SM charge profiles

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Scope

**LEAN-CHECKED: PROFILE-1 coefficient algebra.** The five left-handed
species may have different charges in different generations. The common
layer does not assume an SU(6) source. It reuses the normalized rank-four
SU(5) weight coordinates for the SM target and has an audited SU(6)-free
import closure.

For an additive Abelian label group `A`, each species has a finite profile
`A ->0 Nat`. A `Family` supplies a common **positive** total `N` for all five
species, not equal distributions. Physical labels are
`Additive (H ->* Circle)`, the characters of the residual group, not its
elements. No finiteness or torsion-free assumption on `A` is needed.

Natural occupation numbers are embedded injectively into integer virtual
coefficients. Independent singlet data remains `A ->0 Int`: it is an index,
not a reconstruction of the full singlet spectrum.

## 2. Inputs and conclusion

### Target And Compatibility

`FiniteSMTarget` owns the existing fifteen distinct, nonzero oriented SM
weights. These definitions and the old single-charge targets were moved
out of `SU6/Branching/StandardSMCharacterTarget`; their declaration names
and old import entry point are preserved. The SU(6) file retains its
physical evaluator, faithfulness proof, and actual-representation adapters.

`FiniteChargeProfiles.targetWithSinglets` assigns the entire species
distribution to every weight of that species, plus the singlet index at
weight zero. Checked results include:

- At every one of the fifteen SM weights, the coefficient at charge `q`
  is exactly the species' natural multiplicity at `q`, cast to an integer.
- The five representative charge profiles recover the input distributions;
  arbitrary charged singlets do not alter them.
- Forgetting charges sums collisions and yields `N` copies of the fifteen
  SM weights plus the total singlet index at zero weight.
- Profiles concentrated at one assigned charge per species recover
  `exactSMWithSingletsResolvedCharacter N charges singlets` exactly.
  Existing signed-index targets and negative-orientation results are retained;
  this new `Family` interface covers positive orientation only.

## 4. Proof structure

### Conditional Neutrality

The additional predicate `OrbitCompatible` is

```text
P_Q = P_u, P_Q = P_e, P_d = P_L.
```

It is **not** a field of `Family`. Conditional on these equalities, positivity
provides occupied charges `q` and `r`; selecting `(q,q,r,r,q)` gives both
`protonFirst = 0` and `protonSecond = 0`. For actual residual-character labels,
both characters are trivial. `ProfileOperatorSignatures` packages the two
existing supported invariant `qque`/`duql` signatures at this same choice.

Here “supported” means **supported by the target coefficients**. Neither
actual mass-radical vectors nor nonzero dynamical interaction coefficients
are constructed in PROFILE-1. The generic full-gauge tensor and
Grassmann/Lorentz boundaries are unchanged.

### Checked Bridges

The [PROFILE-2 extension](../../applications/GUT/PROFILE_ZERO_MODES.md) now uses the **dual** light
target to prove positive actual radical multiplicities and construct
corresponding vectors. The [PROFILE-3a endpoint](../../applications/GUT/PROFILE_MODEL.md) now derives
profile equalities from the actual source and connects charge-forgetting to
hypercharge rigidity. The [retained SU(5) source adapter](SU5_CHARGE_PROFILES.md)
and [actual nonuniform-charge SU(6) example](../../applications/GUT/NONUNIFORM_PROFILE_MODEL.md) now
complete the final acceptance gates.

See the [extension plan](../../../../topics/mass-profile-foundations/plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md),
[declaration record](../../applications/GUT/interfaces/finite-charge-profiles.md), and
[historical profile milestone](../../../../topics/mass-profile-foundations/checkpoints/profile-example.md).

## 7. Sources and verification

### Audit

[AuditFiniteChargeProfiles](../../../../../Physics/StandardModel/Spectrum/Audit/AuditFiniteChargeProfiles.lean)
is imported by `GUT.lean` and checks:

- Actual circle-valued characters of `Multiplicative (ZMod n)`, using
  mathlib's injective `ZMod.toCircle`; nontrivial order-two and order-three
  characters are explicitly tested.
- Three-generation distributions with two neutral and one charged ten
  sector, and three repeated charged anti-five sectors. The two occupied
  ten charges are distinct; the ten and anti-five distributions differ.
- Conditional neutral signatures with arbitrary singlet index data.
- Exclusion of zero generation total.
- A one-generation incompatible family with the correct uncharged target
  but no occupied assignment making either proton functional zero. This
  is a coefficient-level negative control, not a proposed UV realization.
- No transitive SU(6) imports; audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

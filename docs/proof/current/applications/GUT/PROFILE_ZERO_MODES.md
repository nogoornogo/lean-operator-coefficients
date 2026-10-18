# Actual zero modes from finite charge profiles

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Scope

**LEAN-CHECKED (stage 01).** PROFILE-2 extends the positive-orientation dual-index support argument to
family-dependent profiles. The hypotheses are a finite-dimensional unitary
action of the physical compact torus times an Abelian residual group, an
invariant symmetric mass, and equality of the radical's dual character with
the specified profile target. No radical support or eigenvectors are assumed.

The analytic adapter currently imports the existing SU(6) evaluator and
actual-spectrum infrastructure, but its field representation is arbitrary.
The coefficient algebra has a separately audited SU(6)-free import closure.

## 4. Proof structure

### Argument

1. The fifteen oriented SM weights are disjoint from their negatives.
   Therefore the profile target at `(-w,-q)` vanishes for every oriented
   SM weight `w`, even if `q = -q` in the residual character group.
2. Faithful character evaluation identifies the dual difference of the
   actual radical spectrum with the dual profile target.
3. At each species weight and charge, the resulting equality is
   `actual(w,q) - actual(-w,-q) = profile(q)`.
   Actual multiplicities are nonnegative, hence `actual(w,q) >= profile(q)`.
4. Positive occupation supplies a genuine nonzero vector in the mass
   radical with that torus weight and residual character, at every one of
   the fifteen weights required by the signature interface.
5. Conditional on the orbit-profile equalities, PROFILE-1 selects occupied
   charges for which both `qque` and `duql` are neutral. The new witnesses
   are supported by the **actual radical spectrum**, not only the target.

`ProfileChiralIndex.orbitCompatible_of_dual_target` additionally proves
the coefficient-level implication from a Weyl-invariant source and dual
target equality to the profile equalities. Supplying that source from a
general-cocharacter physical model is now checked in the
[PROFILE-3a endpoint](PROFILE_MODEL.md).

## 6. Scope and limitations

### Preserved Boundaries

- Extra vectorlike zero modes do not change the dual index and are allowed.
- Self-dual singlets can disappear from that index; no singlet reconstruction
  or exact full-spectrum theorem is claimed.
- Nonzero signed support alone is insufficient. The negative control has
  dual coefficient `-1` but zero actual coefficient in the requested orientation.
- The old negative-index endpoints remain intact and separate.
- Actual torus/residual eigenvectors do not alone provide full SM field
  intertwiners, nonzero internal tensors on a general radical, or a nonzero
  decay amplitude. Those boundaries are unchanged.

## 7. Sources and verification

### Implementation And Audit

- `Physics/StandardModel/Spectrum/SMChiralIndex` extracts the old duality and Weyl-compatibility
  algebra without changing declaration names or the old import entry point.
- `Physics/StandardModel/Spectrum/ProfileChiralIndex` proves conjugate-weight separation,
  profile recovery, multiplicity lower bounds, and the conditional orbit bridge.
- `SU6/SelectionRules/Models/ProfileZeroModeSupport` proves the actual
  character, radical-vector, and supported-signature statements for arbitrary
  unitary fields and invariant symmetric masses. Legacy targets and spectra
  are recovered exactly.
- `AuditProfileChiralIndex` covers order-two charged profiles, arbitrary extra
  conjugate pairs, invisible self-dual singlets, and wrong-orientation support.
- `AuditProfileZeroModeSupport` applies the new interface to the nonzero mass
  with exactly 15 modes and to the nonzero mass with 26 modes. Neither test
  supplies radical vectors or assumes orbit support.

See [the declaration record](interfaces/finite-charge-profiles.md),
[the extension plan](../../../../topics/mass-profile-foundations/plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md), and
[the verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

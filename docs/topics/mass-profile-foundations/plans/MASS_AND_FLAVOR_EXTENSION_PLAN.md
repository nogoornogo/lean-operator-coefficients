# Mass-source and flavor-profile extension plan

Archived checkpoint; not a current work queue. Consult the current topic records.

Status: **MASS-1 through MASS-3 and PROFILE-1 through PROFILE-3 LEAN-CHECKED**.
Agreed direction stage 01. Execute candidate 1 (mass sources) before candidate 2
(charge distributions). Pending milestones live in
[Topic records](../../README.md); verified results move to
[Historical milestones](../../proof-program-context/checkpoints/README.md).

## Purpose and Boundaries

Broaden reusable inputs to the existing selection-rule theorems without
creating a separate proof of the common algebra for each ultraviolet group.
Preserve all checked SU(5), SU(6), and generic representation-theory results.

The two extensions have different meanings:

- Candidate 1 removes scalar-linearity from the Yukawa source interface.
  The mass-level theorem already accepts arbitrary invariant symmetric
  masses. This extends the source bridge, not its selection-rule conclusion.
- Candidate 2 replaces the single-charge-per-species SU(6) infrared target
  with finite charge distributions. Family-dependent charge-profile lemmas
  already exist, and the SU(5) retained-spectrum theorem already permits
  family-dependent actions. The new work is the general mass/zero-mode
  bridge and its connection to the SU(6) endpoint, not a claim that the
  whole project previously excluded family dependence.

Keep finite-dimensional complex matter, the stated exact index matching,
and strict commuting unitary Abelian residual actions in the final model
theorems. The mass-source algebra itself may use an arbitrary group.
Retain the distinct signed Dirac and dual symmetric-mass index conventions.

No non-Abelian residual-symmetry extension, new GUT group, arbitrary light
chiral exotics, extra gauge factor, CKM reconstruction, quantum anomaly
analysis, or scalar-potential dynamics is part of this roadmap. The VEV
remains input data. No exact-SM stabilizer, full Lagrangian semantics,
Lorentz/Grassmann nonvanishing, Wilson coefficient, or decay amplitude is
to be inferred. The general SU(6) endpoint remains a supported-signature
theorem; SU(5)'s separately proved actual internal tensors are preserved.

## Reuse and Ownership

Use a common chain with explicit group-specific adapters:

```text
equivariant scalar-dependent coefficient + fixed vacuum
  -> invariant finite-dimensional mass
  -> conserved charge-resolved index + supplied infrared target
  -> occupied actual light sectors + derived compatible charges
  -> supported neutral operator signature
```

The index target is an applicability condition, not derived from arbitrary
couplings. The charge-profile equalities must be derived from the actual
ultraviolet source in each final adapter. Their derivation is not a
group-independent theorem about every GUT.

Put generic mass constructions under `GUT/FieldTheory`, generic character
facts under `GUT/RepresentationTheory`, and SM field/profile algebra under
`GUT/StandardModel`. Keep actual group geometry and branching in their
existing group directories. These are ownership boundaries, not a request
for a broad file move. Audit transitive imports; a generic-looking path is
not evidence of independence. Extract only prerequisites actually needed,
preserving legacy declarations and wrappers.

Key existing foundations:

- [WeylYukawaMass](../../../../Physics/FieldTheory/Yukawa/WeylYukawaMass.lean): scalar-linear
  coefficients, fixed-vacuum evaluation, and subgroup restriction.
- [CharacterExact](../../../../Math/RepresentationTheory/Characters/CharacterExact.lean) and
  [InvariantWeylMass](../../../../Physics/FieldTheory/Mass/InvariantWeylMass.lean): the two
  index mechanisms; do not re-prove them for each gauge group.
- [ContinuousWeylYukawaModel](../../../../GUT/SU6/SelectionRules/Models/ContinuousWeylYukawaModel.lean):
  the existing source-to-mass adapter.
- [StandardPhysicalSource](../../../../GUT/SU6/SelectionRules/StandardBranch/StandardPhysicalSource.lean):
  occupied family-dependent profiles and character-level neutrality.
- [PhysicalWeylZeroModeSupport](../../../../GUT/SU6/SelectionRules/Models/PhysicalWeylZeroModeSupport.lean):
  positive multiplicity in the actual radical from a dual-index target.
- [SU(5) source](../../../proof/current/inputs/GUT/interfaces/su5-source.md) and
  [selection rule](../../../proof/current/applications/GUT/SU5_SELECTION_RULE.md): actual family-dependent sectors
  and the stronger retained-spectrum tensor boundary.

## MASS-1: Equivariant Coefficient Families

**LEAN-CHECKED** (stage 01); see the
[family and compatibility dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md). The requirements
below record the discharged acceptance specification.

Generalize the symmetric Yukawa coefficient from a linear map
to a family `Y : S -> BilinForm C V`, symmetric in its fermion arguments,
with a proved simultaneous equivariance law

```text
Y(g.s)(g.x, g.y) = Y(s)(x, y).
```

For an invariant bare mass and a vacuum fixed by the specified unbroken
subgroup, construct the mass `B_bare + Y(v)` and prove its invariance.
The proof must not use linearity in `s`. It must still use complex
bilinearity in the fermions: this is not a nonlinear fermion-field theory.

An arbitrary equivariant family is the algebraic interface, not a claim
that every such function is a polynomial, smooth, or physically admissible.
Provide an adapter from the old linear family and prove equality of the
resulting masses. Keep the existing public APIs unchanged.

Acceptance: arbitrary-group and subgroup statements; old linear/bare-mass
compatibility; a fixed-vacuum positive example and a non-fixed-vacuum
control. Do not require the entire ultraviolet group to fix the vacuum.

## MASS-2: Finite Higher-Degree Sources

**LEAN-CHECKED** (stage 01); see the finite-source construction and
continuity in the [family dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md). The requirements
below record the discharged acceptance specification.

Construct the MASS-1 interface from actual finite multilinear
scalar couplings and their finite sums, including constant and linear terms.
Evaluating repeated scalar arguments gives higher-degree dependence;
heterogeneous slots allow several scalar multiplets. Reuse mathlib's
multilinear/tensor APIs after checking the pinned versions.

Treat conjugate scalar slots explicitly where used. A holomorphic complex
polynomial must not be advertised as covering arbitrary expressions in
both a scalar and its conjugate. Prove continuity for the finite-dimensional
constructions when passing them to a continuous physical-source interface.

Acceptance: at least one genuinely nonlinear coefficient on the original
scalar space, with proved equivariance and nonzero induced mass; a mixed
scalar example; zero-vacuum behavior for positive-degree terms; recovery of
the linear special case. A nonlinear source must be built from coefficients,
not by assuming the invariance of its evaluated mass. No assumption that a
nonzero coupling always gives a nonzero mass is permitted.

## MASS-3: Existing Endpoint Adapter

**LEAN-CHECKED** (stage 01); see the
[scalar-dependent model endpoint](../../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md). The requirements
below record the discharged acceptance specification.

Connect the constructed families to the existing SU(6)
continuous symmetric-mass endpoint. Derive the mass from the new source
data, then reuse its index and selection-rule theorems unchanged. Recover
the old scalar-linear model by a mass-preserving conversion.

Construct a higher-degree source recovering a checked nonzero benchmark
mass, so its proved light target and support transfer by equality. Record
whether a given example supplies full ultraviolet scalar geometry or only
the existing unbroken-group interface; do not silently upgrade the latter.

Acceptance: source-to-mass-to-selection-rule composition, old-model
compatibility, and a non-vacuous nonlinear example. SU(5)'s retained-spectrum
theorem is a regression consumer, not a new mass-removal theorem. Extending
its model class to integrate out heavy matter is not required here.

This closes candidate 1. A nonlinear Dirac-source wrapper is a later reuse
opportunity, not a second mandatory mass convention for this first extension.

## PROFILE-1: Finite Charge Distributions

**LEAN-CHECKED (stage 01).** The
[profile dossier](../../../proof/current/inputs/GUT/FINITE_CHARGE_PROFILES.md) records the implementation,
pure-target compatibility, finite-character audits, and negative control.
The requirements below describe this completed coefficient-algebra milestone;
actual radical support and the final source bridge were discharged in PROFILE-2/3.

Define five finitely supported nonnegative profiles, one for
each left-handed SM species, over an arbitrary additive Abelian label group
`A`. For physical residual actions use `A = Additive (H ->* Circle)`, not
elements of `H` as charges. Distinguish these natural multiplicities from
the integer coefficients of a virtual index.

The first target has a common positive total `N` for each species, but
does not prescribe equality of their distributions. Build the corresponding
resolved SM target, with independent singlet index data. Prove that
forgetting charges gives `N` ordinary SM generations plus singlets. Recover
the old target when each profile is concentrated at its specified charge.

At the common conditional algebra layer, prove that
`P_Q = P_u = P_e` and `P_d = P_L`, together with occupied profiles, supply
suitable common-charge sectors and neutral `qque`/`duql` signatures. A final
physical model must not take those equalities as independent assumptions.

Acceptance: different generation charges, repeated charges, order-two and
odd-order residual characters, and the zero-total exclusion. Audit an
incompatible set of profiles with the same uncharged totals: equality of
totals alone must not imply charge compatibility or neutrality.

## PROFILE-2: Actual Zero-Mode Support

**LEAN-CHECKED (stage 01).** See the
[actual-support dossier](../../../proof/current/applications/GUT/PROFILE_ZERO_MODES.md). The conditions below are
the completed positive-orientation support milestone; the final actual-source
assembly was discharged in PROFILE-3.

Lift the profile target through the actual finite-dimensional
mass representation. First use the symmetric-mass dual index and reuse the
existing actual character spectrum and faithful evaluation. At an oriented
SM key the needed argument has the form

```text
actual(w,q) - actual(-w,-q) = profile_species(q) > 0
  -> actual(w,q) > 0
  -> a nonzero vector in the corresponding radical eigenspace.
```

Prove that the conjugate target does not contribute at the oriented SM
keys, including residual groups with two-torsion. Do not replace positivity
by a merely nonzero signed virtual coefficient. Assemble support at all
weights required by the declared operator-signature interface.

Acceptance: genuine radical vectors and supported signatures; extra
vectorlike zero-mode pairs do not invalidate the argument; self-dual and
singlet modes are not reconstructed from the dual difference. Nonzero
torus weight sectors alone do not certify a full SM field intertwiner or
an invariant internal tensor on the general radical.

The new profile endpoint initially uses positive orientation. Preserve the
old negative-index and signed Dirac theorems without silently identifying
their conclusions with this one; their profile extensions are deferred.

## PROFILE-3: Source-Derived Final Assembly

**LEAN-CHECKED (stage 01).** The [PROFILE-3a endpoint](../../../proof/current/applications/GUT/PROFILE_MODEL.md) is
Lean-checked: actual source, hypercharge, profile equalities, radical support,
scalar-family composition, and positive legacy compatibility. The
[SU(5) adapter](../../../proof/current/inputs/GUT/SU5_CHARGE_PROFILES.md) (PROFILE-3b) and
[actual nonuniform example](../../../proof/current/applications/GUT/NONUNIFORM_PROFILE_MODEL.md) (PROFILE-3c) are also
checked. The requirements below record the discharged acceptance specification.

Replace the single-charge target in a new SU(6) symmetric-mass
wrapper by PROFILE-1, preserving the existing wrappers as special cases.
Forgetting charges must feed the existing hypercharge-rigidity theorem on
the original actual source. After deriving the standard embedding, the
Weyl-orbit argument must derive the equal charge distributions. Apply
PROFILE-2 to obtain actual supported neutral operators.

Retain the flipped obstruction as an independent lemma. Neither a
continuous-U(1) anomaly equation nor a new charge-equality/support premise
may replace the source bridge. Compose with MASS-3 so both extensions can
be used together without duplicating the mass-index argument.

Connect the existing SU(5) retained matter to the common profile API as a
compatibility test. Keep its actual field maps and ordered tensors; do not
weaken its checked theorem or assert that its matter is now derived from a
general mass sector.

Acceptance: old fixed-charge special case, finite Abelian specialization,
and an actual SU(6) example with at least two distinct occupied residual
characters. Derive its target rather than postulating it. A sum of existing
copies with different commuting scalar characters was the candidate;
PROFILE-3c now constructs it for a nontrivial order-two character and proves
its target. Both SU(5) and SU(6) regressions pass.

## Verification and Stop Conditions

Before each milestone, search the pinned libraries and existing generic
modules for reusable statements. Keep dependency revisions fixed. The
generic cores must not use an actual SU(5)/SU(6) embedding, branching result,
or source certificate as a hidden premise. Report inherited imports and
extract only small generic prerequisites where necessary.

At each proof milestone run targeted audits, print the public declarations'
axioms, and run the full `lake build`. Persistent positive and negative
controls belong in the repository. No `sorry`, new unproved axiom, or
native-decision trust extension is an acceptance substitute.

Update the focused proof/declaration dossier, move only verified work from
ACTIVE to COMPLETED, append a concise history entry, and commit. Preserve
the last recorded build until a new build actually succeeds. This planning
change needs link/diff checks, not a new Lean build claim.

If a bridge needs an additional physical premise, expose it and reassess
the target rather than encode the intended conclusion in the model. If an
audit finds a counterexample, retain the checked older theorems and record
the precise failing extension. External upstream work remains separate.

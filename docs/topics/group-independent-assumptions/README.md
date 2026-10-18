# Assumptions Without A UV Unification Group

- ID: group-independent-assumptions
- Status: completed
- Result type: proved actual-source counterexample in the frozen finite mass interface
- Working branch: `proof/group-independent-assumptions`
- Integration target: `master`
- Topic endpoint commit: `checkpoint 01`
- Integration: merged into `master` with `--no-ff`; working branch retained

## Endpoint And Frozen Scope

Construct a countermodel after removing the UV unification group and its
charge-orbit constraints. Keep the SM gauge group, a finite ordinary Abelian
residual action commuting with it, finite-dimensional unitary matter, an invariant
symmetric bilinear mass, and the positive charge-resolved light dual index of
three SM generations. Zero mass is allowed; empty matter/support is not.

Refute precisely the existing `ForbidsEverySupportedPhysicalDeltaBOneOperator`
no-go, not a claim about all possible baryon-violating operators. Its predicate
is the declared four-fermion dimension-six class with two left and two right
Weyl slots. No Wilson coefficient, decay amplitude, realistic mass hierarchy,
or vacuum dynamics is asserted.

Quantum anomaly cancellation (including gauging the residual group or coupling
to gravity) is outside this finite linear-algebra interface and is not claimed.
Literature motivates the triality assignment but is not a Lean axiom. Do not
retain `SU5OrbitCompatible` or `ResolvedWeylInvariant` as premises: their derivation
is exactly the UV structure removed. Preserve all existing no-go theorems.

## Milestones And Acceptance

1. **Charge and supported-spectrum counterexample.** Use left-handed charges
   `(Q, u^c, d^c, L, e^c) = (0, 0, 0, 1, -1)` in `ZMod 3`, lift to actual
   circle-valued characters of `Multiplicative (ZMod 3)`, and prove every supported
   signature in the declared class is forbidden. Check positive common totals,
   nonempty support, and failure of the SU(5) orbit condition. Reuse actual SM
   tensors as a cross-check without claiming a mass-radical identification.
2. **Actual source.** Realize three generations as an SM times residual-group
   representation; verify unitarity, continuity, commuting actions, and invariant
   zero symmetric mass. Identify the light dual index and actual support.
3. **Endpoint audit.** Bundle the retained assumptions with the prohibition;
   audit imports and transitive axioms. State exactly which group-free claim is
   refuted, then hand off to the structural-conjugation topic.

Use shared SM representation APIs first; the only alternate route is an explicit
finite block-matrix realization of the same matter. Do not develop new Lie
theory, change dependency pins, complete E6 topology, or formalize quantum
anomalies. Stop if either route requires a new prerequisite outside these
interfaces or a change of physical scope.

Each milestone requires focused builds, strict transitive axiom audits, full
`lake build`, layout/link checks and `git diff --check`. Commit milestones
separately; merge only after the full topic acceptance gate passes.

## Progress

| Milestone | State | Evidence / remaining work |
| --- | --- | --- |
| 1 | completed | [Charge checkpoint](charge-counterexample.md): supported spectrum and actual canonical tensor checks |
| 2 | completed | [Actual-source construction](actual-source.md) and [joint spectrum bridge](spectrum-bridge.md): full radical spectrum, dual index and nonzero joint eigenvectors |
| 3 | completed | `actual_source_counterexample`; strict import and transitive axiom audit, full regression build |

## Result And Next Boundary

The group-free no-go is refuted for the frozen assumptions. The actual
45-dimensional continuous unitary SM source with its commuting order-three
residual action has zero invariant symmetric mass, the specified positive
three-generation dual target, nonempty actual support, and prohibition of every
supported signature in the declared class. The spectrum equality is derived
from actual traces and faithful evaluation, not supplied as a certificate.

All planned proof obligations for this topic are closed. Preserve the narrower
operator and anomaly scope above. The separate structural-conjugation topic
is next in the research order, but needs its own bounded statement and branch;
no E6 topology, quantum anomaly or new mass-hierarchy work is opened here.
This is the canonical status record; retired global active/completed
compatibility indexes have been removed and must not be recreated.

## Current Verification

Final focused build of
`Physics.StandardModel.Spectrum.Audit.AuditLeptonTrialitySpectrum` passed (3869
jobs), with 19 strict transitive axiom checks and a no-GUT-application-import
check. The earlier charge and actual-source audits remain registered (12 and
19 checks respectively).

Full `lake build` passed (5556 jobs). Layout: 540 modules, no errors.
Documentation links passed for all 222 Markdown files. `git diff --check`
passed. New Lean files have no warnings; unchanged files retain their
previous warnings. Shared-coordinate proof bodies were mechanically compared
with the preceding commit and are unchanged. No dependency pins, theorem
assumptions, or axiom allowlists were weakened. Build logs are disposable;
all required Lean sources and audits are tracked.

## References

- [Current assumptions](../../proof/ASSUMPTIONS.md)
- [Physical model interface](../../proof/current/applications/GUT/MODEL_INTERFACE.md)
- [Shared selection rules](../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md)
- [Structural follow-up](../structural-conjugation/README.md)

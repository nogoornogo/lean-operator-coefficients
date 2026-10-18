# Vacuum Evaluation and Mass Family Protection

- ID: yukawa-vacuum-protection
- Status: completed
- Checkpoint detail: completed; integration recorded by Git.
- Working branch: `proof/yukawa-vacuum-protection`.
- Integration target: `master`.

## Frozen Endpoint

For arbitrary UV and residual groups, scalar and product matter representations,
evaluate an actual indexed family of invariant Yukawas at a residual-fixed
vacuum. Include a fixed UV-invariant bare mass. Characterize extension of a
specified residual mass and preservation of its radical by the evaluated
cross terms. Show that equal vacuum evaluations give equal generated masses.
Stop after this general bridge is verified; no SU(6) decomposition, potential,
surjectivity onto all invariant masses, or physical amplitude is required.

The parameter set is arbitrary. The original radical must be fixed and every
member must extend its mass for the protection criterion. These hypotheses
are explicit, not consequences of invariance alone.

## Implementation

- [Actual evaluated family](../../../Physics/FieldTheory/Yukawa/VacuumMassProtection.lean)
- [Strict audit](../../../Physics/FieldTheory/Yukawa/Audit/AuditVacuumMassProtection.lean)
- [Existing protection classification](../invariant-mass-protection/README.md)
- [Prior evaluation milestone](../yukawa-full-space/README.md)

The prior topic was integrated as `checkpoint 01` with dimensions 22 and 17 deferred.
This topic reuses its general motivation, not its numerical classification.
No external source, literature premise, pin change or axiom is introduced.

## Result and boundaries

`mass` evaluates actual full-UV invariant Yukawas at a residual-fixed vacuum.
`extends_iff` states the exact condition for the old mass block to remain B.
Under this condition, `preserves_iff` and `family_iff` classify preservation
by vanishing of the SUM of the bare cross term and evaluated Yukawa cross
term on the original radical. Neither term is required to vanish separately.
`same_evaluation` proves equality of generated masses for equal evaluations.
Thus couplings invisible at this vacuum do not change this protection test.

This is the general bridge, not an automatic search for the allowed family.
It does not assert that all residual-invariant masses are UV-generated,
or that the preserved radical exhausts the new light space. A linear
parameter-space kernel or finite-basis decision procedure is a future
consumer, not an input silently added to this endpoint.

## Verification

- Focused audit build: passed, 3640 jobs and six strict transitive axiom
  checks, permitting only propext, Classical.choice and Quot.sound.
- Full `lake build`: passed, 5881 jobs, also rechecking the prior merged
  milestones. Existing dependency warnings replayed; no new source warnings.
- Layout: 830 modules, passed. Documentation: 312 files, 1905 links,
  33 fragments, zero errors. `git diff --check`: passed.
- Prior merged Yukawa script regression: all eight tests passed. These
  scripts are not premises of the general bridge.
- Lean LSP was unavailable; used source reads and focused CLI builds.
  Initial elaboration fixes made the representation product explicit and
  used proof irrelevance for equal generated masses; no limits were raised.

Commit and integrate this bounded endpoint; retain both topic branches.

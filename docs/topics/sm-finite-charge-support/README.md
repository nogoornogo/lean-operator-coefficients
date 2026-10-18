# Finite lepton-charge support and maintained assignment checks

- ID: `sm-finite-charge-support`
- Status: completed
- Result type: proved
- Working branch (historical): `proof/sm-finite-charge-support`; safely deleted after master merge
- Integration target: `master`; merged as `checkpoint 01`, no push performed
- Authorization: at stage 01 the user requested a new branch, a frozen
  initial plan, and autonomous progress along the two-stage review response.
  On the same date the user explicitly requested integration into master.

## Endpoint And Scope

First maintain the existing 572 kernel-certified assignments through a named,
opt-in verification target and prove charge/fermion-degree lower bounds.
Then determine the finite attainable lepton-charge sets for B1/B2 and, where
the frozen routes suffice, prove a support criterion for arbitrary nonzero
cyclic modulus and q/l charges. The [initial plan](plan.md) fixes interfaces,
routes, resource limits, acceptance and stop conditions before implementation.

Keep the fixed ten signed three-generation species, independent Lorentz
actions, derivative-free exterior algebra, residual-neutral Higgs/dual and
scalar cyclic q/l action. No minimum-dimension optimization, UV realization,
rates, new dependencies, changed proof limits, supplied multiplicity law or
new computational environment is included. The subsequent review-response
request authorizes the bounded root README updates in the
[minimum-lepton plan](minimum-lepton-plan.md).

## Deliverables And Acceptance

Stage 1 owns a reproducible verification command, charge-degree lemmas and
updated interpretation of the existing table. Stage 2 owns finite capacity/
parity bounds, positive witnesses, negative exclusions and the general
original-space equivalence, or an explicit bounded feasibility result naming
unresolved values. A search miss is never a prohibition proof.

Proof changes require focused builds, persistent strict transitive audits,
one serialized full build, layout, local-link and diff checks. Retain actual
resource measurements and failed attempts. A coherent verified checkpoint is
committed; it does not authorize master integration.

## Work And Open Obligations

The [master integration](master-integration.md) is complete at `checkpoint 01`,
integrating topic checkpoint `checkpoint 02`. The merged tree matches that checkpoint.
Fresh strict transitive audits pass 1199 + 52 + 13 checks; the full build
passes 7345 jobs with zero warnings/errors. Layout, links and diff checks pass.
The local topic branch was safely deleted; CSV snapshots remain unchanged.
No push was performed. No scoped obligation remains.

The remaining degree-bound review issue is [complete](minimum-lepton-results.md),
following the [frozen plan](minimum-lepton-plan.md). `minLepton : Option Nat`
has a proved prohibition/attainment meaning; its lower bounds cover negative
B3 and all selected contents/Higgs degrees. All 796 allowed row/target
applications, minimum distributions and the 278 B1 / 284 B2 high-degree
groups are now in the ordinary build. README updates state the exact fixed
scalar-cyclic scope and link Degree interpretation. The current full build
passes 7345 jobs, zero warnings/errors, with 52 new strict checks, the base
13 and existing finite-support 1199. No scoped obligation remains.

Earlier completed stages remain below with their own verification baselines.

The final review found no new proof issue. Its README suggestion is addressed
by marking the fixed q/l table row as an exact equivalence and distinguishing
it from the other necessary-condition filters. At the user's direction,
retained CSV snapshots and their optional comparison tools are unchanged;
they are not Lean proof inputs. This documentation-only follow-up passes
`node tools/docs/check-links.mjs` and `git diff --check`. No Lean build was
rerun, and that checkpoint's verified proof baseline is unchanged. Master
integration had not yet been authorized at that checkpoint.

The subsequent request to remove CSV from the proof path is
[complete](lean-enumeration-results.md), following the
[frozen extension plan](lean-enumeration-plan.md). Candidates and verdicts
are now defined entirely in Lean, with exact membership, unique coverage,
total 572 and class counts 326/144/102/0 proved in the kernel. Counted classes
are connected to the original coefficient spaces. CSV is optional Lean output;
the intermediate external row table/renderer was removed. The checkpoint full
build passes 7342 jobs, zero warnings/errors, with 1199 strict transitive
checks. No implementation obligation remains in this scope.

Earlier completed stages and their checkpoint verification remain below.

Stage 1 is [complete](stage-one-results.md), checkpoint `checkpoint 03`: the
maintained target checks the 572 assignments and all 796 allowed-entry degree
bounds. The general degree interface and persistent audit pass the full build.
Stage 2 is [complete](../sm-attainable-lepton-charges/results.md), checkpoint
`checkpoint 04`: its exact sets are all odd |L|≤17 at B1 and all even |L|≤18 at
B2, with 37 actual joint witnesses. The general theorem covers arbitrary
nonzero k,q,l; all 572 row classifications are committed importable
corollaries checked by the normal library build. No candidate remains unknown.

The [child merge and final parent verification](integration.md) pass at
`checkpoint 05`: full build 7342 jobs, zero warnings/errors, and 1154 freshly rerun
strict transitive checks. The historical independent certificates and all
796 degree bounds also agree. Both stages are complete; there is no remaining
implementation obligation in the frozen scope. Master integration had not yet
been authorized at that checkpoint. Minimum dimension and UV/decay physics
remain outside scope.

## References

- [Original assignment contract](../sm-support-evaluator-feasibility/assignment-plan.md)
- [Existing assignment results](../sm-support-evaluator-feasibility/assignment-results.md)
- [Structural support interface](../../proof/current/applications/Physics/SM_STRUCTURAL_QL_SUPPORT.md)
- [Reproducible tools](../../../tools/structural-support/README.md)

# S3 Yukawa-compatible flavor-map qque sample

- ID: s3-yukawa-compatible-qque
- Status: completed
- Result type: proved (selected-sector coefficient and flavor-map gates)
- Working branch: proof/s3-yukawa-compatible-qque
- Integration target: master; user authorized merge at stage 01
- Authorization: user requested a new branch, plan and autonomous execution to the stop condition.

## Frozen endpoint

Fix S3 acting on three-generation physical right-handed conventions:
Q, uR and dR carry the permutation action; L and eR carry three copies
of the sign character; Higgs is residual-neutral. Gauge and flavor actions
are independent. Prove SM commutation, genuinely noncommuting quark actions,
bijective invariant flavor maps Q→uR, Q→dR and L→eR, and an actual
statistics-constrained nonzero qque coefficient using the existing exterior
coefficient equivalence. The maps are flavor-map gates, not a complete
physical Yukawa/mass certificate. Conjugate field conventions and a bridge to
the full ten-species input are not needed for this selected physical qque endpoint.

## Plan and stop conditions

1. Reuse [existing S3 actions](../../../Physics/StandardModel/Operators/S3QqueTensorSamples.lean)
   and [the physical qque equivalence](../../../Physics/StandardModel/Operators/QquePhysicalExteriorCompleteness.lean).
2. Construct the coefficient det(ones, x*y, z) times sum(r), with coordinatewise
   x*y. Prove its linear tensor lift, Q-pair symmetry, S3 invariance and
   nonzero basis evaluation. Allowed fallback: finite signed orbit sum on
   the same tensor source. No new representation-theory foundations.
3. Certify the fixed dictionary's flavor-map and SM commutation gates.
4. Persist strict transitive axiom audits and an exact finite supplementary
   check. Run focused builds, the audit, full lake build, layout/link/diff
   checks; review assumptions and commit the verified endpoint.

Stop successfully after these finite certificates and documentation are
complete. Stop with a documented blocker if both named coefficient routes
fail within existing interfaces or a new theorem-level prerequisite is needed.
Do not extend to other sectors, a residual-group classification, full B1
protection, realistic masses/mixing, anomalies, UV/SU6 realization,
derivatives, matching or rates. The original plan excluded merge/push; the user
subsequently authorized master integration and a reader-facing model-study page.
No push is authorized.

## Result and stopping decision

The explicit coefficient route succeeded. Noncommuting quark actions, SM
commutation, bijective flavor maps and actual qque allowance are proved for
the same dictionary. See [results](results.md) and [verification](verification.md).
All 25 strict transitive audit checks, focused/full builds and the exact finite
supplement pass. The bounded endpoint is complete; no open proof obligation
remains inside it. Master integration completed in merge checkpoint 01; merged-state
checks passed and the local topic branch was deleted.
See the [reader-facing study](../../model-studies/s3-flavor-qque/README.md)
and [integration record](master-integration.md).
The prior samples and their failed flavor-map gates remain unchanged; see
[their results](../sm-support-and-lfv-decomposition/sm-preserving-sample-results.md).
Unrelated docs.zip is untouched. No physical Yukawa or UV realization is claimed.

# Li Duql And Duue Local Basis Verification

- ID: `li-duql-duue-basis`
- Status: completed
- Result type: proved normalized local-contraction certificates and product inverse
- Working branch: `proof/li-duql-duue-basis`
- Integration target: `master`
- Integration evidence: Git ancestry into the recorded target; report merge outcome

## Endpoint And Scope

Certify the normalized derivative-free dimension-six DUQL and DUUE local
contractions printed by Li et al. against independently defined exterior
coefficient sectors. Together with the completed QQUE and QQQL certificates,
connect their candidate maps to the existing four-family Delta L=+1
completeness equivalence. This is a local-contraction certificate, not a
verification of the whole paper or ABC4EFT runtime arrays.

Inputs are complex flavor modules and specified representations of an arbitrary
abstract residual group H. Retain all intertwining constraints. Finite flavor
bases are additional explicit inputs for coordinates and counting; unrestricted
dimension formulas apply only to trivial residual action. Actual physical
carriers require supplied equivariant identifications, including any dagger
interpretation. Do not silently assume Hermitian self-duality.

The detailed phases and stop gates are in [the plan](plan.md).

## Deliverables And Acceptance

1. Pin and inspect the paper expressions; record equation/page, field order,
   chirality, color/weak/spinor conventions and citation roles.
2. Define literal candidate contractions and prove all reorder signs and raw
   exterior normalization, separately for DUQL and DUUE.
3. Prove agreement with existing completeness inverses, including both
   extraction/reconstruction identities. Repeated U inputs must use the actual
   exchange equations, not an assumed symmetric square.
4. Supply finite nonredundant coordinates, independent spanning families and
   counts for trivial H, while preserving explicit constraints for arbitrary H.
5. Compose all four local certificates with the existing full signed-species
   decomposition; certify a single product reconstruction without strengthening
   the existing field-content hypotheses.
6. Persist strict transitive axiom/import audits; run focused and full builds,
   exact normalization controls, layout, links and diff checks.

Matching dimensions alone is insufficient. At completion write a stable proof
dossier and update the verified assumptions ledger. No master merge is authorized
by creation of this topic.

## Work And Open Obligations

- Visually recovered D.37 and D.6; see the [source dictionary](source-recovery.md).
- Separate DUQL and DUUE convention/certificate modules, strict audits and
  proof dossiers are implemented, as requested. Actual candidate descent,
  two-sided residual and finite coordinate inverses, independent spanning
  families and general counts are proved. Both families have dimension 81
  for three flavors with trivial action; one flavor gives 1.
- The shared four-family candidate agrees with the independently derived full
  sector reconstruction and has both inverses. QQUE's local D.38 expression
  is also checked in the direct-carrier consumer convention, not silently
  identified with the earlier dual-coordinate interface.
- No acceptance obligation remains in the normalized local scope. Physical
  dagger identifications, runtime package arrays and amplitude correspondence
  remain explicit boundaries. No dependency pin or root README was changed.
- Merged into `master` on explicit user direction; Git ancestry records the integration.

## Result And Verification

Planning commit: local links passed (395 files, 2695 links) and diff checks
passed; no Lean build was rerun for that documentation-only checkpoint.

The final scoped results are recorded separately in
[DUQL](../../proof/current/applications/Physics/LI_DUQL_BASIS.md) and
[DUUE](../../proof/current/applications/Physics/LI_DUUE_BASIS.md). The actual conjugate D.6 scalar
factors are proved; arbitrary physical flavor conjugation is a supplied model
input. General H coordinates retain the entire action equations, and only
trivial tensor action yields unrestricted flavor counts.

Verification commands: `lake build`, the three `AuditLiDuqlBasis`,
`AuditLiDuueBasis`, `AuditLiFourFamily` targets, `node tools/layout/check-layout.mjs`,
`node tools/docs/check-links.mjs`, `git diff --check`. Exact finite cardinality
controls are persisted in both family audits and checked by `decide +kernel`.

Final results: `lake build` passed (6400 jobs), with no warnings or errors.
Separate strict audits passed 15 DUQL, 18 DUUE and 8 four-family transitive
checks (41 total); only the three standard Lean axioms are permitted. Layout
passed (1073 modules), local links passed (398 files, 2713 links, zero errors),
and `git diff --check` passed. No heartbeat limit was increased. The earlier
QQUE and QQQL audits also replayed successfully in the full build.

## References

- [Li et al., pinned arXiv:2201.04639v2](https://arxiv.org/pdf/2201.04639v2)
- [QQUE certificate](../../proof/current/applications/Physics/LI_QQUE_BASIS.md)
- [QQQL certificate](../../proof/current/applications/Physics/LI_QQQL_BASIS.md)
- [DUQL exterior completeness](../../../Physics/StandardModel/Operators/DuqlExteriorCompleteness.lean)
- [DUUE residual completeness](../../../Physics/StandardModel/Operators/DuueResidualCompleteness.lean)
- [DUUE exchange equations](../../../Physics/StandardModel/Operators/DuueExchange.lean)
- [Full coefficient completeness](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
- [Four-family topic](../delta-l-one-completeness/README.md)

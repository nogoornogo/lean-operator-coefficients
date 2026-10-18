# Necessary And Sufficient Residual Selection Criteria

- ID: `residual-selection-criteria`
- Status: completed
- Result type: proved algebraic necessary-and-sufficient selection criteria
- Working branch: `proof/residual-selection-criteria`
- Integration target: `master`
- Integration evidence: master integration authorized at stage 01; Git ancestry records the merge

## Endpoint And Scope

Expose a common necessary-and-sufficient algebraic meaning of forbidden and
allowed coefficient sectors, using the existing four completeness endpoints:
dimension-six Delta L one, specified Delta B two, Weinberg LLHH, and chiral
CLFV dipoles. Their distinct input spaces and exchange constraints stay intact.

Then classify, for one-generation SM fermion multiplicities with specified
finite cyclic residual charges and one residual-neutral Higgs, when all four
dimension-six baryon-violating families are forbidden while LLHH admits a
nonzero coefficient. Give proved congruence conditions and positive/negative
controls, not an exhaustive search over symmetry models.

“Allowed” means that an invariant nonzero coefficient exists, not that a UV
model generates it. Quantum anomaly consistency and physical rates are not
outputs. Arbitrary residual groups remain possible in the abstract criterion;
the concrete charge classification has the explicitly narrower inputs above.

## Deliverables And Acceptance

- Common zero/nonzero predicates with equivalence transport and simultaneous
  finite-family prohibition rules.
- Adapters for the four existing completeness endpoints, preserving their
  actual hypotheses, constrained Hom spaces and field dictionaries.
- Exact cyclic-charge criterion for the independently defined full signed
  four-fermion sector, connected to its four-family decomposition.
- A simultaneous all-four-forbidden / LLHH-allowed iff theorem, including
  constructive nonzero witnesses and small finite controls.
- Persistent strict axiom audits, focused/full builds, layout/link checks,
  completed proof dossier and verified assumptions-ledger entries.

See [the plan](plan.md). Completion is all these acceptance gates, not just a
generic linear-equivalence lemma. No automatic master merge is authorized.

## Work And Open Obligations

All five milestones are complete. The physical charge dictionary uses
q, u_R, d_R, l, e_R and opposite charges for their conjugate species.
The concrete theorem uses `[NeZero N]` (equivalent to positive natural order).
No general-flavor sufficiency assertion is inferred from scalar neutrality.
There is no remaining implementation obligation within the frozen endpoint.

## Result And Verification

The [proof dossier](../../proof/current/applications/Physics/RESIDUAL_SELECTION_CRITERIA.md) records
the exact inputs, charge tests, constructive converses and boundaries.
The four abstract adapters retain the existing constrained residual spaces.
The full signed-sector cyclic criterion is derived through its four-family
decomposition. Z2 quark parity passes; trivial charges and order one fail.

Verification (stage 01):

- Focused mathematical and physical audit builds: 11 + 25 strict transitive
  checks passed, permitting only the three standard Lean axioms.
- `lake build`: successful, 6,426 jobs; no new warnings reported.
- `node tools/layout/check-layout.mjs`: 1,099 modules, all checks passed.
- Documentation links, docs/layout regression tests and `git diff --check`
  passed: 421 Markdown files, 2,838 links, zero errors; 14/14 tests.
  Tests using temporary Git repositories were rerun outside the sandbox after
  the sandboxed invocation failed; no test or audit allowance was changed.

Dependency pins, audit allowances and root README are unchanged. The user
authorized closing and merging this topic at stage 01. The verified proof
checkpoint is `checkpoint 01`; Git ancestry is authoritative for integration.

## References

- [Workflow](../../architecture/WORKFLOW.md)
- [Common completeness interface](../operator-completeness-interface/README.md)
- [Dimension-six four-family completeness](../delta-l-one-completeness/README.md)
- [Six-quark physical interface](../delta-b-two-model-interface/README.md)
- [Weinberg completeness](../delta-l-two-weinberg/README.md)
- [Dipole completeness](../clfv-dipole-completeness/README.md)
- [Full signed-sector iff](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
- [Scalar Weinberg criterion](../../../Physics/StandardModel/Operators/WeinbergScalarFlavor.lean)

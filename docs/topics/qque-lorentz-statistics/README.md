# Limited QQue Lorentz And Statistics Audit

- ID: qque-lorentz-statistics
- Status: completed
- Checkpoint detail: completed (limited audit only).
- Working branch: `audit/qque-lorentz-statistics`.
- Integration target: `master`.
- Result type: bounded feasibility audit, not the complete operator theorem.

## Questions And Stop Gate

1. Can the current compact source and explicit SM decomposition inputs
   supply the Q-exchange symmetry required by the qque contraction?
2. Does the one-generation contraction survive fermionic antisymmetry?
3. Do pinned exterior-algebra APIs suffice without new foundations?

Inspect the common-quotient construction, check the signs against the standard
qque contraction, and run small reusable Lean probes for symmetric coefficients
and exterior nonvanishing. Record what the probes prove and what remains a
mathematical/source-inspection argument. Do not implement the complete
Lorentz/SM/H/radical endpoint, add a generation bound or nonzero-coupling
assumption, upgrade dependencies, or reopen other models.

## References

- [Previous tensor endpoint](../explicit-sm-residual-tensor/README.md).
- [Exact adapter hypotheses](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md).
- [Current assumptions](../../proof/ASSUMPTIONS.md).
- Alonso et al., [arXiv:1405.0486v2](https://arxiv.org/html/1405.0486v2),
  qque definition and flavor permutation symmetry.

## Result

[Results and evidence boundaries](results.md): all three questions have a
positive feasibility outcome. Reusing one Q split gives a symmetric nonzero
H coefficient with no generation bound. The one-generation selected exterior
expression is nonzero; an independent integer check covers the full finite
component expansion. The pinned exterior-power universal property is exercised
in Lean. This does not complete the actual Lorentz/SM/H operator endpoint.

No further work is authorized by this audit card. The results file specifies
the three remaining assembly tasks for the later implementation milestone.
Existing theorem scopes, dependencies and E6 boundaries are unchanged.

## Verification

stage 01:

- `lake build Physics.StandardModel.Operators.Audit.AuditQqueStatisticsFeasibility`:
  passed (3120 jobs); 10 strict transitive axiom checks, no new warnings.
- `python3 tools/qque/audit_one_generation.py`: 3 tests passed; exact integers,
  no external packages or floating-point sampling. This is not a Lean oracle.
- `lake build`: passed (5653 jobs); inherited warnings remain.
- `node tools/layout/check-layout.mjs`: passed (616 modules).
- `node tools/docs/check-links.mjs`: passed.
- `git diff --check`: passed.

Lean LSP MCP is unavailable; used pinned source reads and focused builds.
No placeholders, new axioms, relaxed audit allowlists or pin changes.
Integration target is `master`; Git ancestry records the actual merge.

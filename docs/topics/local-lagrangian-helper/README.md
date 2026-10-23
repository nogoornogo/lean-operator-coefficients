# Local Polynomial Lagrangian Helper

- ID: `local-lagrangian-helper`
- Status: completed
- Result type: proved optional local polynomial Euler/IBP generator with existing-input adapters
- Working branch: `proof/local-lagrangian-helper`
- Integration target: `master`; explicitly authorized and integrated
- Integration evidence: preserved-history merge and [merged-state verification](master-integration.md)
- Authorization: user-directed topic and implementation of an optional EOM-input generator

## Endpoint

Generate Euler expressions and explicit IBP currents from finite local
polynomial expressions, including mixed Bose/Fermi fields and arbitrary finite
ordinary derivative words. Reuse the existing jet algebras and coefficient
operations. Keep every published input route and dependency pin unchanged.
The helper supplements direct EOM input; it is not a new required model format.

The [frozen contract](plan.md) states the expression semantics, graded signs,
equation closure, input connection and usability controls. Analytic actions,
nonpolynomial field functions and automatic symmetry discovery are excluded.

## Result And Stop

The [contract](plan.md) is proved. The helper generates finite Euler families
and explicit currents for the full admitted syntax, including mixed signs
and arbitrary finite derivative words. Bosonic output uses the existing
commutative equations factory; mixed output uses the proved two-sided
differential closure and the same common input operations. An actual Lorentz
scalar consumer packages its symmetry proof and takes only a coupling.

See [results](results.md), [input guide](input-guide.md),
[verification](verification.md) and [source roles](references.md). Strict
audits and the full build pass. No contracted proof remains. The verified
topic is integrated into master after the user's separate merge instruction.
Generic symmetry discovery, opaque-contraction conversion, nonpolynomial
functions and analytic/quantum extensions remain outside this helper.

The local working branch is retired after reachability and worktree checks.

## Related Results

- [Existing input choices](../derivative-interface-adapters/input-guide.md).
- [Earlier model-specific first variations](../formal-first-variation/results.md).

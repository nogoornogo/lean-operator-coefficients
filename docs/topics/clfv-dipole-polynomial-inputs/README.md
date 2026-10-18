# CLFV Dipole Polynomial Inputs

- ID: `clfv-dipole-polynomial-inputs`
- Status: completed
- Checkpoint detail: completed (bounded polynomial endpoint); merged
- Integration result: [merge chain and verification](../clfv-dipole-completeness/integration.md).
- Result type: proved for the stated structural class
- Working branch: `proof/clfv-dipole-polynomial-inputs`
- Integration target: `proof/clfv-dipole-input-structure`
- Parent exception: bounded child of the unmerged input-structure branch.
- Integration policy: no merges or remote push; retain verified milestones.
- Overall research goal: revised in the [model-interface topic](../clfv-dipole-model-interface/README.md).
  Matching is a model-author responsibility; no physical decay criterion is claimed.

## Frozen Endpoint

For finite fixed residual mediator paths, take arbitrary multivariate complex
polynomial weights in independent input coordinates. Prove a necessary and
sufficient structural criterion for existence of a nonzero selected dipole:
at least one monomial has nonzero total selected coefficient in B or W.
This total groups all paths contributing to that monomial, including exact
cancellation. Do not assume path isolation or coefficient-space surjectivity.

The free-coordinate domain may be restricted to a product of infinite sets
(one infinite subset of complex numbers per coordinate). Derive existence
on such a product from mathlib's polynomial identity theorem. No open/dense,
genericity, probabilistic or numerical claims are part of this endpoint.

As a structural specialization, distinct monomial weights make existence
equivalent to a nonzero selected path. Prove this from coefficient extraction,
not an assumed controllability premise. Give a two-path control with weights
z and z squared: neither path can be isolated, but a nonzero generated
coefficient exists. Same-monomial cancellations remain in the general theorem.

## Interfaces, Scope And Stop

- Math: scalar selected polynomial, evaluation identity, coefficient formula,
  existence on infinite-coordinate products, distinct-monomial criterion.
- Physics: apply the scalar result to both selected residual channels and
  transfer to generation maps with explicitly supplied polynomial factorization.
- Controls: no isolation for z/z squared, nonzero realization, grouped
  cancellation for equal weights and opposing paths.
- Reuse mathlib's multivariate polynomial identity theorem; no new foundations.
- Fixed paths and polynomial dependence in the chosen free coordinates are
  explicit restrictions. No claim that all UV models have this structure.
  Complex-conjugate/rational/logarithmic weights and correlated input domains
  are not automatically polynomial in these coordinates.
- Do not derive matching/RGE, mass bases, loop constants, or photon amplitudes.

Stop after the interfaces and controls are proved, a persistent strict axiom
audit, focused/full builds, layout/link checks and diff review pass, and the
milestone is committed. A new physical assumption or a failure of the frozen
claim requires a recorded decision, not silent strengthening.

## Result And Verification

The general and B/W criteria, distinct-monomial specialization, external
generation-map transport and non-isolating/cancelling controls are proved.
See [results](results.md) for the hypotheses, theorem map and remaining
research obligations. The overall objective remains in progress.

The unmerged [coupling-model child](../clfv-dipole-coupling-model/README.md)
now derives finite paths and weights from finite coupling spaces and a fixed
equivariant mediator kernel, rather than assuming a path-factorization equality.

- Planning commit: `checkpoint 01`.
- Verified proof/result commit: `checkpoint 02`.
- Focused build: passed, 3554 jobs; 16 strict transitive axiom checks.
- Full build: passed, 5915 jobs; no warnings in the new source files.
- Layout: passed, 862 modules. Link/diff results are recorded in results.
- Lean LSP MCP unavailable; source inspection and CLI diagnostics used.
- No dependency/pin changes, audit exceptions, merges or remote push.
- The proof-commit reference update is documentation-only; no Lean build
  rerun. The verified proof baseline remains `checkpoint 02`.

## Sources

- [Parent input structure](../clfv-dipole-input-structure/results.md)
- [Finite synthesis](../../../Math/LinearAlgebra/WeightedSelectedPaths.lean)
- [Mediator paths](../../../Physics/StandardModel/Operators/DipoleMediatorPaths.lean)
- [Results and theorem map](results.md)

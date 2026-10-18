# Factored Dipole Input Criteria

## Scope And Hypotheses

This is an algebraic extension of the complete dipole coefficient target,
not a matching calculation. Fix residual representations A, B and a mediator
M, with B finite-dimensional over complex numbers. Fix a finite path index I,
equivariant maps u_i : A -> M and v_Bi, v_Wi : M -> B. The residual pair
of path i is (v_Bi composed with u_i, v_Wi composed with u_i).

An arbitrary domain X supplies complex weights w_i(x). Neither X nor the
weight map must be a vector space or linear. The path maps themselves are
fixed in this endpoint; arbitrary input-dependent maps are not silently
replaced by independently adjustable constant paths. Scalar weights absorb
only scalar dependence. A concrete model must justify such a factorization.

For the supplied incoming flavor vector mu and outgoing covector electron,
define the selected path pair

```text
q_i = (electron(v_Bi(u_i(mu))), electron(v_Wi(u_i(mu))))
selected generated coefficient at x = sum_i w_i(x) * q_i
```

The full coefficient is reconstructed using the inverse of the independently
proved SM coefficient equivalence. For an actual supplied map F, the theorem
requires an explicit equality of its residual pair with the weighted sum.
It does not assume that arbitrary allowed coefficients are physically generated.

## Exact And Sufficient Conditions

The [general path lemmas](../../../Math/LinearAlgebra/WeightedSelectedPaths.lean)
are independent of dipoles. The [mediator specialization](../../../Physics/StandardModel/Operators/DipoleMediatorPaths.lean)
proves the following.

1. `selected` and `nonzero_iff`: for every fixed input, the sum above is the
   exact selector; it is nonzero if and only if that finite sum is nonzero.
   Neither absence of cancellation nor controllability is assumed here.
2. `nonzero_of_single_selected_path`: a nonzero weight on a nonzero selected
   path suffices if every other selected contribution vanishes. The other
   paths need not vanish as full maps or full coefficients.
3. `nonzero_of_mediator_witness`: if u_i(mu) = t * v with t nonzero, the
   outgoing B map detects v with nonzero electron projection, the input
   weight is nonzero, and other selected contributions vanish, then the
   generated selected coefficient is nonzero. This gives a concrete
   incoming-vector/outgoing-detection sufficient interface.
4. `exists_nonzero_iff_path`: suppose each path can be isolated by an actual
   input with its weight 1 and all others 0 (`WeightedSelectedPaths.Isolates`).
   Then a nonzero selected generated coefficient exists if and only if some
   q_i is nonzero, equivalently either its B or W composite connects the two
   supplied flavor identifications.
5. `selected_of_factorization` and `realized_iff_path_of_factorization` apply
   these calculations to an externally supplied map F, with its residual
   factorization equality retained as an explicit theorem hypothesis.

Isolation is a sufficient controllability condition for the pathwise
equivalence, not a necessary condition for generating a nonzero coefficient.
It does not require surjectivity onto the complete coefficient space. It
also does not follow just from a common irreducible component: existence
of intertwiners, nonzero selected compositions and reachable weights are
different obligations. Without isolation, the fixed-input sum remains exact,
but nonzero paths alone do not guarantee a nonzero realizable sum.

## Nonlinear And Cancellation Controls

The [two-path sample](../../../Physics/StandardModel/Operators/DipoleMediatorControls.lean)
has trivial residual action, identity incoming maps, opposing off-diagonal
B bridges, zero W bridges and w_i(x) = x_i squared. Coordinate-square
weights isolate every path without any linearity requirement. Lean proves:

```text
each selected B path is nonzero
selected pair = (x_0 squared - x_1 squared, 0)
selected pair nonzero iff x_0 squared != x_1 squared
on the restricted family x_0 = x_1 = z, all selected pairs vanish
on the unrestricted input domain, a nonzero selected pair exists
```

Thus even nonlinear, individually nonzero paths can cancel at every input
of a restricted domain. This is a control of the explicit hypotheses, not
a counterexample to the frozen theorem and not a UV-model restriction.

## Verification And Boundaries

- Focused build: `lake build Physics.StandardModel.Operators.Audit.AuditDipoleMediatorPaths`,
  passed, 3549 jobs, no new-source warnings.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipoleMediatorPaths.lean):
  23 strict transitive checks; only propext, Classical.choice and Quot.sound;
  model-layer imports rejected.
- Full `lake build`: passed, 5909 jobs. Existing warnings replayed; no warning
  in the new source files. The existing qque and dipole audits remain registered.
- `node tools/layout/check-layout.mjs`: passed, 858 modules.
- `node tools/docs/check-links.mjs`: passed, 319 Markdown files, 1952 local
  inline links and 33 heading fragments; zero errors.
- `git diff --check` and staged diff check: passed.
- No dependency/pin changes, custom axioms, `sorry` or audit exceptions.
  Lean LSP MCP was unavailable; source reads and CLI builds were used.
- No matching/RGE, mass-basis derivation, loop normalization, photon
  combination or experimental claim. Both gauge components are monitored
  separately. A nonzero pair is not a theorem about a nonzero decay amplitude.
- No merge or remote push. The child and its parent remain unmerged.

The next physical obligation is to justify the factorization and reachable
weight constraints for a specified model family. A sample calculation alone
does not settle that obligation, and no such model premise is audited as
though it had been derived here.

The unmerged [polynomial-input extension](../clfv-dipole-polynomial-inputs/results.md)
now replaces path isolation by a structural polynomial identity criterion
on independent infinite-coordinate products. Same-monomial contributions
are grouped, so identically cancelling families remain excluded. The overall
research objective is still in progress, beyond both bounded endpoints.

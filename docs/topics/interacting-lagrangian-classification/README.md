# Interacting Lagrangian Coefficients At All Orders

- ID: `interacting-lagrangian-classification`
- Status: completed
- Result type: proved all-order coefficient presentation, closed nonlinear specialization and shortcut counterexamples
- Working branch: `proof/interacting-lagrangian-classification`
- Integration target: `master`; integrated after explicit user direction
- Authorization: user-directed new branch, general interacting formalization and literature/artificial validation
- Branch origin: `master`; the separate unmerged documentation topic is not included

## Endpoint And Assumptions

Classify invariant complex linear coefficients of the actual unbounded mixed
jet algebra modulo the full Euler differential closure and linear IBP.
Admit every existing finite local polynomial expression, with arbitrary
finite derivative words and complex couplings. Keep the specified group
action and its relation stability explicit. Do not assume independent
on-shell field-number grades.

The output is an inverse coordinate equivalence with the solution space of
explicit all-order linear equations, with reconstruction and necessary/
sufficient prohibition and prescribed-value criteria. Construct the actual
exterior/polynomial monomial basis and prove that the generated rows span
every full relation. No invariant basis, truncated relation completeness or
finite rank may be assumed. A terminating finite universal decision algorithm
is a stronger endpoint; investigate its boundary and never claim it from an
infinite presentation alone. Analytic/nonpolynomial/quantum dynamics and
dependency changes remain outside this algebraic topic.

## Plan And Acceptance

1. Build the all-order monomial basis and an infinite-coordinate input
   equivalence with finite-support evaluation on each actual polynomial.
2. Generate equation rows from both monomial multipliers, every derivative
   word and every computed Euler component; add divergence and full-group
   rows. Prove span, inverse maps and evaluation without a degree cutoff.
3. Connect finite selections through full relation preimages. Keep global
   extension and on-shell grading distinct from the all-order presentation.
4. Specialize to a mixed Yukawa interaction and registered scalar/Higgs
   inputs; test signs, coupling-zero recovery, packaged symmetry and an
   exact interacting target criterion.
5. Compare the [primary sources](references.md) and artificial positive and
   negative controls. Record any mismatch and continue to the next source.
6. Persist strict axiom/import audits; update guides, assumptions and source
   roles; run focused builds, one serialized full build and repository gates;
   review and commit on this branch.

Use two Lean threads, default elaboration limits, a 16 GiB address-space cap
and a 540-second wall-clock guard per build command. These are execution
guards, not theorem cutoffs. Report a stronger unsupported endpoint as open;
a counterexample is a scoped result, not a general impossibility assertion.

## Work And Verification

The complete generated-row equivalence, exact selected preimages and both
bosonic/mixed factories are proved. The polynomial-potential family has
closed independent coordinates at every order, including parameter branches.
Mixed cubic and three primary-source comparisons pass; cancelling-equation
and finite-cutoff shortcuts have precise counterexamples.

[Verification](verification.md) records 351 strict transitive checks and the
8,016-job full build. Published APIs, pins and elaboration limits are unchanged.
See the [result dossier](../../proof/current/core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md)
and [literature/artificial results](literature-validation.md).

The recorded mathematical endpoint is complete. Solving every infinite row
system into independent normal forms or counts for arbitrary densities is
not proved; an exact presentation is not a terminating universal classifier.
No undecidability claim is made. The topic and its model-connection and
Euler-naturality successors are integrated into master.
[Merged-state verification](integration-verification.md) records the checks
and retained scope.

## Related Records

- [Model connection successor](../lagrangian-model-connections/README.md): additive packages, checked symmetry certificates and a complete algebraic Yukawa density.
- [Existing helper](../local-lagrangian-helper/README.md).
- [Nonlinear equations](../nonlinear-eom-gauge-jets/results.md).
- [Generated Higgs input](../derivative-literature-foundations/input-guide.md).
- [Sources and validation plan](references.md).

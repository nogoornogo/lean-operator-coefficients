# Finite All-Degree SM/Higgs Support Reduction

For the fixed signed three-generation SM input and one residual-neutral
Higgs doublet/dual, all-degree coefficient support reduces to finitely many
full-group invariant Hom tests. The group H and independent flavor
representations on each three-dimensional species carrier remain parameters.
No residual-action classification or source semisimplicity is assumed.

The [result dictionary](../../../../topics/sm-higgs-support-cutoff/results.md)
states the finite predicate, the source construction and the exact limits.
The [topic](../../../../topics/sm-higgs-support-cutoff/README.md) owns branch,
authorization and verification records.

Core consumers:

- `Physics.SMFiniteHiggsSupport.mem_original_iff` and `originalEquiv`: actual
  fermion/scalar-count support on the full statistical carrier.
- `original_charge_finite_iff` and `original_forbidden_iff`: support iff an
  exact bounded weak-degree test survives with the correct hypercharge.
- `original_table_iff`: a degree-independent table indexed by representative
  Higgs counts s,t with s+t bounded by the fermion doublet count.
- `original_pair_monotone`, `original_pair_stable`, `original_pairs_stable`:
  upward support and exact stabilization at a proved uniform threshold.
- `Physics.SMFiniteSupportTable.all_degrees_iff` and `global_table_iff`: actual
  finite-table reduction across the 180-dimensional fermion universe.

The finite predicates retain `Allowed(T)` rather than substituting charge
neutrality or a dimension diagnostic for the zero/nonzero Hom proof.
The general statement remains parameterized in arbitrary residual flavor
actions. For the existing scalar cyclic q/l actions, the separate
[structural classification](SM_STRUCTURAL_QL_SUPPORT.md) now discharges the
retained tests without numerical rank/multiplicity certificates or a Weyl
premise. `SMJointHiggsSupport.original_ql_iff` states actual all-content,
all-Higgs support iff residual and hypercharge neutrality and a finite
positive occupation/component/color-diagram/SU2-path condition.
`original_ql_forbidden_iff` proves the complementary prohibition criterion.

## Other retained interfaces

The [compact local-kernel result](../../../../topics/sm-compact-kernel-completion/results.md)
provides exhaustive actual gauge/Weyl tests and replaces local `Allowed(T)`
with a finite constraint-matrix rank inequality. That interface does not
compute the ranks. It is separate from the structural criterion above.

The [joint component and algebraic occurrence result](../../../../topics/sm-computable-characters/joint-branching-results.md)
constructs bounded weak/left/right multiplicity actions preserving
color/hypercharge. Under the explicit Weyl torus-reduction input,
`SMJointAlgebraicSupport.original_ql_iff` gives the alternative Laurent
coefficient nonvanishing criterion. Its source-character presentation is
proved, but Weyl integration remains its explicit premise. The new
structural theorem does not use this premise.

Previously bounded structural results cover constant Q/L, saturated
contents, mixed leptons and paired colored sources. The Q cubic through
sixth source decompositions and complementary/conjugate transports, followed
by complete positive color coupling and generation/species composition,
close their former full-content boundary. The owning topic's
[phase index](../../../../topics/sm-computable-characters/phase-index.md)
retains those results and their checkpoint verification records. They are
not additional unresolved premises of the final structural theorem.

The Physics adapters construct actual statistical-source comparisons and
retain Higgs admissibility, hypercharge, scalar q/l charge and both independent
spin actions. Permission is coefficient nonzeroness; it does not assert a
UV-generated interaction or rate. Arbitrary residual representations,
derivatives/EOM/IBP and numerical phenomenology remain outside the fixed
q/l classification. Persistent audits permit only `propext`,
`Classical.choice` and `Quot.sound`; see the
[final verification](../../../../topics/sm-computable-characters/full-support-verification.md)
for executed checks.

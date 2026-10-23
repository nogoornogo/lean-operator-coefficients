# Scalar Jet And IBP Implementation Contract

Status: scalar proof gates completed on `proof/derivative-ibp`, after the
dependency child was merged and its full compatibility gate reverified. The integration target
remains `master`; the current instruction authorizes resuming implementation
on this topic, not merging it into master. All dependency pins stay unchanged.

## Plan Change And Frozen Endpoint

The earlier survey stopped before implementation authority. The user now
authorizes implementation and necessary plan changes through a bounded stop.
Use its Route A and four gates. Implement the scalar foundation first; the
external even mixed-algebra derivations are available but do not remove the
need to prove a scalar jet/IBP semantic connection. Do not import the external
SM or analytic IBP packages to stand in for that connection.

The source is the commutative polynomial algebra over complex numbers on
ordinary scalar jets `X_(a,alpha)`, with arbitrary component labels `a` and
finitely supported natural multi-indices `alpha`. Define
`D_mu X_(a,alpha) = X_(a,alpha + e_mu)`. These are ordinary derivatives,
with no factorial normalization or momentum phase. The algebra is unbounded
in derivative order. Restriction to a fixed grade never sets higher jets to zero.

Use the pair `(number of fields, total number of derivatives)` as the grade.
Prove that each `D_mu` preserves field count and raises derivative count by
one, that total derivatives commute, and that finite component/direction sets
give finite-dimensional fixed grades. The first endpoint is algebraic scalar
jets with commuting derivatives; directions do not themselves assert a Lorentz
action, gauge-covariant commutator or spacetime interpretation.

At target grade `(n,d+1)`, the current space is the direct sum of copies of
grade `(n,d)` indexed by derivative directions. Divergence is the sum of the
actual `D_mu` maps. The IBP relations are exactly its linear range, not an
ideal of the full field algebra. Record generator membership and the exact
annihilation condition for functionals. Source quotients and their coefficient
duals remain different objects: coefficients are linear functionals on the
quotient, equivalently functionals on the source annihilating every divergence.

Construct internal actions by relabelling scalar components while fixing jet
directions, and prove covariance and stability. Connect these actual relations
to `RelationQuotient` and the existing local-coinvariant/residual-Hom descent
for commuting local/residual relabellings. No exchange of invariants with a
quotient, reductivity or semisimplicity is assumed. This is a new scalar
consumer of the general descent framework; existing derivative-free mixed
completeness statements keep their scopes and hypotheses.

The concrete acceptance consumer has one scalar component, one derivative
direction, two fields and two derivatives. Prove that its entire source is
spanned by `X_1^2` and `X_0 X_2`, that the entire divergence relation is spanned
by `X_1^2 + X_0 X_2`, and construct an explicit quotient equivalence with the
complex line. Prove a surviving class and exact quotient dimension one.
The relation matrix must follow from the actual total derivative, not be
supplied as a hypothesis. This tests nonzero IBP relations and their complete
span, rather than just proving a generic quotient theorem.

## Gates And Stop Conditions

1. Define scalar jets and total derivatives; prove generator, Leibniz and
   commutation formulas.
2. Prove joint grading, finite fixed grades, internal covariance and the
   actual divergence/range construction.
3. Prove inverse coefficient descent and local/residual-Hom correspondence,
   with explicit evaluation on quotient classes and zero/nonzero criteria.
4. Prove the concrete source/span, relation/span and quotient-line consumer.
5. Register new modules and persistent strict transitive audits; run focused
   builds, the strict audits and full `lake build`, layout, documentation
   links/index/metadata and diff checks. Reconcile bibliography/assumptions,
   review and commit coherent verified milestones on this topic branch.

Stop successfully after these gates and their verification. Stop with a
precise partial result if a gate needs an independent new foundation, changed
dependencies, extra mathematical/physical premises, an audit exception or a
resource-limit escalation. Keep Lean's default recursion/kernel limits for
new proofs; for a named costly check retain the earlier operational ceiling
of 16 GiB process RSS / 9 minutes. Do not restart a failed route by renaming it.

No mixed-statistics/source bridge, analytic integrated-action equality,
boundary/Stokes theorem, EOM/Bianchi quotient, momentum-symbol equivalence,
Lorentz/Gram completeness, Hilbert-series counting or full SMEFT theorem is
included. Reaching the scalar endpoint does not authorize automatically
starting one of these separate foundations.

## Gate Outcome

All four proof gates pass. The actual scalar construction, grading, finite
grades and symmetry covariance feed the existing quotient/Hom descent. The
complete quadratic example has source generators `X_1^2`, `X_0 X_2`, divergence
range exactly `C (X_1^2 + X_0 X_2)`, a proved quotient-line equivalence and a
surviving class. The usual formal IBP functional identity is derived from
the actual graded product derivative.

The focused audit passes 62 strict transitive checks; full `lake build`
passes 7574 jobs. No increased recursion/kernel limit, dependency change,
custom axiom or audit exception is introduced. See the
[result dossier](../../proof/current/core/Math/SCALAR_JET_IBP.md) and
[verification](verification.md). This is the successful stop of this contract;
the mixed-statistics/spacetime foundations above are not opened automatically.

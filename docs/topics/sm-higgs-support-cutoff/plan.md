# Plan And Frozen Proof Contract

## Selected endpoint

Reduce all natural Higgs counts (h,d) to a finite collection of invariant
Hom tests for the fixed three-generation signed SM matter input. The group H
and its species flavor actions remain parameters. The tests retain color,
weak, Weyl, hypercharge, residual actions and exterior statistics. Their
zero/nonzero classification is deliberately outside this endpoint.

The initial request authorized planning and branch creation. The user then
authorized implementation along this contract through its stop condition.
Any material change to the endpoint or assumptions requires a scope decision.

## Frozen input and notation

- Use the actual ten signed SM species, each with the existing
  three-dimensional flavor carrier, and their existing gauge/Weyl actions.
- Supply representations of an arbitrary group H on those flavor carriers;
  H acts through flavor, independently of the gauge/Weyl factors. Retain the
  existing signed-field convention. No irreducibility or complete
  reducibility of the flavor action is assumed.
- Use one actual SM Higgs H and its algebraic dual, with hypercharge phases
  z^3 and z^-3 and trivial residual/color/Weyl action. Additional Higgs
  copies or residual Higgs actions are not included.
- A content c records counts of each signed fermion species. W_c is its
  actual exterior-statistical source, constructed from the existing input,
  not an ordered tensor substituted for that source.
- Y_c is the sum of the existing integer hypercharges. N_c is the count of
  weak-doublet slots, including signed dual doublets. Torus normalization
  must make the fundamental doublet weights +1 and -1.
- Let delta=h-d in integers. Let B_(m,delta) be Sym^m of the weak doublet,
  pulled back to the full group and twisted by z^(3*delta). Define
  T_(c,m,delta) = Hom_Gamma(W_c tensor B_(m,delta), C).

The torus dictionary, signed dual action, hypercharge sign and fixed-content
source construction must be written down and checked before proof coding.
Existing full-group transport proves the boson constituents; it does not
already supply all the fixed-fermion-content interfaces needed here.

## Target theorem shape

For the original full-field coefficient space at content c and counts (h,d),
prove an iff of the following form, using precise Lean definitions:

    Allowed(c,h,d) iff
      Y_c + 3*delta = 0 and
      exists m in {0,...,N_c},
        |delta| <= m and m <= h+d and
        m congruent to h+d modulo 2 and Allowed(T_(c,m,delta)).

The redundant explicit hypercharge condition is retained to expose the
selection rule; T itself retains hypercharge covariance. Impossible or
zero fermion contents must be handled, rather than given positivity premises.
The equivalent `Forbidden` predicate should follow by negation.

Crucially, m and delta range over a finite table independent of (h,d):
0 <= m <= N_c and -m <= delta <= m with matching parity. Prove allowance is
false outside |delta| <= N_c. A representative of each table entry has
counts ((m+delta)/2,(m-delta)/2); prove these are natural counts and its
constituent test is the same actual representation. This does not say that
the whole coefficient space equals the coefficient space of that one seed.

For fixed delta with |delta| <= N_c, put t=min(h,d). The candidate threshold
is floor((N_c-|delta|)/2). Once t reaches it, the admissible bounded
constituent list is fixed. Prove exact support stabilization under pair
addition and upward support monotonicity at every degree. State the
threshold only after checking parity and natural/integer conversions.

For the fixed 180-dimensional fermion universe, exterior degrees above 180
vanish. Contents of total degree at most 180 form a finite superset; their
N_c <= 180 gives a coarse universal bound. Enumerating that superset or
proving each of its surviving Hom tests nonzero is not required. Existence
of finitely many tests is distinct from an executable classifier of them.

## Ordered phases

### 0. Freeze actual interfaces

Inspect the sources linked below and the immediate declarations they use.
Identify the existing content projection/statistical carrier and construct
its connection to the source interface in FullHiggsCoefficientBridge.
Select one two-Q fixed content as the pilot, after checking its precise
source presentation. A source bound is useful even if the pilot has a
separate color/Weyl obstruction; do not add a positive-witness premise.
Record exact declarations, import ownership and intended audit entrypoints.

### 1. Weak torus support and high-spin vanishing

Prove that the actual species slot tensors are spanned by torus eigenvectors
with total weights in [-N_c,N_c]. Transport the bound through the actual
statistics construction and to its dual. Weak-singlet slots contribute zero;
dual doublets preserve the same interval. A dimension count is not a weight
bound.

Turn an invariant bilinear coefficient into a weak intertwiner
Sym^m(doublet) -> dual(W_c). A nonzero intertwiner from the existing
irreducible Sym^m is injective. Its highest-weight vector would give weight
m in dual(W_c), contradicting the bound when m>N_c. Verify every action and
dual conversion; do not assume source semisimplicity.

Generic transport and bounded-weight helpers belong in Math; the actual SM
dictionary and its source-bound consumer belong in Physics.

### 2. Pilot original-carrier finite reduction

Apply the existing full Higgs decomposition. Prove invariant Hom over its
finite constituent product decomposes into the constituent Hom factors,
with allowance iff at least one factor is allowed. Remove high-spin factors
by phase 1. Reindex the survivors by (m,delta), retaining the common twist.
Compose with the actual pilot source/content transport to prove both
directions of the target iff and its stabilization statement.

### 3. All contents and finite universe

Generalize the constructed bound and content transport to every actual
signed content. Discharge the generic premises using the fixed input.
Prove the global finite-table reduction with all source statistics intact,
including empty content and contents killed by exterior relations. Connect
to the existing degree-180 vanishing theorem.

Use the previous DUQL/QQUE/QQQL/DUUE, uR^2 dR^4 and LLHH results as consistency
controls for charge, parity and Higgs counts. Recover their support results
from the new reduction only where their existing witnesses/exclusions
actually discharge the finite Hom tests; those individual classifications
are not premises of the general reduction.

### 4. Verify and close the selected endpoint

Register new sources and persistent strict transitive axiom audits in the
appropriate aggregates. Run focused builds/audits, one serialized full
`lake build`, layout, link and diff checks. Review statements and assumptions
against the contract, document the finite reduction and its unevaluated
tests, and commit coherent verified milestones on this branch. Do not edit
the root README or merge/push without explicit user direction.

## Stop conditions and excluded work

Allowed helpers include torus eigenbasis transport, tensor/dual/statistical
descent, finite constituent Hom decomposition and exact index arithmetic.
If the required fixed-content interface or bounded-weight descent needs a
new foundational program beyond these constructions, record the exact
missing theorem and stop for a scope decision. Do not replace it with an
assumed certificate or silently claim the pilot proves all contents.

No general compact-group classification, general invariant-theory finite
generation, friendship/saturation foundations, Lie/group integration,
dependency changes, new residual action classes, SU(6) restart, signed PS
matching, derivatives/EOM/IBP, UV realization, masses/VEVs, quantum validity,
RGE, hadronic inputs or rates are part of this endpoint.

At completion, leave Allowed(T) explicitly unevaluated. Whether to classify
it for the existing q/l residual family, and revisit the 572 assignments,
is a subsequent user decision rather than an outstanding obligation here.

## Starting sources

- [Full Higgs coefficient bridge](../../../Physics/StandardModel/Operators/FullHiggsCoefficientBridge.lean)
- [Actual Higgs constituents](../../../Physics/StandardModel/Operators/SMHiggsConstituents.lean)
- [Full Higgs connection results](../sm-support-and-lfv-decomposition/full-higgs-connection-results.md)
- [SU2 Clebsch-Gordan](../../../Math/RepresentationTheory/SU2ClebschGordan.lean)
- [Twisted SU2 Clebsch-Gordan](../../../Math/RepresentationTheory/TwistedSU2ClebschGordan.lean)
- [Existing exterior weight constraints](../../../Math/RepresentationTheory/ExteriorWeightSupport.lean)
- [Generic content support adapter](../../../Physics/StandardModel/Operators/ContentHiggsSupport.lean)
- [Previous input/result register](../sm-support-and-lfv-decomposition/results.md)

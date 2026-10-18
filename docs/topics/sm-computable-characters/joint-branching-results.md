# Joint components and algebraic occurrence

The continuation from `checkpoint 01` constructs simultaneous weak/left/right
isotypic decompositions of the **actual statistical mixed source**, preserving
color and hypercharge. For the actual Higgs coefficient target it eliminates
the remaining opaque Hom/block-equivalence tests in favor of a finite symbolic
coefficient condition, under the already approved Weyl input. No exact
multiplicity or rank numeral is evaluated or certified.

This closes the frozen uniform criterion endpoint. It does **not** give a
simplified partition-inequality classification, a separate table of every
colored highest weight, concrete zero/nonzero decisions for every entry, or
the 572-assignment enumeration. The previous numerical resource problem is
not claimed solved by making those computations faster.

In particular this criterion endpoint is not completion of the original
full q/l zero/nonzero classification. The subsequent
[structural continuation](structural-classification-results.md) decides new
mixed subfamilies and records the remaining partially occupied source boundary.

## Unconditional joint decomposition

[`SU2IsotypicEvaluation`](../../../Math/RepresentationTheory/SU2IsotypicEvaluation.lean)
groups equal SU2 irreducibles into their entire multiplicity representations.
For a continuous finite action of SU2 × K with a proved first-factor weight
bound N, evaluation constructs a complete equivariant equivalence

```text
source ≃ product over m : Fin (N+1) of Sym^m(C²) tensor Multiplicity_m.
```

Surjectivity uses the complete bounded SU2 certificate; injectivity follows
from the symbolic dimension identity, Schur's lemma and compact Hom symmetry.
No closed dimension is calculated. Unlike individual chosen SU2 copies, each
whole multiplicity carries the full commuting K action.
[`SU2IsotypicModels`](../../../Math/RepresentationTheory/SU2IsotypicModels.lean)
realizes it as an invariant evaluation range in the original normed carrier,
with proved continuity and inherited torus bounds. This permits iteration.
`SU2FiniteBranching.exists_certificate_of_dimension` also supplies an abstract
dimension-bounded certificate when a sharper source bound is unavailable.

[`SMJointWeakContent`](../../../Physics/StandardModel/Operators/SMJointWeakContent.lean)
and [`SMJointSpinContent`](../../../Physics/StandardModel/Operators/SMJointSpinContent.lean)
apply this construction three times, retaining SU(3) × U(1) on the final
`jointMultiplicity flavor p m a b`. The label ranges are

| Factor | Proven upper bound |
| --- | --- |
| Weak SU2 | `SMContentWeakBound.bound p` |
| Left spin SU2 | `SMChiralitySupport.count p false` |
| Right spin SU2 | `SMChiralitySupport.count p true` |

[`SMCompactSpinBound`](../../../Physics/StandardModel/Operators/SMCompactSpinBound.lean)
proves the independent spin bounds from actual field eigenvectors, tensor
slots and the statistical source quotient. Bounds survive the intermediate
invariant ranges. No assumption about separate-species singlets is made.

[`ExternalIrreducibleMatch`](../../../Math/RepresentationTheory/Decomposition/ExternalIrreducibleMatch.lean)
proves componentwise equivalence for external irreducibles; `SU2IsotypicMatching`
identifies the SU2 models exactly by their degrees. For any finite colored
target c, `SMJointOccurrence.hom_allowed_iff` then proves

```text
Hom(source, Sym^m ⊗ Sym^a ⊗ Sym^b ⊗ c) is nonzero
  iff Hom(jointMultiplicity_mab, c) is nonzero.
```

The product-group reordering and every factor transport are explicit.
`SMJointCoefficient.targetEquiv` identifies the actual dual Higgs constituent
with the target `(m,0,0,c_delta)`, where c_delta is color trivial and has
hypercharge `-3*delta`. SU2 self-duality and the inverse hypercharge character
are proved; they are not conventions left to the caller.

## Explicit algebraic occurrence and matching

[`SMJointAlgebraicSupport`](../../../Physics/StandardModel/Operators/SMJointAlgebraicSupport.lean)
defines `Occurs counts m delta` using the already proved actual inverse
character terms. Let f(w) be their integer Laurent coefficient. Define

```text
S(f,w) = f(w) - f(w+u) - f(w+l) - f(w+r)
       + f(w+u+l) + f(w+u+r) + f(w+l+r) - f(w+u+l+r)
B(f)   = S(f,0) - S(f,alpha) - S(f,beta)
       + S(f,2*alpha+beta) + S(f,alpha+2*beta)
       - S(f,2*alpha+2*beta).
Occurs counts m delta := B(f) != 0.
```

Here u,l,r are the weak and independent spin roots. The color roots use the
existing `diag(z0,z1,(z0*z1)^-1)` convention; hypercharge remains coordinate 5.
`spin_formula`, `root_formula` and `terms_balance` prove this expression equals
the six-root extraction. The 48 terms are symbolic function evaluations,
not a generated list of exact dimensions. Their signs can cancel: an
individual weight's presence alone is not sufficient.

The source polynomial is the product of the ten actual species' exterior
characters. Thus its coefficients retain cross-species color and spin
cancellation, generation multiplicities and exterior statistics. This is
not a test of whether each species separately contains a singlet.

The general `SMIteratedContent` interface no longer imports
`SMConstantContentRanks` merely for its dimension dictionary. Its dictionary
and statements are definitionally unchanged, but the dependency on the closed
LLHH certificate is removed. The extraction consumer imports the generic
character construction directly instead of the older request aggregate.
The existing numerical `SMNeutralSparseRanks` consumer now declares its own
direct numerical import; its statements and proofs are unchanged.

With `SMCompactMultiplicity.Input flavor p m delta` explicit:

- `local_allowed_iff` and `kernel_allowed_iff` identify actual coefficient and
  kernel support with `Occurs`.
- `joint_allowed_iff` eliminates the remaining color/hypercharge Hom for the
  canonical joint multiplicity selected by the actual Higgs target.
- `matches_iff` replaces the existential `SMFiniteConstituentSupport.Matches`
  over its complete source blocks, without choosing or evaluating them.
- `ql_test_iff`, `original_ql_iff` and `original_ql_forbidden` connect this
  criterion to the existing cyclic q/l residual action at **all Higgs counts**.
  Permission is exactly residual neutrality plus an admissible bounded weak
  label satisfying `Occurs`; no Hom or representation equivalence remains on
  that right-hand side. Forbidden is its logical negation.

Nonvanishing is sufficient because the existing Weyl-conditioned theorem
also proves the extracted integer is nonnegative. Its exact positive value
is unnecessary for support. These are uniformly proved equivalences; concrete
large inputs have not been expanded, executed or assigned truth values here.

## Other colored targets and the external boundary

[`CompactWeylHom`](../../../Math/RepresentationTheory/Characters/CompactWeylHom.lean)
constructs the continuous Hom model, uses the pinned proved Hom character and
Haar-counting identities, and proves support iff the extracted coefficient is
nonzero. For irreducible source and target, `equiv_iff` replaces an isomorphism
test by that same coefficient condition.

[`SMJointColoredSupport`](../../../Physics/StandardModel/Operators/SMJointColoredSupport.lean)
constructs the full target's character from verified color/hypercharge torus
terms and three explicit SU2 strings. It constructs the Hom presentation from
the actual source character, with source weights reversed, and proves
`joint_allowed_iff` for arbitrary bounded m,a,b. Its right side is again B(f)
nonzero, with every action retained. A nonzero Hom to a reducible target
detects a shared constituent; it does not assert that the entire target is
a source summand. An irreducible target gives component occurrence.

For this generic colored-target API, the caller supplies its verified torus
character, its continuity, and `TorusReduction` specialized to this Hom model.
That is another specialization of the **same approved Weyl integration
theorem**, not a proof obtained from the coefficient model's particular
`Input` instance. No arbitrary colored-target character or highest-weight
catalogue is assumed to have been constructed automatically. The actual Higgs
consumer above needs neither additional target terms nor this extra instance:
its polynomial is constructed and it uses exactly the existing coefficient
`Input`. Weyl integration itself remains an explicit unformalized premise.

## Verification and scope

See [verification](joint-branching-verification.md) and the
[plan with route refinement](joint-branching-plan.md).
The unchanged structural audits reject numerical evaluator imports; the
separate optional extraction audit permits generic character correctness but
rejects closed numerical certificate modules. No new axiom, dependency pin,
physical scope, numerical certificate, merge or push is introduced.

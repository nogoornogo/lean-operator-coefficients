# Colored square branching and actual paired support

Resume `proof/sm-computable-characters` from `checkpoint 01`, target `master`;
no merge or push. The [plan](colored-square-plan.md) preserves the fixed
SM inputs and the prohibition on numerical rank/multiplicity proofs.

## Complete exterior-square construction

[`ExteriorSquareCauchy.equivalence`](../../../Math/LinearAlgebra/ExteriorSquareCauchy.lean)
constructs a basis-free linear equivalence

```text
Lambda^2(A tensor B) =
  (Lambda^2 A tensor Sym^2 B) direct-sum
  (Sym^2 A tensor Lambda^2 B).
```

The symmetric and alternating square quotient maps have explicit
unnormalized sections. Their two diagonal composites are twice the identity
and their cross composites vanish. After tensor regrouping, the Cauchy
sections and projections have diagonal composite four times the identity,
zero cross composites, and reconstruct every exterior vector. Dividing
by four gives both inverse identities. This is a uniform algebraic proof,
not a dimension comparison, matrix rank, basis enumeration or imported
Cauchy-decomposition premise.

[`ExteriorSquareCauchyRepresentation.equivalence`](../../../Math/RepresentationTheory/ExteriorSquareCauchy.lean)
proves equivariance for arbitrary retained group actions. No independence,
irreducibility or finite-dimensionality hypothesis is imposed. The
arithmetic constants two and four normalize the universal square maps;
no representation multiplicity or support-table entry is calculated.

## Actual color and spin branches

[`SU3SpinExterior`](../../../Math/RepresentationTheory/SU3SpinExterior.lean)
and [`SU3ConjugateSpinExterior`](../../../Math/RepresentationTheory/SU3ConjugateSpinExterior.lean)
specialize to defining color and dual color, each tensored with the actual
SU2 spin doublet. For defining color the complete square is

```text
Lambda^2(3 tensor 2) = (dual(3) tensor Sym^2(2)) direct-sum Sym^2(3).
```

For dual color the first branch is defining color tensor Sym^2(2), and
the second is Sym^2(dual color). The second branch has trivial spin.
[`SU3DualExterior`](../../../Math/RepresentationTheory/SU3DualExterior.lean)
proves the dual-color determinant-one and exterior-duality identifications;
color is not identified with its dual. Determinant-one complementary
exterior duality gives the complete fourth, fifth and sixth branches and
overflow zero. Exterior degree three remains unproved in this construction.
The small carrier dimensions enter exterior duality and overflow only;
no multiplicity or rank numeral is evaluated.

[`SMColoredCoreBranching`](../../../Physics/StandardModel/Operators/SMColoredCoreBranching.lean)
checks the dictionary against the actual signed single-generation U/D
cores (species 1,2) and their conjugates (6,7). Both independent spins stay
in the retained semisimple group, with positive and negative cores using
different spin projections. It supplies the actual square/fourth-degree
equivalences. Hypercharge is set to one only in this semisimple restriction;
coefficient consumers must reattach it and the q/l residual action.

## Positive coupling and an actual all-Higgs consumer

[`SpinSquarePairing`](../../../Math/RepresentationTheory/SpinSquarePairing.lean)
uses the complete Cauchy inverse to give a **surjective** projection from
a color/spin exterior square to the symmetric color square whenever the
spin exterior square is an equivariant scalar line. Apply it to color
and dual color with independent spin factors. The existing symmetric-power
evaluation pairing is nonzero on a normalized vector/functional pair.
Pulling it back through both surjective projections yields a nonzero
mixed coefficient. Symmetric color-square irreducibility is not needed.
This constructs a compatible positive color coupling; it is not a general
color tensor-product classification.

[`GenerationExteriorProjection`](../../../Math/RepresentationTheory/GenerationExteriorProjection.lean)
projects onto one actual generation equivariantly and surjectively in every
exterior degree. It lifts the nonzero coupled coefficient to three
generations without assuming that an arbitrary coefficient extends from
an injected subspace. Binary statistical-source equivalence then retains
the actual fermionic statistics.

[`SMColoredPairHiggsSupport.original_ql_iff`](../../../Physics/StandardModel/Operators/SMColoredPairHiggsSupport.lean)
proves, for each canonical content U^2 conjugate-U^2 and D^2 conjugate-D^2,
all h,d and every existing cyclic scalar q/l assignment of nonzero order:

```text
Allowed(original coefficient space at h,d) iff h=d.
```

The proof reattaches the actual hypercharge and residual charges, both
zero for these contents. Necessity follows from hypercharge selection.
Sufficiency constructs the nonzero local coefficient at weak degree zero
and uses the proved Higgs consumer. This permission is not a generated
interaction or a rate. Field-order transport is available through the
existing general equal-count original-space equality.

## Remaining endpoint

The exterior-square and paired consumer are complete. The full original
q/l classification is still open. The next unproved colored core is the
middle exterior cube: scalar color tensor spin-three, plus trace-free
color endomorphisms tensor spin-one. That requires actual maps and inverse
or completeness proofs, not the existing abstract trace splitting alone.
The Q core and complete compatible color couplings across all generation
and species factors also remain. No desired occurrence, isomorphism,
Kronecker coefficient or positivity rule was added as a premise.

See [remaining obligations](colored-core-boundary.md) and
[verification](colored-square-verification.md).

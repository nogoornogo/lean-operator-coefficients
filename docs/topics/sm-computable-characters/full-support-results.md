# Complete structural support for the fixed q/l actions

The original endpoint 2 is proved for the fixed ten signed three-generation
SM species and one residual-neutral Higgs doublet and its dual. The result
is uniform in fermion content, nonzero cyclic modulus, q/l charges, and Higgs
bidegree. It uses no numerical multiplicity/rank certificate and no Weyl
or other external mathematical premise.

## Actual coefficient-space statement

[SMJointHiggsSupport](../../../Physics/StandardModel/Operators/SMJointHiggsSupport.lean)
proves `original_ql_iff`. For any species word p and Higgs counts h,d:

```text
Allowed(actual original q/l coefficient space at p,h,d)
  iff q/l charge(p) = 0
  and hypercharge(p) + 3(h-d) = 0
  and there is an m <= the proved weak slot bound such that
      m is Higgs-admissible at h,d
      and the finite positive joint condition below has a witness.
```

`original_ql_forbidden_iff` proves the complementary prohibition criterion.
The left side is `SMFiniteHiggsSupport.OriginalSpace`, not a substitute
component, a conditional source presentation, or a charge-only diagnostic.

`HiggsSupport` expands into a finite weak label followed by
`SMJointContentSupport.Supports`. The latter has only:

1. A generation occupation for each species: three counts with the required
   total. An over-capacity core is the zero expression.
2. A branch of each proved actual core decomposition. All color, weak,
   left-spin and right-spin labels belong to the same branch choice.
3. A positive color diagram for their tensor word. Evaluation pairs have
   distinct leaf owners; every determinant triple has three distinct owners.
   The number of triples and the slot permutations range over finite types.
4. Three finite Clebsch--Gordan paths, each ending at degree zero: weak
   (including the Higgs constituent), left spin, and right spin.

`supports_iff_choices` exposes the occupation and joint branch witnesses.
`JointColorSpinWord.Supports` is precisely the conjunction of the positive
color predicate and the three degree-zero path conditions. No unproved
Hom/nonzero test, kernel rank, source equivalence, signed-character coefficient
or branching assertion remains on the right side.

The result is a uniform finite mathematical criterion. No enumeration of
572 assignments or numerical rank/multiplicity table is a premise or a
separate claim of this theorem.

## Proof chain

- `SMSignedCoreJointPresentation.presentation` constructs actual presentations
  of all ten signed single-generation core exteriors at every degree.
  Q/conjugate-Q include all middle degrees and complementary duals; U/D
  and conjugates use their complete square/cube decompositions; leptons
  use the complete two-doublet and single-doublet exterior decompositions.
  Overflow vanishes by proved exterior capacity. The finite species dispatch
  selects these proved maps and is not a numerical support computation.
- `GenerationTensorSupport.allowed_iff` uses actual generation restriction
  and extension with an arbitrary target. Tensor currying and tree induction
  preserve an arbitrary spectator while choosing finite occupations.
- `JointContentPresentation` composes the core branches in every occupied
  generation. `SMJointContentSupport.sourceEquiv` identifies the actual
  ten-species statistical source after semisimple restriction. Its
  `restricted_iff` therefore applies to the actual color/weak/two-spin action.
- `SMJointHiggsSupport.local_iff` reattaches hypercharge using its proved
  necessity and neutral extension. The existing compact/full Lorentz
  coefficient equivalence preserves the entire invariant functional space.
- The original Higgs cutoff and scalar q/l separation then give
  `original_ql_iff` and its prohibition counterpart.

Each source comparison is constructed in Lean. No comparison or occurrence
is an argument that a caller must provide. The positive color theorem uses
the already proved contraction spanning, symmetry and trace-kernel arguments;
the SU2 paths use the proved Clebsch--Gordan equivalences.

## Scope and inputs

The field dictionary, three generations, scalar cyclic q/l residual actions,
and residual-neutral Higgs/dual are the fixed model input. Arbitrary residual
flavor representations still use endpoint 1 with `Allowed(T)` retained; this
result does not classify them. Operator derivatives, EOM/IBP, UV generation,
interaction rates and numerical phenomenology are outside this endpoint.
Permission means an actual nonzero invariant coefficient, not a generated
interaction. Exact multiplicities and ranks are not claimed.

The older Weyl-input and computable-character results remain separate
conditional interfaces. They are not used in this structural theorem, and
all retired numerical certificate modules remain outside active builds.

See [verification](full-support-verification.md) and the
[composition plan](joint-composition-plan.md).

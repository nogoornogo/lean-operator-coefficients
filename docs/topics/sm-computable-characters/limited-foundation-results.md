# Complete, bounded generation-occupation reduction

This is the first milestone of the
[limited-foundation plan](limited-foundation-plan.md). It implements a
complete reduction to single-generation exterior factors, independently of
the external Weyl premise and without a new literature input. It does not
decide the target occurrence in every factor, and does not complete the
original stage 2.

## Exact statements

[`FiniteExteriorExhaustion`](../../../Math/RepresentationTheory/FiniteExteriorExhaustion.lean)
proves that the actual occupation subrepresentations span the entire
exterior representation of a finite direct sum. The proof expands only a
symbolic multilinear expression. It does not list words, permutations or
exterior basis elements. `Occupation` records realizable count vectors,
each bounded by total degree, with one opaque representative per count.
`occupation_sum` proves their sum is exactly the total degree.
`occupations_span` removes the redundant word ordering from the exhaustion.

For an arbitrary retained group and arbitrary equivariant target, restriction
to the occupation sources detects whether a map is zero. Conversely, the
already proved equivariant occupation projection extends any nonzero map
from a source to a nonzero map on the full exterior representation.
`exists_nonzero_occupation_iff` proves both directions. The sources need
not have their own singlets and the target need not be trivial.

[`GenerationExteriorExhaustion`](../../../Math/RepresentationTheory/GenerationExteriorExhaustion.lean)
uses mathlib's proved `TensorProduct.piScalarRight` to identify
`V tensor Flavor_3` equivariantly with three copies of V. The resulting
exterior equivalence transports the preceding complete restriction and
extension statements to three actual generation summands. Every retained
group factor acts throughout the proof. This is stronger than merely
injecting selected generation blocks into the full exterior source.

[`SMGenerationExhaustion`](../../../Physics/StandardModel/Operators/SMGenerationExhaustion.lean)
specializes the construction to **all ten signed SM species** with their
actual compact color, hypercharge, weak and independent left/right spins.
`core` removes only the trivial generation factor from the actual field;
`actual_field` checks this identification definitionally. `occupationEquiv`
identifies each generation occupation with the tensor product of three
single-generation exterior powers via the existing complete content tree.

The final foundation interface, `exists_nonzero_bounded_factor_iff`, is

```text
Hom_G(Lambda^n Field_s, target) has a nonzero element
  iff there is a realizable triple (a,b,c), a+b+c=n,
      a,b,c <= dim(Core_s),
      whose actual tensor product
        Lambda^a Core_s tensor Lambda^b Core_s tensor Lambda^c Core_s
      has a nonzero equivariant map to target.
```

The capacity bound follows from symbolic exterior binomial factors, keeping
all dimensions unevaluated. `source_nonzero_iff` decides whether that tensor
source is zero; it does **not** decide invariant permission. The construction
does not evaluate multiplicities, ranks, character recurrences or large bases.
The existing q/l separation remains the consumer for residual charges;
the compact specialization does not assume arbitrary residual actions are
trivial on generations.

## Remaining work and exact interpretation

The old demand to branch each three-generation exterior power can now be
replaced in this construction by complete branching/support for the much
smaller single-generation cores, followed by compatible generation/species
coupling. The first milestone of the plan is proved. The next milestone
still requires the missing **joint color/weak/two-spin target occurrences**
on these exterior factors, and their cross-species assembly. This result
does not assert that the full route is already feasible or complete.

The Hom condition on the right is deliberately an internal foundation
interface. Moving it to smaller exterior factors does not constitute the
requested structural classification by itself. No desired positive support
is an assumption, no unresolved family is classified as forbidden, and no
new literature premise is introduced. The previous
[boundary](structural-classification-boundary.md) remains a description of
the unproved occurrence problem; its stopping decision has been reopened
by the user's limited-foundation direction.

See [verification](limited-foundation-verification.md).

The subsequent [joint lepton construction](lepton-joint-results.md) closes
the full weak/spin doublet-pair core and its three-generation joint support
with inequalities and parity. The remaining colored/mixed occurrences are
still distinguished from that completed subfamily.

The subsequent [signed mixed-lepton iff](mixed-lepton-results.md) also closes
actual L/conjugate-L mixed operator support for all Higgs degrees and all
existing scalar cyclic q/l assignments. Its predicate contains only explicit
capacity, parity, charge and weak inequalities; the actual nonzero direction
is constructed. Colored and other mixed families remain unclassified.

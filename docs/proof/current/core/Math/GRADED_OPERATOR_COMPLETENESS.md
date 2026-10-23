# All-Degree Coefficient-Space Decomposition for Derivative-Free Operators

## Name And Scope

The adopted name is **all-degree coefficient-space decomposition theorem for
derivative-free operators**, shortened to **all-degree coefficient-space
decomposition theorem**. “Decomposition” describes the proved linear
equivalence with a product of residual Hom spaces. Earlier documents called
this graded operator completeness; the Lean declarations and file paths retain
that identifier. The separate four-sector coefficient classification is a set
of bounded applications, not the definition of this all-degree theorem.

## Result

For finite fermion/boson species alphabets, each field carries a complex local
representation tensored with an arbitrary residual-group representation.
At every natural pair of degrees `(n,m)`, invariant functionals on
`Λⁿ Vferm ⊗ Symᵐ Vbos` are linearly equivalent to the product over species
contents of residual-equivariant functionals on constructed carriers

`Q_c = ((L_c)_G ⊗ M_c) / R_exchange`.

[GradedMixedCompleteness](../../../../../Math/RepresentationTheory/Coefficients/GradedMixedCompleteness.lean)
proves unrestricted/support-selected equivalences, prohibition/nonzero iff,
and the all-degree direct-sum functional equivalence.
[TypedMixedSeparatedHom](../../../../../Math/RepresentationTheory/Constructions/TypedMixedSeparatedHom.lean)
constructs each carrier and its two-sided equivalence. No chosen contraction
basis or coefficient-completeness premise is supplied.

## Inputs And Scope

Groups G and H are arbitrary abstract groups (`[Group G] [Group H]`); no
topological or algebraic-geometric group structure is assumed. Local and multiplicity carriers
are complex modules; no finite-dimensionality, continuity, compactness or
semisimplicity is required. Local and residual actions act on separate factors;
their commutation is proved. Support is stable under separate fermion/boson
permutations. Separately, positive integral weights imply finitely many contents
under each finite bound, by `MixedContentBounds.bounded_finite` in
[MixedContentBounds](../../../../../Math/RepresentationTheory/Content/MixedContentBounds.lean).
This is an independently audited finiteness result, not an import or a premise
of `GradedMixedCompleteness`. The existing `all_bounds_forbidden_iff` assumes no
positive weights: it compares all bounds with all degrees, not a single finite
product indexed over all degrees below one bound. A combined packaged finite-
index equivalence is not asserted here.
Additive integer charges restrict support, not replace actual local invariance.

## Proof Structure

Ordered heterogeneous tensors are regrouped canonically into local and
multiplicity tensors. Local coinvariants quotient the span of `g • x - x`.
Signed identical-fermion and unsigned identical-boson relations are transported
and quotiented explicitly; all residual actions descend. Hom descent and its
inverses prove that local invariance and exchange constraints agree with the
separated carrier construction.

Typed restriction and normalized alternation/symmetrization identify supported
exterior/symmetric functionals with ordered exchange-constrained maps.
Permutation orbits partition species profiles; projection to selected orbits
gives the product equivalence, including zero degrees. Internal classical basis
choices in tensor separation satisfy a proved pure-tensor formula and uniqueness;
they are not theorem inputs.

There is also a distinct noncanonical profile choice: `Content` is a quotient
of ordered species profiles, and `Factor` uses `x.out` (`Quotient.out`) to choose
one profile for each orbit. Thus `Q_c` abbreviates the carrier for that chosen
representative, not a definitionally representative-independent carrier.
`MixedContentOrbits.support_iff` identifies support intrinsically with the orbit,
and `support_allow` makes permutation-stable selection independent of its
representative. The product equivalence uses these internal classical choices;
users do not supply representatives as theorem hypotheses. This does not by
itself assert a separate carrier-level coherence theorem for reselecting them.

The direct sum of field carriers, the product of their algebraic coefficient
spaces, and finitely supported coefficient families are distinct. The proved
all-degree functional interface is the algebraic dual of a direct sum, hence a
product. All-degree vanishing is equivalent to vanishing at every finite bound,
without a uniform finite cutoff.

## Consumers And Verification

The [naturality and restriction integration](GRADED_COMPLETENESS_NATURALITY.md)
compares these equivalences under field presentation changes and residual-group
restriction, including selected and all-degree interfaces.

See [the SM comparison](../../applications/Physics/GRADED_BNV_COMPARISON.md) for actual signed
fields, independent multiplicities and the existing six/seven classifications.
[MixedCompletenessExamples](../../../../../Math/RepresentationTheory/Coefficients/MixedCompletenessExamples.lean)
checks two-boson exchange, mixed fermion signs, repeated-input vanishing and
inverse maps through the constructed separated quotient.

The [foundation audit](../../../../../Math/RepresentationTheory/Constructions/Audit/AuditGradedOperatorFoundations.lean)
and [SM audit](../../../../../Physics/StandardModel/Operators/BaryonOne/Inputs/Audit/AuditGradedBnvComparison.lean)
persist strict transitive checks. Final commands/evidence are in the
[topic](../../../../topics/graded-operator-completeness/README.md).

## Boundaries And Citation Role

This is an internal universal-property theorem, not a new literature-table
certificate. Earlier literature comparisons are proved bounded consumers,
not external premises. No derivatives, field strengths, EOM/IBP, amplitudes,
matching, rates, numerical inference or external generator is used.
The theorem does not compute arbitrary-H Hom, enumerate dimension-eight-to-eleven
bases or prove inevitable BNV for every symmetry. See the
[plan](../../../../topics/graded-operator-completeness/plan.md) and [assumptions](../../inputs/Math/ASSUMPTIONS.md).

## Related literature and attribution

[Li et al. (2022)](https://arxiv.org/abs/2201.04639v2) construct explicit generic
EFT bases with Lorentz/gauge/flavor and permutation organization;
[Henning et al. (2017)](https://arxiv.org/abs/1706.08520v1) develop operator-space
and Hilbert-series methods with EOM/IBP. Neither is imported as a completeness
premise or identified with this derivative-free residual-Hom equivalence.

[Mac Lane, second edition](https://link.springer.com/book/10.1007/978-1-4757-4721-8)
provides universal-construction/adjunction background. This is explanatory
reading, not evidence that the local quotient API is supplied by that book or
mathlib. Lean declaration/source links above identify implementation ownership.
See the [literature map](../../../RELATED_LITERATURE.md) for scope distinctions.

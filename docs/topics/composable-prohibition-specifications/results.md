# Results and Interface Boundaries

## Stable Specifications

`ProhibitionSpecification.Spec` stores a content predicate and permutation
stability. `pullback` turns a stable detector and any target predicate into a
specification; `charges` reuses the proved additive charge detector. Empty/full,
union, intersection, complement and arbitrary indexed union preserve stability.
`Satisfies` tests a property on the canonical content representatives.

`union_iff`, `iUnion_iff`, `mono`, `inter_of_left`, `empty_satisfies` and
`all_union_iff` express specification algebra. Prohibiting both classes means
union. Prohibiting an intersection is weaker and has no converse to prohibition
of its constituents; a Bool counterexample certifies this distinction.

## Existing Coefficient and Symmetry Interfaces

`ComposableProtection.forbidden_iff` connects the actual selected coefficient
space to contentwise residual-Hom vanishing through existing completeness.
`protected_iff` connects it to natural restriction surjectivity. Their union
laws hold at each degree and all degrees. Neither map nor field action is
redefined by a dimension count. The indexed property law applies equally to
these factor predicates. Existing product/finite-support prohibition comparisons
remain prerequisites; these spaces are not identified.

`charges_forbidden` accepts actual scalar actions and a contentwise detecting
character. The same field input accommodates every target predicate; detectors
may differ between contents. No neutral-charge existence converse is added.
Controls include overlapping specifications, the empty specification, actual
mixed degree-(1,2) phase prohibition, and neutral residual content killed by
local invariance.

## Linear Selectors and Dipoles

`CoefficientSelectorComposition.combine` packages any indexed family of
linear selectors on one common coefficient domain. `combine_zero_iff` proves
vanishing iff each component vanishes. `transport_zero_iff` transfers this
through a supplied completeness equivalence. `restriction_square` checks the
needed restriction equation under an explicit commuting-square hypothesis.

`ComposableDipoleSelection` uses the existing actual SM dipole coefficient
space and its independently proved residual-Hom equivalence. `extraction`
commutes with the product selector; `forbidden_iff` characterizes simultaneous
vanishing on residual selectors. `forbidden_of_weights` proves a whole family
vanishes when each prescribed pair has distinct detected weights. Each pair
may use a different symmetry element. Finite-dimensional target B is inherited
from the existing dipole interface. No universal flavor/mass basis is inferred.

The bounded adapter pass succeeds within the dedicated dipole domain. No
mixed-field embedding of field-strength dipoles is needed or claimed. Combining
selectors from different domains would need a supplied common-domain map; it
is not automatically provided by this family construction.

## One SM B/L Dictionary

`ComposableBLSupport` assigns existing integer 3B and L to signed SM fermions,
and zero B/L to the two admitted Higgs scalar species. `charge_eq` proves the
pair of total sums; `old_support` recovers the old nonzero-baryon predicate.
No new field-strength, spurion or opposite-flavor identification is admitted.

`bOneTwo` selects absolute 3B equal to 3 or 6; `bOneOrLTwo` selects absolute
3B equal to 3 or absolute L equal to 2. Their union identities are proved.
`Input` uses the existing actual field actions, and `inputEquiv` reuses their
proved local/residual presentation. `equiv` supplies extraction/reconstruction
with both inverse laws. `forbidden` transfers the explicit character certificate
to these actual inputs at every degree. Neither target is claimed forbidden
without its scalar-action and detection hypotheses. No protecting UV model
is constructed; mass/light-domain adapters remain separate.

# Dev–Mohapatra Selected Operator Connection

The [source register](../../../../topics/dev-mohapatra-coefficient-connection/references.md)
pins Eq.(1) and Eq.(4) of arXiv:1504.07196v2 and specifies the local
charge-conjugation/right-Weyl dictionary. The operator certificate and the
subsequent bounded supplied-action tree-level derivation are separate claims;
full normalized matching to the source remains outside them.

## Statements and Construction

[Connection source](../../../../../Physics/StandardModel/Operators/DevMohapatraConnection.lean):
`physical_invariant` closes the full SM-cover/Lorentz/residual action on the
previous coefficient. Hypercharge phases cancel with charges 4,-2,4,-2,-2,-2;
weak action is neutral, and `up_action`/`down_action` prove actual field transport.

`printed_apply` gives the source's color triples (0,1,3),(2,4,5) and Weyl
pairs (0,2),(1,3),(4,5). `downCoupling_swap`, `downCoupling_same` and
`downCoupling_selected` verify the selected antisymmetric flavor dictionary.
The selected monomial uses projections u,d,u,s,d,s. `sourceExterior` is its
full alternatization on the up/down direct sum. `sourceExterior_evaluation`
proves -2 at a specified pure probe; `sourceExterior_invariant` proves the
actual action invariance after descent. `weighted_nonzero_iff` handles a
supplied scalar coefficient and does not establish its matching origin.

[Physical source](../../../../../Physics/StandardModel/Operators/DevMohapatraPhysicalSource.lean):
`coefficient` is an actual invariant intertwiner from the sixfold exterior
power of the physical up/down field direct sum. `evaluation` and `nonzero`
transport the selected -2 witness. `satisfies` upgrades the mixed request
allowed target to the actual physical exterior coefficient domain. Tensor reorder equivalences preserve the
original color, spin and flavor carriers. No flavor-span or computed rank is
used as a premise.

## Limits of the Operator Certificate

The local reading fixes C-inverse to right-Weyl epsilon. Four-component
normalization, full flavor-summed antisymmetric UV matching, multiple-N
interference and the printed scalar prefactor are unproved. The descent is
unnormalized: -2 must not be substituted into source matching without a
normalization dictionary. No unconditional paper prefactor discrepancy is asserted.

## Bounded Supplied-Action Tree-Level Derivation

[Tree-level source](../../../../../Physics/StandardModel/Operators/DevMohapatraTreeLevel.lean)
adds an explicit derivative-free chiral action with one N, three scalar color
coordinates and selected u,d,s fields. `uv_after_scalar` and
`uv_sequential_on_shell` derive the generated current-product polynomial
from the supplied action. The noncommutative algebra-valued quadratic
elimination identities require odd source anticommutation; `current_swap`
and `generator_current_swap` prove it using mathlib exterior products.
The completed-square and stationary-variation identities retain the
Majorana half and do not assume odd sources commute.

`printedOperator_eq` identifies the explicit color/right-Weyl uu/ds/ds
contraction as twice the current product. `generated_printed` therefore
derives `(lam lamDS)^2/(2 mChiSq^2 mN)` for that contraction.
`generated_nonzero` proves nonvanishing on eighteen independent Grassmann
components under nonzero masses/couplings, by an exact six-component
restriction. `ordered_flavor_sum` quantifies the factor two from both
antisymmetric ordered d,s entries; `source_generator_order` fixes the minus
sign relative to the old U,D,U,S,D,S generator order.

`prefactor_comparison` proves a ratio 8 pi² to the recorded Eq.(4) scalar
under an identical mass/coupling/operator dictionary; `prefactors_ne`
proves conditional inequality. Identification of source C-inverse, flavor
sums, kinetic normalization and the full Hermitian action remains external.
No full polynomial-to-physical-intertwiner identity is claimed. The prior
intertwiner consumer retains its original supplied-scalar semantics.
See the [action and comparison dictionary](../../../../topics/dev-mohapatra-coefficient-connection/tree-level-results.md).

The [fixed one-N source inspection](../../../../topics/dev-mohapatra-coefficient-connection/convention-results.md)
subsequently confirms the chi-bar/chi placement and Majorana half directly
from the v2 PDF and TeX. The accepted manuscript retains the Eq.(4) factor.
This narrows source uncertainty without proving the remaining convention
dictionary or changing any theorem hypothesis.

See [results and matching stop](../../../../topics/dev-mohapatra-coefficient-connection/results.md),
[verification](../../../../topics/dev-mohapatra-coefficient-connection/verification.md)
and [reader-facing study](../../../../model-studies/dev-mohapatra/README.md).

The [fixed signed adapter](../../../../topics/dev-mohapatra-coefficient-connection/signed-results.md) proves the inverse-C dictionary
for the supplied Euclidean charge matrix and a consistent common bilinear
rescaling. It does not recover the paper's omitted kinetic or spinor conventions
or certify its signed prefactor.

The [literature-informed evaluation](../../../../topics/dev-mohapatra-coefficient-connection/literature-evaluation-results.md) proves the Dev and
Mohapatra matrix dictionaries and lower/right-block operator transport. Its
canonical-normalization comparison retains the magnitude difference (8 pi²,
or 32 pi² for an unhalved ordered flavor sum). Source adoption and full
physical matching are still explicit boundaries.

The [independent mass-inverse route](../../../../topics/dev-mohapatra-coefficient-connection/external-leg-results.md) agrees with the
sequential elimination and fixed determinant probe. Its conjugate-completion
projection identities retain explicit zero-image hypotheses; they do not prove
full Hermitian matching or stationary elimination commuting with projection.

The [literal Hermitian-action recalculation](../../../../topics/dev-mohapatra-coefficient-connection/hermitian-results.md) proves exact scalar
elimination and Hermiticity in a supplied complex star algebra. A separate
exact Grassmann calculation of the full one-N action through degree six
checks heavy stationarity through degree five in two rational cases and
recovers the earlier holomorphic coefficient. This computational heavy-field
check is not a formal all-degree stationary matching theorem. The target
paper's adoption of the convention dictionary remains unproved.

The [all-degree heavy-elimination proof](../../../../topics/dev-mohapatra-coefficient-connection/heavy-elimination-results.md)
now constructs the concrete H.c. carrier and proves an exact finite inverse,
actual left stationary equations, uniqueness, H.c.-preserving substitution
and on-shell action without degree truncation. The original H.c. action
projects to the earlier chiral coefficient. Source convention adoption,
kinetic/physical matching, loops and rates remain outside this certificate.

## Nonzero action, normalization matching and magnitude obstruction

The [normalization closure](../../../../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md)
proves nonzero of the literature operator and actual projected-action inequality
under the stated nonzero mass/coupling assumptions. Its explicit multiplier
family satisfies the matching iff `-8 pi² (a b)² = t mu² nu`, for nonzero
mass multipliers. This is not a classification of all field/kinetic conventions.

The [magnitude obstruction](../../../../topics/dev-mohapatra-coefficient-connection/review-closure-results.md)
excludes arbitrary unit phases and a specified bounded norm-compensation
family; it does not exclude all rational or algebraic identifications.
The corresponding strict audits remain registered with the physics aggregate.
Source adoption and physical matching are explicit boundaries.

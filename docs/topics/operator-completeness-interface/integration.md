# Four Consumer Integration

The shared endpoint is algebraic coordinate completeness with commuting
constraints, not an operator catalogue for arbitrary dimensions or gauge groups.
The four existing bounded classifications retain their independent input spaces.

## Common Input Contract

The model supplies a representation equivalence for each actual field and its
specified model field. It does **not** supply a coefficient, a spanning claim,
a nonzero witness or a UV matching claim. Residual symmetry remains supplied.

The realizations are intentionally different:

| Consumer | Independent realization | Field identifications | Dimension premise |
|---|---|---|---|
| Delta L one | Supported exterior fourth power on ten signed species | Species-indexed representation equivalences | None |
| Delta B two | Degree-(2,4) sixth exterior power of distinct up/down fields | Separate up/down equivalences | Finite-dimensional up/down for existing Hom assembly |
| Weinberg | Exterior-square leptons tensor symmetric-square Higgs | Separate lepton/Higgs equivalences | None |
| B/W dipoles | Two prescribed ordered tensor channels | Lepton/electron/Higgs/strength equivalences | Finite-dimensional electron flavor for existing dual/Hom conversion |

Commonality is in the primitive field correspondence and proved transport laws,
not a single record that erases these different realization types. Existing
public input records and argument lists are retained as adapters. No assertion
is made that all four accept the same exterior coefficient type.

[Invariant coefficient transport](../../../Math/RepresentationTheory/InvariantCoefficientTransport.lean)
proves `alongEquiv_compatible` and `alongStatistics` from commutation of field
maps. `alongMaps_compatible` / `alongConstraints` also allow noninvertible
scaling maps, so the six-quark degree condition includes zero scalings.
[Supported species transport](../../../Math/RepresentationTheory/SpeciesCoefficientTransport.lean)
preserves the independently specified support predicate for any finite species
set and slot count. Neither construction requires local completeness as an input
to the field-identification interface.

## Genuine Statistics Consumers

- **Weinberg:** the normalized local line has swap eigenvalue -1. The common
  theorem gives symmetric flavor from the fermion sign -1.
  `WeinbergModelSector.homEquiv` now uses this construction; `homEquiv_agrees`
  and `inverse_agrees` compare it with the former mixed-domain classification.
  SM hypercharge cancellation and actual-field inputs still precede extraction.
- **Six quarks:** the local 25-coordinate equivalence is restricted by the common
  generator-sector theorem; `source_iff` proves the complete species sign rule
  using the certified word cover. `twoProbeEquiv_agrees` and `inverse_agrees`
  retain the scalar two-probe normalization. For arbitrary typed flavors the
  chosen route is the common **pointwise injective-reconstruction theorem**, not
  a new flattening of all multilinear inputs into a finite tensor module.
  `typed_statistics_iff` proves the exchanged-flavor equations, which are used
  by the full Hom extraction and inverse. `homLinearEquiv_apply` and its inverse
  formula, followed by `sectorHomEquiv_symm_apply` and the actual-field inverse
  formula, keep the physical exterior lift explicit. The flavored space is not
  asserted to have dimension two.
- **Delta L one:** duql is the empty-generator case. qque and duue prove
  `permutation_compatible` for independently specified slot pullback and explicit
  residual actions; their restricted equivalences use the shared theorem.
  qqql uses injective local reconstruction with the independently computed
  weak/Weyl exchange matrices and color sign. The existing generator/descent
  lemmas connect these to all allowed within-species permutations.
  `extract_factorization` / `reconstruct_factorization` retain the four-family
  product and its normalization. Actual-field support transport now uses the
  generic species implementation.
- **Dipoles:** the prescribed channels have no repeated identical fields. The
  common theorem therefore specializes to an empty generator set. `equiv_agrees`
  and `inverse_agrees` prove agreement with the existing B/W product coordinates.
  Actual-field identification uses the same invariant transport primitive;
  generated/admissible UV coefficients remain a separate interface.

These are not four unconstrained wrappers: the nontrivial local actions,
exchanged flavor arguments and necessary/sufficient statistics equations are
proved in the common construction or its pointwise form. Empty-generator
consumers impose no artificial alternation on ordered fields.

## What Is Still Separate

Local gauge/Lorentz completeness remains a proved sector-specific ingredient.
The generic theorem does not discover allowed field species, deduce a residual
group from a VEV, or prove arbitrary invariant theory. Forward coefficient
pullback is contravariant; no unproved left permutation-group action or Schur
decomposition is claimed. Generator-to-full-permutation comparison remains a
consumer obligation, discharged by the existing descent/generation results here.

Finite-flavor Schur/Young decomposition, basis enumeration, further operators,
derivatives, EOM/IBP and amplitudes are optional new topics, not remaining work
on this acceptance gate. Stabilizer work can be planned separately after review.

## Verification

The owning topic records the final focused/full builds, strict transitive audit
and exact regression results. The [audit](../../../Physics/StandardModel/Operators/Audit/AuditStatisticalCompleteness.lean)
checks the common construction, physical consumer endpoints and both-direction
comparison formulas. Bosonic +1 and fermionic -1 controls guard the statistics
twist; old scalar and zero-multiplicity consumers are rebuilt in the full build.
No dependency pins, custom axioms or audit allowlists are changed.

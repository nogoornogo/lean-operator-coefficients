# Normalized Li D.37 Duql Basis Certificate

## Result

The normalized local contraction printed in Li D.37 exhausts the independently
defined derivative-free DUQL exterior coefficient sector. The certificate
proves literal contraction agreement and both residual-coordinate inverses.

Sources: [conventions](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/LiDuqlConvention.lean),
[certificate](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/LiDuqlCertificate.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/Audit/AuditLiDuqlBasis.lean).

## Inputs And Citation Role

Inputs are complex D,U,Q,L flavor modules in a common universe and specified
representations of an arbitrary abstract group H. No finite-dimensionality,
compactness, continuity or nonzero premise is needed for the residual theorem.
Finite coordinates use supplied finite bases. Physical dagger/carrier
interpretations require supplied identifications, not inferred self-duality.

[Li et al., v2 PDF page 52, D.37](https://arxiv.org/pdf/2201.04639v2#page=52)
supplies the local candidate, not a trusted completeness premise. Brackets and
gauge epsilons use chosen normalized alternating coordinate pairings. The
[source dictionary](../../../../topics/li-duql-duue-basis/source-recovery.md) fixes
field order, chirality and signs.

## Proof Structure And Normalization

Paper order L,Q,D,U becomes D,U,Q,L by an odd permutation. Weak and left
bracket reversals cancel; the source is `-k` to compensate the Fermi minus.
`ordered_apply` proves the literal full contraction on pure field tensors.
`ordered` is defined by direct gauge/spin/residual contraction and regrouping.
`candidate` is its actual distinct-species alternating descent, not defined
as the completeness inverse. `candidate_eq` proves agreement with that inverse;
`extract_candidate` and `candidate_extract` establish both identities.

## Finite Coordinates And Applicability

The index is `(I_D × I_U) × (I_Q × I_L)`. `finiteEquiv` retains exactly all H
intertwining equations on reconstructed functionals. Both inverses are included
in the linear equivalence, and `finite_inverse_is_candidate` identifies the
reconstruction with the actual candidate.

If the tensor flavor action is trivial, `flavorEquiv` is unrestricted and
`flavorBasis` is independent and spanning. Every member is a mapped literal
candidate. `flavor_finrank` gives `n_D*n_U*n_Q*n_L`; equal flavor counts three
give 81, one gives 1, and an empty input gives 0. The persistent audit checks
these finite index controls inside the Lean kernel. General H need not have
this invariant dimension.

## Four-Family Connection, Scope And Verification

`LiFourFamilyCertificate.duql` transports the actual candidate through the
existing residual equivalence into the signed-species family. Its equality
with full-family reconstruction is proved; the shared four-family product has
both inverse identities. The support theorem still derives the four families,
not assumes them.

No ABC4EFT runtime arrays, amplitude equivalence, general p/y/m/j algorithm,
derivatives, EOM/IBP, matching or rates are certified. Only standard Lean
axioms `propext`, `Classical.choice`, `Quot.sound` are permitted transitively.
Build and check evidence belongs to the
[shared topic](../../../../topics/li-duql-duue-basis/README.md).

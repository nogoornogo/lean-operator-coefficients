# Normalized Li Weinberg LLHH Basis Certificate

## Result

The normalized LLHH local candidate exhausts the independently defined sector
of invariant functionals on `Λ² Lepton ⊗ Sym² Higgs`. Its assembly and residual
extraction are mutually inverse. This verifies the printed local interpretation,
not the whole dimension-five SMEFT field-content classification.

Sources: [conventions](../../../../../Physics/StandardModel/Operators/Weinberg/LiWeinbergConvention.lean),
[certificate](../../../../../Physics/StandardModel/Operators/Weinberg/LiWeinbergCertificate.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/Weinberg/Audit/AuditLiWeinbergBasis.lean).

## Inputs And Citation Role

One Higgs weak doublet with trivial residual action, an arbitrary group R and
complex lepton flavor representation F are supplied. General completeness
requires neither finite-dimensionality nor compactness, continuity or
self-duality. Actual fields additionally require the existing equivariant
lepton/Higgs identifications; no UV correspondence is inferred.

[Li v2, page 38, Out[7]](https://arxiv.org/pdf/2201.04639v2#page=38) supplies
the candidate expression, not a completeness premise. The
[dictionary](../../../../topics/li-weinberg-basis/source-recovery.md) records the
local interpretation and citation limits.

## Proof Structure And Normalization

`ordered` assembles the proved invariant local contraction with a symmetric
residual tensor functional. `candidate` transports this through the existing
mixed-statistics universal-property descent and SM adapter, not the final
completeness inverse. `candidate_apply` identifies the polarized literal
formula; `candidate_diagonal` recovers the printed Higgs polynomial.
`candidate_eq`, `extract_candidate` and `candidate_extract` prove agreement
with the existing independent-sector equivalence and both inverses.

The spin bracket supplies the lepton-exchange minus; Higgs exchange is symmetric.
Polarization averages two weak pairings with factor 1/2. The normalized exterior
probe has factor one and the mixed probe has factor -1/2. No artificial
four-slot exterior domain or sector defined as a contraction image is used.

## Finite Coordinates And Applications

For a supplied finite flavor basis indexed by I, `finiteEquiv` gives coordinates
indexed by `Sym I 2`, with exactly the residual action equations on reconstructed
functionals. `finite_inverse_is_candidate` identifies reconstruction with the
literal candidate. `flavor_entry` proves diagonal and off-diagonal coordinates
evaluate the symmetric product directly, without an additional factor two.

When the induced symmetric-square action is trivial, `flavorEquiv` is
unrestricted, `flavorBasis` is independent and spanning, and every basis member
is a candidate. `flavor_finrank` proves `n(n+1)/2`: empty, one-generation and
three-generation controls give 0, 1 and 6. Trivial F action is sufficient, but
not necessary: `sign_candidate_nonzero` proves an actual nonzero candidate for
the nontrivial order-two sign action.

`onFields_extract` and `onFields_reconstruct` supply both inverses on actual
fields under `Inputs`. `mass_formula` gives exactly `v² k(u,w)` for the existing
specified neutral VEV evaluation, including zero at v=0. Nonzero VEV evaluation
uses the already proved Majorana equivalence, not a dynamical vacuum theorem.

## Boundaries And Verification

No general p/y/m/j construction, amplitude equivalence, derivative/EOM/IBP
classification, multi-Higgs sector, seesaw matching, RGE or numerical masses
are claimed. The persistent audit permits only `propext`, `Classical.choice`
and `Quot.sound` transitively. Verification is recorded in the
[topic](../../../../topics/li-weinberg-basis/README.md).

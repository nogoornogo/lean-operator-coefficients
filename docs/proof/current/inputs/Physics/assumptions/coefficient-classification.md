# Physics Assumptions: Coefficient Classification

[Ledger index](../ASSUMPTIONS.md). These are theorem-specific inputs, not a
universal hypothesis package. Recorded checks retain their topic checkpoints.

## Coefficient Classification

[QqueCoefficientCompleteness](../../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/QqueCoefficientCompleteness.lean)
is a classification of coefficients for fixed fields, not another source
extraction theorem. Its inputs are arbitrary complex H representations
`a : H -> GL(A)`, `b : H -> GL(B)`, `d : H -> GL(D)`, with B and D
finite-dimensional for tensor duality. A need not be finite-dimensional in
this algebraic API; the finite-dimensional physical cases are included.
No compactness, topology, continuity, unitary action, mass, conjugation,
species index, constituent overlap or nonzero premise is required.

The explicit fields are `quark tensor A`, `upRight tensor B.dual` and
`electronRight tensor D.dual`, with the same Q field in both slots and the
existing left/right Weyl-spinor actions. The sector is specified independently
by SM-cover x H x SL(2,C) invariance and species scaling degree (2,1,1) on
the fourth exterior power. It is not defined as the assembly image.
Gauge and spinor contraction uniqueness, ordered reconstruction and residual
Q-slot symmetry prove `fromHom_surjective` and the linear equivalence `equiv`.

`onFieldsEquiv` transports the full classification through supplied SM x H
equivalences of three participating field spaces with those explicit fields.
`exists_on_fields_iff` and `hasNonzeroAlternation_iff` give the necessary and
sufficient nonzero-Hom criterion. These identifications can be provided by
the existing source routes, but their existence for an arbitrary radical is
not proved by the classification. Existing `HasNonzeroAlternation` endpoints
connect through `QqueCoefficientSector.hasNonzeroAlternation_iff`.

This qque theorem alone covers the fixed derivative-free qque sector and the participating spaces
specified, not every exterior degree-four component, all Delta B = 1 classes,
or a derivative/EOM/IBP quotient. No automatic computation of the Hom space,
automatic irreducible decomposition, stabilizer classification or
vacuum-derived H is asserted. See [proof and verification](../../../../../topics/qque-coefficient-completeness/results.md).

### Normalized Published Qque Coordinates

[Li D.38 basis certificate](../../../applications/Physics/LI_QQUE_BASIS.md) interprets the printed epsilon
and bracket contraction in explicit normalized local bases. The gauge/flavor
dagger convention is algebraic contragredience with constructed gauge bidual
identifications; physical conjugate-field identifications remain model inputs.
The semantic family retains arbitrary H and A; B,D are finite-dimensional only
for the residual Hom equivalence. Finite coordinate corollaries additionally
supply finite bases of A,B,D. For nontrivial H the coordinate matrices must
satisfy intertwining equations; unrestricted matrix units form a basis only
with trivial residual action. Both coordinate inverses and every finite
candidate's contraction map are proved. No literature completeness premise,
package execution, general amplitude correspondence or physical normalization
is used. The factor 2 from raw exterior alternatization is explicit.

### Li Weinberg Local Certificate

`LiWeinbergCertificate` certifies Li v2 page 38 Out[7]'s normalized local
LLHH contraction against the independently defined mixed exterior/symmetric
Weinberg sector. Inputs remain arbitrary complex flavor representation F of
an arbitrary group R, one Higgs doublet with trivial residual action, and
explicit equivariant field identifications for actual-field transport.
Candidate assembly/extraction have both inverses. Finite bases yield exact
residual constraints on `Sym I 2` coordinates; only trivial induced Sym² action
licenses the unrestricted basis and dimension `n(n+1)/2` (three flavors: 6).
The nontrivial order-two sign representation has a nonzero candidate.
Specified neutral VEV evaluation is exactly `v² k`, not a vacuum-discovery
or UV-generation result. Li is candidate data, not an assumed completeness
premise; no runtime output or general amplitude/basis algorithm is certified.
See [dossier](../../../applications/Physics/LI_WEINBERG_BASIS.md) and
[topic](../../../../../topics/li-weinberg-basis/README.md).

### Li Duql And Duue Local Certificates

`LiDuqlCertificate` and `LiDuueCertificate` independently certify the normalized
local interpretations of D.37 and conjugate D.6, with actual exterior descent
equal to the existing completeness inverses. Inputs remain specified complex
flavor representations of arbitrary abstract H; finite coordinates use supplied
bases. Their invariant coordinate subspaces retain all action equations.
Unrestricted basis/count statements additionally require trivial tensor flavor
action. Equal three-flavor counts give 81 for each family, without conjugate
doubling. DUUE retains both symmetric and alternating U sources, not only Sym²U.
Physical dagger/conjugation identifications remain model inputs; only scalar
local-factor conjugation is proved automatically. The shared four-family
composition has both inverse identities and uses direct multiplicity carriers,
with the QQUE literal formula checked in that convention. It does not infer
an identification with the older QQUE dual-coordinate interface.
See [DUQL](../../../applications/Physics/LI_DUQL_BASIS.md), [DUUE](../../../applications/Physics/LI_DUUE_BASIS.md) and the
[topic](../../../../../topics/li-duql-duue-basis/README.md). General Li basis algorithms,
runtime arrays and amplitude correspondence remain outside the certificate.

### Qqql Flavor Component Presentation

`QqqlFlavorComponents.exteriorEquiv` decomposes the independently defined
degree-(3,1) physical exterior sector into symmetric, alternating and mixed
residual functionals. Inputs are arbitrary complex Q,L modules and specified
representations of an arbitrary abstract group H; finite dimensionality,
compactness and continuity are not required. The mixed functional is symmetric
in its last two Q inputs with zero cyclic sum. The component equations are
necessary and sufficient, and both coordinate inverse identities are proved.
With supplied bases indexed by Fin n and Fin m, `QqqlFiniteFlavor.exteriorEquiv`
gives nonredundant finite coordinates constrained by the actual H equations on
their interpolated functionals. Both inverses are proved. With trivial residual
action `flavorEquiv` is unrestricted, its transported basis is independent and
spanning, and `flavor_finrank_binomial` gives
`m * (choose(n+2,3) + choose(n,3) + n*n-n + 2*choose(n,3))`;
three Q and three L flavors give dimension 57, without conjugate doubling.
Actual carriers enter through supplied equivariant identifications.
`LiQqqlExterior.candidate_eq` identifies raw exterior descent of the normalized
literal D.9 seed with this complete inverse, using source `-T-U/3+V`.
Exhaustiveness and candidate injectivity are proved, not inferred from counting.
This is a local contraction certificate, not a general Li basis algorithm or
ABC4EFT runtime certificate; see the [dossier](../../../applications/Physics/LI_QQQL_BASIS.md).
The strict component audit permits only `propext`, `Classical.choice` and
`Quot.sound` transitively.

### Full Light-Species Connection

[FullLightSpeciesQque](../../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/FullLightSpeciesQque.lean)
takes a finite-dimensional complex SM-cover x H representation tau on K and
semisimplicity of its SM restriction. H is an arbitrary abstract group; no
topology, compactness or semisimplicity of its action is required. Define
Q as the evaluation image of ALL `Hom_SM(quark,K)`, and U/E as the evaluation
images of ALL `Hom_SM(upRight,K.dual)` and `Hom_SM(electronRight,K.dual)`.
`image_le_iff` proves the evaluation image is the smallest subrepresentation
containing every value of every such intertwiner. The three membership lemmas
make the no-omission property explicit, including on the dual side.

Multiplicity duality identifies the latter two full multiplicities with
`Hom_SM(upRight.dual,K).dual` and `Hom_SM(electronRight.dual,K).dual`.
These field identifications are derived, not supplied. `equiv`, `nonzero_iff`
and `all_forbidden_iff` classify the entire degree-(2,1,1) sector on these full
standard species. Existing `LightSMFieldExtraction.Fields` certificates use
the same full multiplicities; `supplied_alternation_iff` connects their qque
existence statements to this full sector, without a positive-support premise.

[FullLightRadicalQque](../../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/FullLightRadicalQque.lean)
specializes this to the unchanged radical of the existing symmetric mass B.
The ambient/mass carrier interface and compatible SM-cover x H action D remain
inputs. Only joint continuity of the SM restriction of D.action is required;
SM compactness derives its semisimplicity. The existing full-action continuity
premise also suffices via restriction. No conjugations, T-unitarity, exact
spectrum, species indices or residual positive support are needed to state
the necessary-and-sufficient test. Unlike an existence theorem, it does not
assert that the Hom space is nonzero for every model.

The zero criterion forbids all derivative-free qque coefficients built from
these standard Q/U/E species, including all their multiplicities. It is not
a prohibition of every degree-four operator on K plus K.dual, exotic-species
operators or all Delta B = 1 classes. Zero on arbitrary smaller participating
spaces is not a model-wide prohibition. H is not reconstructed from a vacuum,
and the criterion is not an executable Hom-space decision algorithm.
See [scope and verification](../../../../../topics/qque-full-species-boundary/README.md).

### Equivalent Common-Irreducible Criterion

[QqueCommonIrreducible](../../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/QqueCommonIrreducible.lean)
adds a necessary-and-sufficient constituent test for the same complete qque
sector. With actual left-chiral multiplicities A, B and D, the condition is
that `Sym^2 A` and `B tensor D` contain isomorphic nonzero simple submodules
over the group algebra. These are actual representations, not virtual indices.
The comparison is AFTER the symmetric square and tensor product, not between
the individual Q/up/electron representations.

The algebraic core requires only semisimplicity of `Sym^2 A`; it does not
require target semisimplicity, a finite group or a topology. The coefficient
adapter retains the finite-dimensional B and D assumptions of the existing
classification. The compact adapter derives source semisimplicity from a
finite-dimensional normed A and its continuous action of compact H. It does
not require independent continuity of B or D for this abstract adapter.

`full_nonzero_iff` additionally uses SM semisimplicity to derive all actual
field identifications. `radical_nonzero_iff` and `radical_forbidden_iff` use
compact H and joint continuity of the compatible SM-cover x H action on the
unchanged radical. They cover the full specified standard-species qque sector,
not an extracted constituent alone. No spectrum, conjugation, positivity or
species-index equation is required. The arbitrary-H Hom classification remains
available without these extra semisimplicity/compactness premises.

For Circle, A=1, B=z and D=z^-1 have post-product overlap and a nonzero exterior
coefficient, although A and B have no common constituent. This checked
field-model control is not an ambient GUT construction. In particular, the
older pairwise-positive and other source routes remain sufficient, not
necessary. No executable decomposition or reconstruction of H is claimed.
See [results and verification](../../../../../topics/qque-common-irreducible/README.md).

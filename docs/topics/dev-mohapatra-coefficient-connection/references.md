# Sources and Conventions

Primary source: Dev–Mohapatra, [arXiv:1504.07196v2](https://arxiv.org/abs/1504.07196v2),
PDF [versioned](https://arxiv.org/pdf/1504.07196v2). The unversioned PDF inspected
on stage 01 has the v2 header (5 June 2015). Sec.II Eq.(1) supplies parity
and antisymmetric down-flavor couplings. Sec.III p.3 Eq.(4) prints the color
and charge-conjugation contraction and scalar prefactor; Fig.1 and Eq.(3)
provide the proposed tree route. This is an algebraic operator comparison,
not verification of the subsequent hadronic estimates or rates.

Previous [bounded result](../non-susy-mixed-candidates/results.md) proves
allowance of a selected coefficient, not the printed source channel.
Repository conventions: ordered species slots U,D,U,D,D,D; hypercharges
4,-2,4,-2,-2,-2 in the integer cover convention; right Weyl epsilon and color
epsilon. Source flavor placement is u,d,u,s,d,s, so color triples are
(0,1,3),(2,4,5) and spin pairs are (0,2),(1,3),(4,5).
The conversion of C-inverse to right Weyl epsilon must remain explicit.

For the authorized [tree-level phase](tree-level-plan.md), Eq.(3), Fig.1 and
Eq.(4) were rechecked against the v2-header PDF on stage 01. Eq.(3) supplies
the proposed inverse-Mchi² intermediate route; Fig.1 and the text call the
six-quark route tree-level; Eq.(4) explicitly includes inverse 16 pi².
The [explicit action dictionary](tree-level-results.md) is local supplied
data, not a claim that all suppressed source conventions are recovered.
Browser screenshot retrieval failed with a cache miss; the scalar transcription
was checked in the PDF text. No downstream rate or loop formula is used.

Additional reusable sources:

- [Algebra-valued quadratic elimination](../../../Math/LinearAlgebra/AlgebraValuedQuadraticElimination.lean): local extension of the paired action to noncommutative values and odd Majorana sources.
- [Existing Weyl mass convention](../../../Physics/FieldTheory/Mass/WeylGrassmannAction.lean): two-component Grassmann pairing and Majorana half convention; the new phase proves its own generic half identity.
- mathlib `ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm` and `ι_mul_ιMulti_anticomm`: direct reuse for odd cubic currents.
- mathlib `ExteriorAlgebra.liftAlternating_apply_ιMulti`, basis determinant and exterior-algebra map: direct reuse for exact coefficient extraction and restriction.

- [Physical flavor transport](../../../Physics/StandardModel/Operators/DeltaBTwoFlavorBridge.lean).
- [Existing witness](../../../Physics/StandardModel/Operators/DevMohapatraSixQuark.lean).
- [Species sum](../../../Math/RepresentationTheory/SixSlotSpeciesSum.lean).
- [Local color/Weyl coefficient](../../../Physics/StandardModel/Operators/SixQuarkInvariant.lean).

## Fixed One-N Convention Inspection (stage 01)

The [inspection result](convention-results.md) supersedes the earlier
text-extraction limitation: the downloaded v2 PDF was rendered locally and
Eq.(1) inspected at higher resolution. Its chi-bar at the N-u vertex is
visible. The v2 TeX archive independently confirms it and the Eq.(4) scalar.

| Source | Pinned locations and role | Download SHA-256 |
| --- | --- | --- |
| [arXiv v2 PDF](https://arxiv.org/pdf/1504.07196v2), downloaded via the unversioned PDF with v2 header | pp.2–3 Eqs.(1),(3),(4), Fig.1; actual symbols inspected | `3208b40c96fe7f6c473840a05c03a8be111d77f4e48dcc1b447a6ce7e514a849` |
| [v2 TeX source](https://arxiv.org/src/1504.07196v2), member `arXv2.tex` | lines 121–127: mass half, chi-bar, chi, selected coupling labels; 166–168: literal Eq.(4). No vertex sum restriction or C matrix definition was found | `565d6bca4cff5c5f570fcdc3fb6d68319209a8eb588fd8f7200f3b2ac01c8c05` |
| [APS CHORUS accepted manuscript](https://link.aps.org/accepted/10.1103/PhysRevD.92.016007) | pp.3–4 Eqs.(1),(3),(4), Fig.1; publication-stage comparison, not final publisher typesetting | `434bf4acb641fce187c716148c9d75a7011235661f37b2a5a6c3ff262df83aea` |
| [Publisher record](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.92.016007) and [arXiv record](https://arxiv.org/abs/1504.07196) | Publication identity and version history only; no claim that the typeset formulas were inspected | Not applicable |
| [Babu–Mohapatra–Nasri, hep-ph/0612357v3](https://arxiv.org/pdf/hep-ph/0612357v3) | Ref.[11] in v2; Sec.II Eq.(1), Sec.V Eq.(14). Citation provenance and absence of an exact transferred convention dictionary; supersymmetric model outside this verification scope | Not downloaded; inspected PDF text has v3 header |

Files were retained only as disposable inspection artifacts under `/tmp`;
no full third-party paper or TeX source was copied into the repository.
The bounded correction search did not locate a clarification for the Eq.(4)
factor. This is not an exhaustive erratum survey or a claim that none exists.

## Signed-adapter reuse

The [signed result](signed-results.md) uses repository definitions in
[RightWeylChargeConjugation](../../../Physics/FieldTheory/Spinor/RightWeylChargeConjugation.lean)
and [DevMohapatraTreeLevel](../../../Physics/StandardModel/Operators/DevMohapatraTreeLevel.lean).
The supplied Euclidean C and right projector are not attributed to the paper.
[ChiralActionConvention](../../../Physics/FieldTheory/Mass/ChiralActionConvention.lean)
and [GrassmannCoefficient](../../../Math/LinearAlgebra/GrassmannCoefficient.lean)
were inspected as possible further adapters; their conditional kinetic and
pairing interfaces are not premises of the present signed proof.

## Related-author and citation survey (stage 01)

See [the location-by-location survey and transfer decisions](related-conventions-results.md).
Pinned PDFs were inspected with pdftotext; key C, Weyl-action and Majorana
appendix pages were rendered with pdftoppm and visually checked. Browser
screenshots again returned cache misses. Institutional manuscript retrieval
resolved the inaccessible final 1981 PDF; no final-typeset inspection is claimed.

| Inspected PDF | SHA-256 |
| --- | --- |
| [1404.1003v4](https://arxiv.org/pdf/1404.1003v4) | `d5796a7ead6356ec00f8d7b24c55bb2505c5267e60a00971c11672ba1402c996` |
| [Mohapatra–Senjanovic institutional manuscript](https://inspirehep.net/files/78ee796b5ef38d1d83d344fd170b03f8), FERMILAB-PUB-80-061-THY | `d2fff578da10af267a0504309c72f04a7724c1b0574e81fc0d783688fe91c622` |
| [1712.02713v2](https://arxiv.org/pdf/1712.02713v2) | `3f765b42b1df446197d6800b4f647f9d4cfd76ec7605e306f16507153e4f3032` |
| [hep-ph/0612357v3](https://arxiv.org/pdf/hep-ph/0612357v3) | `29fef8da734f2a5cb577792b8d8fb3c2195ba7a6b693dcbc13228296818389c3` |
| [1305.0287v1](https://arxiv.org/pdf/1305.0287v1) | `32b9836b9f62f9fb3720a1b76ebd26e0cd3b5db5f43b8b736633a78723703231` |
| [1304.0711v1](https://arxiv.org/pdf/1304.0711v1) | `79085b1fa0972ee5344a698bfececd514d2dc4e831a7edaab82f6300d7271a51` |
| [1504.07244v2](https://arxiv.org/pdf/1504.07244v2) | `ac906c159a8c0379ff4ca233f792e06e100c80fcb5f48fb09929ca8ab5bfafd6` |
| [1303.6918v2](https://arxiv.org/pdf/1303.6918v2) | `72523060c2504628e5dfe52cc42ffc02bc74dbc26035c04ae9fcfc04809238bf` |
| [0811.3411v3](https://arxiv.org/pdf/0811.3411v3) | `d9cc3e492145de2f180e2b887bd094ffae017ead11b0268547af0e329e397714` |
| [1502.06541v3](https://arxiv.org/pdf/1502.06541v3) | `c3b40a5c73b99629672d9707439dce3168b890b226a3d0abcfb39ae3d9f6c712` |

Unversioned requests were pinned by actual PDF headers where used. A guessed
1303.6918v3 URL failed; the inspected header is v2. Downloaded papers and
renders remain disposable /tmp artifacts; only provenance and findings enter
the repository. Supersymmetric sources are notation evidence, not an expansion
of the non-SUSY model verification scope. A discovered corrigendum to
1404.1003, [1504.07640](https://arxiv.org/abs/1504.07640), concerns resonant
leptogenesis numerical examples; its abstract was inspected only. No inference
about the target Eq.(4) follows from that corrigendum.

The [literature-informed evaluation](literature-evaluation-results.md) uses
the pinned Dev Appendix B Weyl gamma blocks, C phase stated at Eq.(3.31),
and the pinned Mohapatra Appendix A gamma blocks/C definition, pp.33,36–37.
It proves their matrix and lower-block consequences in Lean; it does not
infer that citation [28] adopts these conventions for the target quark vertices.

## Fixed external-leg assets

The [external-leg result](external-leg-results.md) reuses the explicit
DevMohapatraTreeLevel currents, mass action, determinant probe and completed
quadratic elimination. Its inverse mass kernel and vertex contraction are
separately defined in [DevMohapatraExternalLeg](../../../Physics/StandardModel/Operators/DevMohapatraExternalLeg.lean).
[ExteriorConjugation](../../../Math/RepresentationTheory/ExteriorConjugation.lean)
was inspected for the further H.c. bridge; its semilinear coefficient interface
is not a premise proving a star anti-involution or a full stationary solution.
The paper/source conventions remain those pinned in the prior register.

## Hermitian recalculation library inputs

The [Hermitian plan](hermitian-plan.md) and [result](hermitian-results.md)
use the pinned mathlib StarModule/StarRing laws and the local
Math.AlgebraValuedQuadraticElimination identities. The inspected mathlib
LinearAlgebra/CliffordAlgebra/Star.lean explicitly fixes scalar coefficients
under its Clifford conjugation; it is not used as physical complex H.c.
No new external paper or convention adoption is introduced in this phase.

## All-degree heavy-elimination provenance

This phase introduces no new paper normalization input. It retains the
[literature dictionary](literature-evaluation-results.md), and the prior
[Hermitian plan](hermitian-plan.md) is superseded for heavy elimination by
the explicitly authorized [all-degree plan](heavy-elimination-plan.md).

The following library sources were inspected and used from mathlib revision
`1a547d8a48a8fa7877d2decb69d7294723bb0187`, as pinned in
[lake-manifest.json](../../../lake-manifest.json). No pin was changed.

- [ExteriorAlgebra/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean): exterior universal property, lift, generator square zero and induction. Directly reused; local odd-element lemmas extend its generator identities.
- [ExteriorPower/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/LinearAlgebra/ExteriorPower/Basic.lean): `subsingleton_of_span_eq_top_of_card_lt` is the finite-degree vanishing input. The matrix-entry degree and concrete kernel bound are local proofs.
- [Algebra/Ring/GeomSum.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/Algebra/Ring/GeomSum.lean): `geom_sum_mul_neg` and `mul_neg_geom_sum` are directly used for exact finite inverses. No analytic Neumann-series convergence theorem is invoked.
- [CliffordAlgebra/Conjugation.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/LinearAlgebra/CliffordAlgebra/Conjugation.lean): reverse and grade involution are directly reused. Complex scalar conjugation and the field swap are constructed locally.
- [CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean): `contractLeft` and its generator recursion provide actual Grassmann left differentiation at zero quadratic form. The graded Leibniz rule and model action bridge are local proofs. The source file attributes its mathematical background to Grinberg and Bourbaki; those references are not additional matching premises here.
- [Algebra/Star/Module.lean](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/Algebra/Star/Module.lean): compatible complex star-module interface. A concrete local instance is now constructed; mathlib's scalar-fixed Clifford star is not replaced globally.

The [result](heavy-elimination-results.md) distinguishes these reused library
inputs from local theorems and from still-conditional literature conventions.

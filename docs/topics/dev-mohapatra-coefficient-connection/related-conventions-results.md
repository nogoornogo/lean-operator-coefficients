# Related-Source Convention Survey

The [bounded search plan](related-conventions-plan.md), continued from checkpoint 01,
is complete. Explicit spinor and kinetic conventions **do exist** in related
author papers. They provide useful candidate dictionaries, but none inspected
states that its complete dictionary governs the selected Eq.(4) coefficient
in arXiv:1504.07196v2. No new premise was inserted into Lean.

## Useful findings

| Source and inspected location | Explicit evidence | Transfer decision |
| --- | --- | --- |
| Dev–Millington–Pilaftsis–Teresi, [1404.1003v4](https://arxiv.org/pdf/1404.1003v4), printed pp.22–23, Eqs.(3.27)–(3.31); Appendix B.1, pp.80–81, Eqs.(B.1)–(B.5) | Charge-conjugation phase C = i gamma0 gamma2; Weyl spinor ordering, gamma matrices, unit-coefficient Dirac kinetic action, and explicit Weyl/Dirac basis rotation | Strong candidate for a supplied Minkowski dictionary. The target cites this paper as Ref.[28] for flavor effects, not an explicit adoption of its quark-vertex conventions. Its Dirac kinetic action alone does not settle the target Majorana normalization or scalar kinetic term |
| Mohapatra–Senjanovic, [FERMILAB-PUB-80-061-THY](https://inspirehep.net/files/78ee796b5ef38d1d83d344fd170b03f8), July 1980 manuscript of [Phys. Rev. D 23, 165 (1981)](https://doi.org/10.1103/PhysRevD.23.165), Appendix A, pp.33,36–37, Eqs.(A.9)–(A.12) | Explicit spatial gamma blocks (0,-i sigma; i sigma,0), gamma4, gamma5 and C = gamma2 gamma4; C transpose = -C = C inverse. Chiral kinetic action, mass half and two-component equation are written together | Particularly useful historical Majorana convention. Shared author and seesaw lineage do not establish adoption in 2015. The upper block is called left-handed here; it is called right in the existing repository convention. A chirality/field dictionary is essential |
| Allahverdi–Dev–Dutta, [1712.02713v2](https://arxiv.org/pdf/1712.02713v2), Sec.II p.2 Eq.(1), p.3 Eq.(9) and references [16],[17] | Explicit two-component Weyl notation, conjugate-quark labels, same singlet-Majorana/color-triplet interaction family, Majorana mass half, and an ij sum in the width | Closest inspected Dev follow-up, explicitly citing the target. Kinetic terms are still placeholders; no explicit independent-pair summation rule or charge matrix is supplied. A width sum is not a proved vertex normalization dictionary |
| Babu–Mohapatra–Nasri, [hep-ph/0612357v3](https://arxiv.org/pdf/hep-ph/0612357v3), Sec.II p.3 Eq.(1) | Antisymmetric lambda-prime and Majorana half in the superpotential of the target's Ref.[11] | Supports notation lineage, not an exact component-action dictionary. SUSY model is not admitted as a model verification |
| Allahverdi–Dutta–Mohapatra–Sinha, [1305.0287v1](https://arxiv.org/pdf/1305.0287v1), p.2 Eq.(1) | Same superpotential family, antisymmetric flavor coupling, Majorana half; target Ref.[16] | No explicit sum-domain/kinetic/C dictionary recovered; notation evidence only |
| Allahverdi–Dutta, [1304.0711v1](https://arxiv.org/pdf/1304.0711v1), p.2 Eq.(1) and following paragraph | Non-SUSY Weyl singlet/color-triplet precursor, antisymmetric down-flavor coupling, Majorana half | Cited by the Dev follow-up; kinetic terms remain placeholders. Does not resolve ordered versus independent flavor sums |
| Davoudiasl–Zhang, [1504.07244v2](https://arxiv.org/pdf/1504.07244v2), p.3 Eq.(10) and following matching paragraph | Explicit PR vertices and contact coupling identified as fa f-prime / MT squared, without a loop factor in that scalar exchange | Target Ref.[20], acknowledged related work; different scalar quantum numbers/flavor channel. Useful comparison, not normalization of the target's six-quark coefficient |
| Babu–Dev–Fortes–Mohapatra, [1303.6918v2](https://arxiv.org/pdf/1303.6918v2), pp.4–5 Eq.(2), p.11 discussion after Eq.(7); Babu–Dev–Mohapatra, [0811.3411v3](https://arxiv.org/pdf/0811.3411v3), model interactions | Explicit multiplet-dependent half/square-root factors in the sextet model, with final-state normalization discussed in the 2013 paper; target Ref.[12] | Different sextet model. Its factors must not be transplanted to the target color-triplet vertex |
| Deppisch–Dev–Pilaftsis, [1502.06541v3](https://arxiv.org/pdf/1502.06541v3), pp.2,4, Eqs.(1),(2) | C-inverse bilinear notation and Majorana half; target Ref.[10] | Further notation support, without the target's complete kinetic/flavor dictionary |

The old manuscript's displayed matrices give spatial gammas opposite in sign
to the repository's Euclidean gammas, with the same off-diagonal gamma4.
Thus its C is minus the repository C, by direct block-matrix inspection.
This observation is a candidate translation, **not a new Lean certificate**.
Identifying just C, without translating the chirality, mass, couplings and
operator simultaneously, would not settle a signed comparison.

## What can now be supplied, and what remains unresolved

It is no longer accurate to say that no related source provides kinetic or
charge-conjugation conventions. There are two concrete documented choices:
the modern Dev Minkowski/Weyl-Dirac dictionary and the older Mohapatra
chiral/Majorana dictionary. Either could guide a future literature-informed
conditional adapter using the existing algebraic assets. They are alternatives
whose field and phase maps must be made explicit, not a single recovered
2015 dictionary.

The remaining most model-specific gap is the down-flavor vertex normalization:
none of the inspected selected interactions specifies all of the summation
range, an optional flavor half, and the relation between the printed
lambda-prime and the component Feynman-rule coupling. Antisymmetry alone does
not decide this. The existing ordered_flavor_sum theorem already shows the
two-entry versus independent-entry factor; the resulting squared coefficient
choice remains conditional. No rate formula was used as a matching premise.

Canonical normalization is a defensible explicit model assumption, with the
related sources supporting usual spinor choices, but it is still not a sourced
proof of the target's suppressed full action. The selected Eq.(4) sign and
normalization remain unconfirmed as a complete source match. The survey does
not establish that an author clarification or an uninspected appendix cannot
exist; it is a bounded search, not an exhaustive negative result.

## Admission decision

Retain the proved supplied-convention adapter unchanged. Use the newly found
sources as provenance for candidate conventions, without upgrading them to
theorem premises or calling the paper's prefactor certified. No new kinetic
calculus, Majorana propagator framework, loop calculation, numerical
phenomenology, author contact or model extension was started.

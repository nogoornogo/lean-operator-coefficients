# Primary Sources And Local Inputs

This work reuses the six pins in the
[comparison register](../derivative-literature-comparison/references.md).
Selected PDF text is reinspected as needed; no complete paper theorem is
imported into Lean as a premise.

- A / C3: Grzadkowski et al., [1008.4884v3](https://arxiv.org/pdf/1008.4884v3),
  Section 5, Eq. (5.3). Guideline for cross-class Higgs reduction, with the
  project's explicit gaugeless/Yukawa-free normalization derived locally.
- B / C2: Henning et al., [1706.08520v1](https://arxiv.org/pdf/1706.08520v1),
  Section 6.1, Eq. (6.3). Free four-scalar finite-sector expectations only;
  actual group/quotient completeness must be proved independently.
- B / C4: Murphy, [2005.00059v6](https://arxiv.org/pdf/2005.00059v6), Table 2.
  The three Higgs four-derivative contractions; no raw-polynomial probe
  is treated as an admitted quotient functional.
- C / C5: Li et al., [2005.00008v3](https://arxiv.org/pdf/2005.00008v3),
  Eqs. (4.24)–(4.26), and Murphy Table 5. Conventions and fixed-flavor current;
  no full basis or four-component dictionary is assumed.
- Optional C1 control: Henning et al., [1507.07240v1](https://arxiv.org/pdf/1507.07240v1),
  Eq. (3.11). Fixed two-species finite sectors, not an all-orders series proof.
- C6 control: Criado and Pérez-Victoria,
  [1811.09413v2](https://arxiv.org/pdf/1811.09413v2), Section 3, Eq. (3.2).
  First-order response and higher-order boundary, tested on the project's
  constructed quartic polynomial example; no analytic equivalence premise.

## Renewed Primary-Source Inspection

All six pinned primary PDFs were reopened for the
[literature recheck](literature-recheck.md); the listed equation/table text
was inspected. Page numbers here count PDF pages from one, rather than
the printed article pagination. This is selected-location inspection,
not a paper-wide verification or imported completeness theorem.

| Case | Reinspected location | Convention checked |
| --- | --- | --- |
| C1 | 1507.07240v1, PDF p. 13, Eq. (3.11) | One-/two-species generating-series expectations |
| C2 | 1706.08520v1, PDF p. 58, Eq. (6.3) | Four-identical-scalar coefficients at derivative degrees 0,2,4 |
| C3 | 1008.4884v3, PDF pp. 3,9, Eqs. (2.1),(5.3), and Table 2 | Potential normalization a=-m2, b=lambda; schematic class terms versus exact coefficients |
| C4 | 2005.00059v6, PDF p. 20, Table 2 | Three distinct Higgs four-derivative index orders |
| C5 | 2005.00008v3, PDF pp. 33–34, Eqs. (4.23)–(4.26); 2005.00059v6, PDF p. 23, Table 5 | Odd order, Pauli/bidirectional current and factor of i; four-component conversion remains a proof obligation |
| C6 | 1811.09413v2, PDF p. 10, Eq. (3.2) | First-order EOM term versus retained higher coefficients |

## Nonderivative Input Inspection

For the [nonderivative recheck](nonderivative-recheck.md), the same primary
pins were reopened at these selected text locations: 1507.07240v1 Eq. (3.11)
(PDF p. 13), 1706.08520v1 Eq. (6.3) (PDF pp. 58–59), 1008.4884v3 Eq. (2.1)
and Table 2 (PDF pp. 3–4), and 2005.00008v3 Eqs. (4.20)–(4.21) (PDF p. 33).
These identify scalar zero-derivative powers, rho squared/rho cubed and a
two-odd/five-even pattern. The latter motivates only a constructed statistics
input control here, with no SM species/flavor or physical symmetry dictionary.
No paper count or external completeness premise is imported. The earlier
C3 table location should be read with Table 2 on PDF p. 4; its two equations
remain on PDF pp. 3 and 9.

Local inputs: the existing
[Higgs controls](../../../Math/RepresentationTheory/DerivativeLiteratureHiggs.lean),
[helper](../local-lagrangian-helper/input-guide.md),
[common derivative input](../../../Math/RepresentationTheory/DerivativeInterface.lean),
[Weyl equations](../../../Physics/FieldTheory/Jets/WeylLinearEquation.lean),
[conjugate equations](../../../Physics/FieldTheory/Jets/ConjugateWeylEquation.lean),
and the actual scalar, gauge and spinor representations linked by these
sources. Final results must distinguish reused proofs, new certificates,
source inspection and remaining hypotheses.

## Additional Small-Sector Inspection

For the [additional four-part check](extended-checks.md), the primary PDF
text of 1507.07240v1 Eq. (3.11), PDF p. 13, and 1706.08520v1 Eq. (6.3),
PDF p. 58, and its representatives on p. 59 was reinspected. The expected
C1 sequences are (1,1,0)/(1,1,1), and C2 is (1,0,1). The new Lean C1
zero-derivative and bilinear d=2 results are independent proofs. Strengthened
exact scripts check surviving representatives as well as finite ranks;
remaining source/group bridges are still explicit. The PDF screenshot
retrieval failed, so this inspection uses the extracted primary PDF text.
No additional reference, paper completeness premise or software dependency
is introduced.

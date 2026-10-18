# Fixed One-N Source-Convention Inspection

## Outcome

One N and the u,d,s channel suffice for this inspection. Scalar conjugation
and the Majorana half are explicitly recoverable. The unique signed
four-component dictionary and selected-flavor vertex normalization are not
fully determined by the inspected sources. The existing conditional tree
comparison remains conditional; no extension to multiple N or other flavors
would supply those missing definitions automatically.

This is a source-inspection result, not a new Lean theorem or a complete
Hermitian-action matching certificate. The [tree-level proof](tree-level-results.md)
continues to apply to its declared action.

## Evidence and Dictionary

The arXiv v2 PDF was downloaded and rendered locally; pp.2–3 were inspected,
including a magnified Eq.(1). The v2 TeX archive member `arXv2.tex` independently
confirms the overline on chi and the literal 16 pi² in Eq.(4). The APS CHORUS
accepted manuscript has a cover page, so the corresponding locations are
pp.3–4. It retains these formulas. Sources and hashes are in the
[source register](references.md).

| Item | Source evidence | Recovered status and connection |
| --- | --- | --- |
| Scalar/conjugate scalar | Eq.(1) has N-transpose **chi-bar** u, followed by epsilon **chi** d d; TeX lines 122,124 | Explicit. The paired chi/chiBar placement of the supplied chiral action agrees with the printed placement. The overline was lost in earlier PDF text extraction; it is not an unspecified choice after visual/TeX inspection. |
| Majorana half | Eq.(1) has `(1/2) M_ab N_a^T C^{-1} N_b`; TeX line 121 | Explicit. One N retains the half. Existing `majorana_half` proves the local Grassmann reduction. The overall sign still depends on the C-inverse and action dictionary. |
| Lorentz contraction | Eq.(4) displays three C-inverse bilinears; Eq.(1) suppresses the spinor matrix in both quark vertices | The antisymmetric right-Weyl pairing is a compatible local completion. An explicit C matrix, its phase and the source-to-repository chirality convention are not specified. The repository adapter is an explicitly Euclidean convention, not a recovered source Minkowski dictionary. |
| Selected down coupling | Eq.(1) lists nonzero labels 12,13,23; no explicit summation range or down-vertex half is printed | An independent-pair interpretation is natural, but not uniquely certified. The same section also uses a 32 coupling in flavor bounds. TeX has no hidden sum restriction at the vertex. The already proved ds/sd sum identity distinguishes b = lambda-prime_12 from b = 2 lambda-prime_12. |
| Scalar mass / kinetic normalization | Eq.(3) uses inverse Mchi², Fig.1 supplies the scalar exchange route | Canonical propagation is a compatible conventional interpretation. No explicit chi kinetic term or fully normalized quadratic action is supplied in the inspected model description. Eq.(3) does not itself prove the chosen action dictionary. |
| Six-quark operator | Eq.(4) writes two color epsilons and literal uu/ds/ds bilinears, with no explicit factorial divisor | The printed local tensor/order is recoverable. Its identification with a canonically normalized Wilson-coefficient convention and with the old exterior-intertwiner polynomial remains a separate bridge. Existing `source_generator_order` fixes the local fermion-order minus sign only. |
| Printed scalar | Eq.(4), TeX line 166, and accepted manuscript Eq.(4) all contain inverse 16 pi²; Fig.1 and nearby text identify a tree route | Explicit and not a PDF text-extraction artifact. The inspected material provides no derivation of that factor from the stated tree route. This does not prove that no other explanation or author convention exists. |

Reading Eq.(3) as the coefficient of a single already normalized selected
N-u-d-s operator favors the local identification b = lambda-prime_12.
However Eq.(3) suppresses precisely the contractions and summation dictionary
under investigation. Using that equation as a normalization axiom would make
the resulting comparison conditional; it would not recover the premise.

## What the Remaining Choices Can Explain

The two ordered down-flavor entries without a half double the vertex, and
therefore multiply the tree coefficient by four. With the previously fixed
action/operator dictionary the two candidate ratios are 8 pi² and 32 pi².
These are alternative conditional readings, not a complete classification of
all source conventions. In particular, a signed source coefficient cannot be
declared recovered while the C-inverse/action phase dictionary is unresolved.

A consistent change of the bilinear normalization must be applied to the
mass, both vertices and the target operator together. Changing only the three
C-inverse factors in Eq.(4) is not a valid convention comparison. Ordinary
unit phases or the proved ds/sd factor do not supply a magnitude 1/(16 pi²).
This statement presumes the stated canonical field and bilinear interpretation;
it is not a theorem excluding arbitrary unpublished coupling redefinitions.

The accepted manuscript is a useful independent publication-stage check,
but is not the final publisher-typeset version. The arXiv record lists v1 and
v2; the bounded search did not locate a convention clarification or correction
for this factor. That is a search outcome, not certification that no correction
exists.

## Bounded Reference Check

The v2 paper cites Babu–Mohapatra–Nasri, arXiv:hep-ph/0612357v3,
Phys. Rev. Lett.98,161301 (2007), as Ref.[11] for the Nudd mechanism.
Sec.II Eq.(1) explicitly states antisymmetric lambda-prime couplings and a
Majorana half. Sec.V Eq.(14) gives an approximate inverse MN MX⁴ strength
without the same explicit inverse 16 pi². It does not specify an exact
matching dictionary for the Dev–Mohapatra Eq.(4) contraction or settle the
ordered-flavor half. It concerns a supersymmetric construction with additional
scalar structure. It is used only for citation provenance; no MSSM model
verification, transferred normalization or rate result is admitted here.

## Stop and Verification

The direct PDF/TeX inspection and bounded accepted-manuscript/reference check
are complete. Restoring a unique exact source dictionary stops at the missing
C-inverse/spinor, flavor-sum and kinetic/action definitions. No missing premise
was inserted into the Lean consumer. The recovered scalar placement and mass
half narrow the uncertainty, while the source's printed 16 pi² is confirmed
at both inspected publication stages.

Documentation only: local links and diff checks are required; no Lean rebuild
is needed because no declarations, proof hypotheses, imports or dependencies
changed. There is no new proof baseline, paper-error certification, multiple-N
extension, rate calculation, author contact, master merge or remote push.

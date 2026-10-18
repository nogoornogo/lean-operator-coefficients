# Sources and input contracts

Sources supply model conventions, not trusted completeness or stability premises.
The statements below are restricted to the independently defined Lean domains.

| Candidate | Pinned source/location | Frozen input and correspondence boundary |
| --- | --- | --- |
| Constructed parity SM | [existing construction](../inverse-cyclic-sm-construction/results.md) | Same explicit SM/spectator mass and parity dictionary; no new physical model |
| S3 | [fixed dictionary](../s3-yukawa-compatible-qque/results.md), [unequal controls](../sm-support-and-lfv-decomposition/sm-preserving-sample-results.md) | Selected physical qque with Q-pair statistics; no full B1/SUSY/UV lift |
| DFPW | [1304.0576v2](https://arxiv.org/abs/1304.0576v2), Table I, Sections II–IV, N=1; [earlier dictionary](../../model-studies/gauged-baryon-lepton/results.md) | Product cover b=6B,l=2L; VEVs (-18,-6),(0,-4); pure baryon element x=1/18 gives Z18 with physical q=2,l=0. Actual UV spectrum/quotient remains supplied |
| Split SU5 | [1706.08535v2](https://arxiv.org/abs/1706.08535v2), Eqs.(1),(4),(6),(7),(10),(15),(16),(22) | Original one-generation mass/light dictionary unchanged; three-generation consumer is conditional on three copies of that SM dictionary. Exact light parity is not asserted on the original mixing mass |
| Minimal PS | [2211.02054v2](https://arxiv.org/abs/2211.02054v2), Section II Eqs.(1),(2),(5),(10), Section III Eq.(19) | Original minimal variant only; gauge-only versus extra exact B; later normalization discrepancy remains separate |
| SU6 | [scalar/block result](../../model-studies/su6-protection/scalar-block-obstruction.md) | Fixed 15+bar6+bar6 benchmark and complete ScalarBlockQque.Input, no broader action/mass search |
| Minimal B-L | [1411.5042v2](https://arxiv.org/abs/1411.5042v2), introduction pp.1–3 discussing the conventional model | Three conventional right-handed neutrinos, singlet chi2 with B-L=2, neutral SM Higgs; select the conventional comparison, not the paper's alternative charges or S3 construction. X=3(B-L), charge-six VEV |
| Left-right | [1507.01584v3](https://arxiv.org/abs/1507.01584v3), Section II Eqs.(1)–(3), footnote 1 | qL/qR B-L=1/3, leptons -1; bidoublet charge zero, chiR charge -2 with neutral VEV. Only one specified SM Higgs/light projection; extra dark multiplets are excluded |
| Ma | [hep-ph/0601225v1](https://arxiv.org/abs/hep-ph/0601225v1), Eqs.(3)–(6),(11) | SM fields even, N and eta odd, eta has zero VEV. Restrict external alphabet to SM fields/Higgs; Eq.(11) loop map is not derived |
| B3/P6 | [hep-ph/0512163v2](https://arxiv.org/abs/hep-ph/0512163v2), Eqs.(2.17),(6.2), Section 9; [hep-ph/0610026v1](https://arxiv.org/abs/hep-ph/0610026v1), Section 2.2 and Section 5; [0708.0989v1](https://arxiv.org/abs/0708.0989v1), Section 2 Eq.(2.3), Table 1 | Non-R symmetries, n=0; B3 m=p=1; P6 m=5,p=2. Physical right-handed charges are negatives of conjugate chiral charges; invert the P6 generator to compare with BGW. Keep Hu and Hd-conjugate as a single explicitly supplied light doublet. Full FN parameter assignments, SUSY spectrum and threshold matching are not certified |

The B3/P6 model-realization papers are inspected for the residual-action
conditions; this pass does not choose or certify their complete FN parameter
space or spectrum. Their UV-to-single-Higgs projection is an unresolved model
input. Successful restricted certificates do not close that obligation.

For scalar cyclic tests the signed SM convention is physical Q,uR,dR,L,eR
and their opposites, with hypercharge 6Y and baryon grading 3B. The neutral
Higgs q/l consumers use the fixed three-generation ten-species SM dictionary.
The B3/P6 consumers explicitly retain a charged Higgs. No R symmetry or
superpotential dimension is identified with the component-field dimension.

## B-L / LR continuation scope

The same source versions and conventional variants are retained. Existing
[bidoublet source](../../../GUT/PatiSalam/Embeddings/PhiRepresentation.lean)
supplies the proved Hom(right,left) SM column decomposition; the continuation
constructs the LR group action explicitly and proves equality of its restriction.
The new quadratic-coordinate selection hypothesis is a formal theorem parameter,
not a claim extracted from either paper's potential. It is a sufficient
conditional selection, not a necessary classification of LR Higgs sectors.

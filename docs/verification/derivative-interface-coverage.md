# Derivative Interface Literature Coverage

Only the stated algebraic readings are checked. The original six-case
portfolio has five partial comparisons and one complete finite polynomial specialization, not
an analytic equivalence theorem. Source pins and equation/table locations
are fixed in the [source register](../topics/derivative-literature-comparison/references.md).
The [dossier](../proof/current/applications/Physics/DERIVATIVE_LITERATURE_CONTROLS.md)
owns hypotheses and proof structure; the topic owns the remaining gaps.

The [necessary-condition usage review](../topics/derivative-input-literature-review/review.md)
reinspects all six pins and maps them to actual support, relation and
restriction hypotheses. It adds no Lean proof coverage: C1–C5 remain partial,
and C6 retains its constructed polynomial scope. Worked C1/C3/C6 input tests
and the rejected C4 raw probe are distinguished from complete basis results.

The subsequent [proof-based recheck](../topics/derivative-literature-foundations/literature-recheck.md)
reinspects all six pins and tests the obtained foundations through persistent
Lean consumers. It adds exact real-parameter C3 quotient relations and C5
conserved-current EOM/IBP tests, and rejects the C4 raw separator on the new
represented input. These results strengthen the checked subsets; the
complete paper-basis targets remain distinct.

The [nonderivative input recheck](../topics/derivative-literature-foundations/nonderivative-recheck.md)
also supplies actual old Bose/Fermi/mixed and finite-local coefficients to
the integrated interface, with inverse and evaluation checks. Actual Lorentz
scalar nonderivative values and the global SM/Lorentz Higgs potential
selection are checked separately in full EOM inputs. The constructed
two-odd/five-even control inspired by Li Eqs. (4.20)–(4.21) tests statistics
with Unit symmetry; it is not a certified SM-operator dictionary or new
basis count. The six literature rows retain their stated partial boundaries.

The [additional four-part checks](../topics/derivative-literature-foundations/extended-checks.md)
add actual Lorentz Weyl old/new controls, presentation transport and supported
real-source checks. C1 now has complete actual d=0 images at every two-species
content and a zero complete (1,1), d=2 image. Finite diagnostics additionally
check explicit surviving representatives, including C2's K squared; remaining
source/group bridges are not imported. C1–C5 retain their partial boundaries.

The [finite scalar completeness follow-up](../topics/scalar-derivative-completeness/results.md)
completes the specified C1 counts through order 2 and the entire actual
Lorentz C2 order-two coefficient vanishing. At order four it proves K squared
nonzero in the full quotient and complete reduction of the three specified
metric contractions to its line. The [order-four successor](../topics/scalar-quartic-four-completeness/results.md)
proves K-squared evaluation is a linear equivalence on the entire selected
invariant coefficient space, with an explicit normalized inverse and
dimension one. The larger un-invariant quotient and the old fixed-wave
noninvariance control are retained. These results supersede only the
corresponding bounded gaps, not the paper-wide partial classifications.
The [renewed scalar literature comparison](../topics/scalar-quartic-four-completeness/literature-validation.md)
tests the new completeness theorem against the C2 count, Cao's normalized
chosen density and Lehman–Martin's low-order scalar examples.

The [C4 successor](../topics/higgs-quartic-four-completeness/results.md)
closes the whole-grade free Higgs coefficient target. Its three-source
[validation](../topics/higgs-quartic-four-completeness/literature-validation.md)
checks Murphy, Li's distinct higher-derivative densities and the new Eboli
comparison, retaining each paper's wider boundaries.

| Pinned source/location | Target | Verified claim | Conditions and limits | Evidence |
| --- | --- | --- | --- | --- |
| [1507.07240v1](https://arxiv.org/pdf/1507.07240v1), Section 3, Eq. (3.11) | One-dimensional free scalar EOM/IBP | Complete actual image/coefficient counts (1,1,0)/(1,1,1) for two-species contents (1,1)/(2,2) at orders 0,1,2; normalized global coefficients and inverse/evaluation laws in the positive sectors; complete d=0 images at every content | Complete for these bounded sectors; paper-wide comparison remains partial. No arbitrary positive-degree-content or full Hilbert-series theorem. | [Finite completeness](../topics/scalar-derivative-completeness/results.md#c1-source-reconstruction-and-independent-coefficients); [Lean](../../Math/RepresentationTheory/Coefficients/ScalarTwoSpeciesCompleteness.lean) |
| [1706.08520v1](https://arxiv.org/pdf/1706.08520v1), Section 6.1, Eq. (6.3), PDF pp. 58–59 | Four-scalar low-derivative sector | Complete d=0 image dimension 1, complete actual Lorentz d=2 coefficient dimension 0, and complete d=4 selected invariant coefficient equivalence with the complex numbers via K-squared evaluation; normalized inverse and extraction proved | Complete at these native bounded coefficient sectors. Full Euclidean/Lorentz bridge and arbitrary-degree series remain outside the claim. The un-invariant quotient is larger than the K-squared line. Python counts are supplementary. | [Order-four result](../topics/scalar-quartic-four-completeness/results.md); [finite certificate](../proof/current/applications/Physics/FINITE_DERIVATIVE_CERTIFICATES.md); [Lean](../../Physics/FieldTheory/Jets/Scalar/QuarticFour/ScalarQuarticFourCompleteness.lean) |
| [1008.4884v3](https://arxiv.org/pdf/1008.4884v3), Eqs. (2.1),(5.3), Table 2 | Gaugeless Higgs generated input and reduction | Paper-normalized real a=-m2, b=lambda density; exact full generated quotient and coefficient relation, with a criterion for omitting potential values; actual global SM/Lorentz input and inverse direct/generated maps | Specified input/relation proved; full-paper comparison remains partial. Complexified independent generators and proved conjugate-value real form; no complete Warsaw basis, actual-group finite five-candidate presentation, local gauge covariance or Yukawa restoration. | [Renewed C3](../topics/derivative-literature-foundations/literature-recheck.md#c3--paper-signs-and-full-generated-input); [foundation](../proof/current/inputs/Physics/HIGGS_LAGRANGIAN_INPUT.md); [Lean](../../Physics/FieldTheory/Jets/Scalar/Inputs/DerivativeLiteratureRecheck.lean) |
| [2005.00059v6](https://arxiv.org/pdf/2005.00059v6), Table 2 | Free Higgs four-derivative coefficient input | Evaluation on q1,q2,q3 is a linear equivalence on the entire actual grade (4,4) admitted invariant coefficient space, with normalized inverse, both inverse laws, dimension 3 and direct/generated agreement. | Complete native bounded coefficient comparison; full-paper coverage remains partial. Actual global covering-SM and Lorentz actions, full unbounded free EOM ideal and linear IBP. No local gauge/Yukawa completion or global invariant extension. | [C4 result](../topics/higgs-quartic-four-completeness/results.md); [validation](../topics/higgs-quartic-four-completeness/literature-validation.md); [Lean](../../Physics/FieldTheory/Jets/Higgs/QuarticFour/HiggsQuarticFourCompleteness.lean) |
| [2005.00008v3](https://arxiv.org/pdf/2005.00008v3), Eq. (4.8), PDF p. 31 | Native higher-derivative Higgs densities | Full free EOM/IBP gives values (4q3,q1,q2-q1-q3). Native-density evaluation is an equivalence for all selected invariant coefficients. | Complete native bounded coefficient dictionary. Independent formal field/dual generators and ordinary derivatives; no interacting SMEFT or amplitude count. | [C4 validation](../topics/higgs-quartic-four-completeness/literature-validation.md); [Lean](../../Physics/FieldTheory/Jets/Higgs/QuarticFour/HiggsQuarticFourLiterature.lean) |
| [1604.03555v1](https://arxiv.org/abs/1604.03555v1), Eq. (16), PDF p. 5 and footnote 2 | O_S,0/O_S,1/O_S,2 densities | Their order is (q2,q3,q1), giving complete selected-coefficient coordinates. Omitting O_S,2 misses a proved nonzero admitted coefficient. | Complete native bounded density comparison only; gauge-boson coupling formulas, nonlinear realization and numerical bounds are not checked. | [C4 validation](../topics/higgs-quartic-four-completeness/literature-validation.md); [Lean](../../Physics/FieldTheory/Jets/Higgs/QuarticFour/HiggsQuarticFourLiterature.lean) |
| [2005.00008v3](https://arxiv.org/pdf/2005.00008v3), Eq. (4.24), conversion (4.26); [Murphy v6 Table 5](https://arxiv.org/pdf/2005.00059v6) | One-flavor charged-lepton/Higgs current, free ordinary derivatives | Actual global SM/Lorentz mixed input combines both massless Weyl and free Higgs equations; full generated/component closure and coefficient transport, entire grade membership, Minkowski block/Pauli density equality and density invariance are proved. Conservation and symmetric-current redundancy hold. Whole-grade coefficient evaluation is a complex linear equivalence with ℂ: normalized inverse, both inverse laws, nonzero full-quotient support, dimension one and native Li/Murphy extraction are proved. | Fixed free one-flavor scope. The independent 56-variable matrix remains diagnostic; the complete proof instead uses whole-source tensors and an invariant Grassmann-wave functional killing every unbounded relation. No interacting or general-flavor SMEFT count. | [C5 result](../topics/weyl-higgs-current-completeness/results.md); [validation](../topics/weyl-higgs-current-completeness/literature-validation.md); [dossier](../proof/current/inputs/Physics/WEYL_HIGGS_CURRENT_INPUT.md); [Lean](../../Physics/FieldTheory/Jets/Weyl/Higgs/WeylHiggsCompleteLiterature.lean) |
| [0812.1594v6](https://arxiv.org/pdf/0812.1594v6), Appendix G.1 (G.1.62),(G.1.67),(G.1.82), footnote 127 | New independent Minkowski current convention check | Block gamma/projector current equality, (+---) Clifford law and raised anticommuting reversal sign are proved; independent exact Grassmann/matrix controls pass. | Convention validation only; no C5 basis count, physical dagger/real-form theorem or amplitude comparison. | [C5 validation](../topics/weyl-higgs-current-completeness/literature-validation.md); [Lean](../../Physics/FieldTheory/Spinor/Weyl/MinkowskiWeylCurrent.lean) |
| [1811.09413v2](https://arxiv.org/pdf/1811.09413v2), Section 3, Eq. (3.2) | Constructed quartic scalar local polynomial specialization | Helper/direct differential relations and inverse coefficient maps agree; actual substitution coefficients through order two, explicit first Euler/current and raw second-order nonzero control | Complete for the specified polynomial example. Not a verbatim paper example, analytic functional theorem, nonzero quotient claim or all-order field-redefinition equivalence. | [C6 result](../topics/derivative-literature-comparison/results.md#c6--proved-finite-polynomial-contract); [Lean](../../Physics/FieldTheory/Jets/Scalar/Inputs/DerivativeLiteratureScalar.lean) |

For the Grzadkowski row, the [nonderivative Higgs tests](../topics/derivative-literature-foundations/nonderivative-recheck.md#z5--nonderivative-higgs-input-selection)
add a stable rho squared/rho cubed selection with full-quotient image,
restriction/extraction and direct/generated agreement. These include
Table 2's Q_phi representative, with no two-coordinate independence claim.

The [verification record](../topics/derivative-literature-comparison/verification.md)
contains the original strict audits and full build. The
[foundation verification](../topics/derivative-literature-foundations/verification.md)
records the subsequent additions and their gates. No coverage
percentage, paper-wide certification or literature completeness premise is used.
The same record now includes the renewed six-case proof and diagnostic gate.
The [scalar successor gate](../topics/scalar-derivative-completeness/verification.md)
owns the new strict audits, full build and three exact diagnostics.

## Additional scalar validation

The [existing/new consumer verification](../topics/scalar-derivative-completeness/validation.md)
checks restriction, extraction, presentations and helper inputs. Its anisotropic
order-two class is nonzero in the full quotient although all admitted Lorentz
coefficients vanish there. The fixed-wave functional has the proved
noninvariance control, so no invariant extension is inferred. Four exact
diagnostics and the existing/new strict audits pass at that predecessor
checkpoint. The [complete-coefficient literature recheck](../topics/scalar-quartic-four-completeness/literature-validation.md)
supersedes its native order-four completeness stop: all selected coefficients
are determined by either K-squared evaluation or the paper-normalized Cao
combination. The Euclidean group bridge and conformal claims remain outside
the comparison.

| Source/location | Checked claim | Boundary and evidence |
| --- | --- | --- |
| [1510.00372v1](https://arxiv.org/pdf/1510.00372v1), Eq. (2.8), PDF pp. 9–10 | Four-field free-scalar order-two coefficient vanishing and order-four coefficient dimension one agree with the low-order scalar examples. The paper's displayed subtraction failure starts at six derivatives. | No general subtraction or SMEFT table certification. [Recheck](../topics/scalar-quartic-four-completeness/literature-validation.md#per-source-endpoints). |
| [2105.12742v3](https://arxiv.org/pdf/2105.12742v3), Eqs. (3.28)–(3.29), Eq. (A.20), PDF pp. 20,43 | The normalized combination has class (3/2)q(K squared). Its evaluation is an equivalence on all selected invariant coefficients; density values (a,b,c) are admitted uniquely exactly when b=-a and a=2c. | Complete native algebraic coefficient comparison in this sector; no conformal-primary, off-shell-basis or quantum theorem. [Lean](../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarQuarticLiteratureChecks.lean); [recheck](../topics/scalar-quartic-four-completeness/literature-validation.md). |


## Interacting Polynomial Input Comparisons

These rows compare source expressions under the all-order coefficient
transport. The all-order presentation does not imply a finite normal-form
algorithm or a source-wide operator count.

| Source/location | Verified comparison | Conditions and evidence |
| --- | --- | --- |
| Grzadkowski et al., [1008.4884v3](https://arxiv.org/pdf/1008.4884v3), Eqs. (2.1),(5.3), PDF pp. 3,9 | The signed Higgs potential/derivative relation holds after complete all-order coefficient reconstruction, with inverse transport. | Actual global SM-cover/Lorentz action; real mass/quartic parameters; gauge/Yukawa couplings zero. [Consumer and exact scope](../topics/interacting-lagrangian-classification/literature-validation.md). [Registered model entry](../topics/lagrangian-model-connections/literature-validation.md). |
| Criado–Pérez-Victoria, [1811.09413v2](https://arxiv.org/pdf/1811.09413v2), §3 Eq. (3.2), PDF p. 10 | The constructed quartic scalar first-order term vanishes for every admitted coordinate family; a nonzero second-order term is retained. The prescribed cubic value criterion remains g*c=0. | Constructed scalar specialization, full EOM/IBP and actual Lorentz action; no all-order field-redefinition or quantum equivalence. [Consumer and scope](../topics/interacting-lagrangian-classification/literature-validation.md). [Model API comparison](../topics/lagrangian-model-connections/literature-validation.md). |
| D. Tong, [QFT HTML §5.6](https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S5.html), Eq. (5.475), interaction part | Literal four-component scalar/fermion interaction, all nine left-Grassmann Euler components and inverse all-order coefficient transport. | Independent complex barred/unbarred labels; trivial group. Full kinetic and physical Lorentz dictionaries are not checked. [Component comparison](../topics/interacting-lagrangian-classification/literature-validation.md). |
| Dreiner–Haber–Martin, [0812.1594v6](https://arxiv.org/pdf/0812.1594v6), (2.21)–(2.22),(2.29),(2.38)–(2.39),(3.1.1),(3.2.1),(4.3.2) | Two-component contraction and kinetic dictionaries identify both the scalar/Weyl total density and its Euler family; full relation transport and Lorentz invariance are proved. | One species, complexified conjugate labels, specified scalar addition; no reality or quantum claim. [Comparison](../topics/lagrangian-model-connections/literature-validation.md); [Lean](../../Physics/FieldTheory/Jets/Lagrangian/LagrangianModelLiterature.lean); [field-coordinate/full-input connection](../topics/model-input-connections/literature-validation.md). |


The [graded Euler/Yukawa comparison](../topics/euler-naturality/literature-validation.md)
checks Sardanashvily (31),(37) in the polynomial evolutionary specialization
and recovers the retained DHM model through density invariance. No geometric
or whole-paper scope is added; build and artificial-control records stay in
the owning topic.

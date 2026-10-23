# Ordered C5 Literature Validation

The pinned primary PDFs in [references](references.md) were rechecked at
the specified displays. Li, Murphy and DHM were processed in that order.
The [completed native consumers](../../../Physics/FieldTheory/Jets/WeylHiggsCompleteLiterature.lean)
use the proved coefficient equivalence on the whole actual grade; paper
counts are not premises. The [earlier dictionary consumers](../../../Physics/FieldTheory/Jets/WeylHiggsLiterature.lean)
and independent exact diagnostics are retained.

| Source | Proved comparison | Exact boundary |
| --- | --- | --- |
| [Li et al. 2005.00008v3](https://arxiv.org/pdf/2005.00008v3), Eq. (4.24), PDF p. 34; conversion (4.26) | The one-flavor charged-lepton Pauli current, factor i, Higgs bidirectional derivative and norm give the native density. Its evaluation is now a complete scalar coordinate, with normalized value one, both inverse laws, nonzero full-quotient support and complex coefficient dimension one. | Free ordinary-derivative specialization, zero gauge/Yukawa couplings. No neighboring field/flavor rows, Hermitian real count or full SMEFT basis is certified. |
| [Murphy 2005.00059v6](https://arxiv.org/pdf/2005.00059v6), Table 5, PDF p. 23 (printed p. 22) | The right-chiral gamma/projector density equals Li's ordered density in the actual algebra. Native extraction, both inverse laws and normalized value one hold for all admitted selected coefficients and commute with generated/component transport. | Formal barred components are independent. No physical dagger, interacting EOM, arbitrary flavors or paper-wide dimension-eight count. |
| [Dreiner–Haber–Martin 0812.1594v6](https://arxiv.org/pdf/0812.1594v6), Appendix G.1, (G.1.62),(G.1.67),(G.1.82), PDF pp. 203,205; footnote 127 | The block/projector identity, (+---) Clifford law and raised anticommuting reversal minus agree. The admitted normalized coefficient evaluates the unsigned reversed density to −1, versus +1 on the native density. | An independent convention check, not an independent C5 basis classification, star/real-form theorem or amplitude result. |

The accepted normalization has no discrepancy within these readings.
The free/global model is explicitly specialized before comparison. A basis
entry with covariant derivatives in an interacting SMEFT is not asserted
equal to this entire free theory without that specialization.

## Controls and independent diagnostics

The completed Lean consumers detect a doubled native Li factor by values
2 versus 1 and a missing reversal minus by −1 versus 1. Both controls use
an admitted full-relation coefficient, rather than a raw component probe.
The candidate is nonzero in the full quotient. Li/Murphy normalization and
the selected generated-input values all equal one.

The standard-library exact script
`python3 tools/derivative-literature/check-weyl-higgs-literature.py`
uses Gaussian rationals, explicit gamma/projector matrices and an exterior
algebra on eight independent odd components. Li and Murphy each pass eight
nontrivial rational Higgs/first-jet configurations. Four chiral components,
16 Clifford pairs and four raised-reversal signs pass. Doubling Li's
factor produces a local discrepancy, after which Murphy and DHM still run
and pass. The wrong Grassmann sign is detected. All three entries were
processed, independently of the status of a preceding comparison.

Separately,
`python3 tools/derivative-literature/check-weyl-higgs-finite.py`
rechecks 4160 ordered monomials, 896 hypercharge-zero and 56 Cartan-zero
coordinates. All 216 row residuals vanish; cumulative ranks are 52,54,55.
Omitting Weyl equations leaves three diagnostic coordinates; omitting IBP
leaves two. The symmetric current vanishes and the bidirectional candidate
has value 24 (factor i omitted in this diagnostic normalization).

These scripts are independent diagnostics, not Lean premises. The full
theorem uses the alternative [proved route](results.md): whole-source
invariant tensors for the upper bound, full unbounded relations and an
invariant Grassmann-wave sum for the lower witness. It does not claim a
complete relation-preimage identification for the diagnostic row matrix.

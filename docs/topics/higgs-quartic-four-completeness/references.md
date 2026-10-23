# Sources and comparison queue

Sources guide finite comparisons; no imported operator count is a Lean
premise. Version pins, precise locations and final dictionaries are retained
here. Each entry receives its own outcome before the next entry proceeds.

1. Existing C4: C. W. Murphy, *Dimension-8 Operators in the Standard Model
   Effective Field Theory*, [2005.00059v6](https://arxiv.org/pdf/2005.00059v6),
   Section 4.1, Table 2, PDF p. 20. The three H4D4 contractions are compared
   in their free, gaugeless ordinary-derivative specialization. The existing
   q1,q2,q3 ordering is the proved native dictionary, with whole-grade
   coefficient extraction and an explicit inverse.
   Full SMEFT EOM, gauge-field operators and phenomenology are not included.
2. Existing portfolio source, new C4 comparison: H.-L. Li et al., *Complete
   Set of Dimension-8 Operators in the Standard Model Effective Field Theory*,
   [2005.00008v3](https://arxiv.org/pdf/2005.00008v3), Section 4.2's pure-Higgs
   four-derivative class, Eq. (4.8), PDF p. 31. Its higher-derivative density
   presentation differs from Murphy's. Lean proves the native map
   (4q3,q1,q2-q1-q3) through the full free EOM/IBP relations and the actual
   selected input. The independent exact diagnostic agrees.
   No full-paper count,
   flavor classification or general amplitude dictionary is imported.
3. New source: O. J. P. Eboli and M. C. Gonzalez-Garcia, *Mapping the genuine
   bosonic quartic couplings*, [1604.03555v1](https://arxiv.org/abs/1604.03555v1).
   Section III.A, Eq. (16), PDF p. 5, and footnote 2. The served PDF identifies
   itself as v1; the versioned retrieval returned a cache miss. Its local
   density ordering is (q2,q3,q1). Footnote 2 explicitly includes O_S,2
   relative to the cited earlier conventions. Scattering/coupling bounds and
   nonlinear-realization claims remain outside this check.

The existing [field dictionary](../../../Physics/FieldTheory/Jets/HiggsFieldDictionary.lean),
[actual input](../../../Physics/FieldTheory/Jets/HiggsStandardInput.lean),
[paired contractions](../../../Math/RepresentationTheory/PairedJetContractions.lean),
[Lorentz controls](../../../Physics/FieldTheory/Jets/LorentzRankFour.lean),
[scalar complete coefficients](../../../Physics/FieldTheory/Jets/ScalarQuarticFourCompleteness.lean)
and [previous C4 boundary](../derivative-literature-foundations/finite-certificates.md#c4--independent-partial-stop)
are local proof inputs, retaining their own assumptions. The source papers
must not be used to fill an unproved invariant span or relation-annihilation
condition in these interfaces.

# Sources And Roles

- Henning, Lu, Melia and Murayama,
  [1507.07240v1](https://arxiv.org/pdf/1507.07240v1), Eq. (3.11), PDF p. 13.
  Target C1 finite counts: (1,1,0)/(1,1,1) at contents (1,1)/(2,2), orders
  0,1,2. Guidance and comparison only; no series/completeness premise.
- Henning, Lu, Melia and Murayama,
  [1706.08520v1](https://arxiv.org/pdf/1706.08520v1), Eq. (6.3), PDF p. 58,
  with representatives on p. 59. Target C2 coefficients (1,0,1) at four
  identical scalar fields and derivative orders 0,2,4. The repository has
  Lorentz (+---) conventions. The completed native Lorentz order-two result
  and order-four nonzero class are compared at that scope; a complete
  Euclidean SO(4)/O(4) to Lorentz coefficient-space equivalence is not claimed.
- The pinned primary PDF text was reinspected at Eq. (3.11), PDF p. 13,
  and Eq. (6.3) and its representatives, PDF pp. 58–59. It agrees with the
  finite expected counts above. The
  [predecessor register](../derivative-literature-foundations/references.md)
  preserves the earlier inspections.
- Lehman and Martin, [1510.00372v1](https://arxiv.org/pdf/1510.00372v1),
  Eq. (2.8), PDF p. 9, and the subtraction discussion on pp. 9–10.
  Existing survey source, now used for the four-field free-scalar
  order-two comparison. No higher-derivative subtraction or SMEFT count
  is certified by this test.
- Cao, Herzog, Melia and Roosmale Nepveu,
  [2105.12742v3](https://arxiv.org/pdf/2105.12742v3), Eqs. (3.28)–(3.29),
  PDF p. 20; dot-product and distinct-permutation conventions in Sec. 3.1,
  PDF pp. 13–15. New source for the normalized three-density algebraic
  comparison in [validation](validation.md). Conformal, quantum and
  renormalization results are outside the comparison.

Existing local foundations: [two-species source](../../../Math/RepresentationTheory/TwoSpeciesDerivativeChecks.lean),
[finite certificate](../../../Math/RepresentationTheory/FiniteDerivativeCertificate.lean),
[actual scalar controls](../../../Physics/FieldTheory/Jets/DerivativeLiteratureScalar.lean),
[direction/EOM dossier](../../proof/current/core/Math/DIRECTIONAL_JET_EOM_IBP.md)
and [finite certificate dossier](../../proof/current/applications/Physics/FINITE_DERIVATIVE_CERTIFICATES.md).

Retained [C1](../../../tools/derivative-literature/check-one-dimensional.py)
and [C2](../../../tools/derivative-literature/check-scalar-lorentz.py) exact
diagnostics guide expected representatives and finite ranks. The additional
[actual finite-group diagnostic](../../../tools/derivative-literature/check-scalar-group.py)
uses the matrices independently proved in `LorentzFiniteControls`. None of
these Python results is a Lean premise. The final scope is reconciled in the
[bibliography](../../proof/RELATED_LITERATURE.md). The additional scalar
reference supplies no proof premise or dependency.

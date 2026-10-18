# Literature And Repository Source Register

Recorded: stage 01. Sources guide proposed formalization; none is currently
an admitted external theorem premise. Inspection is not Lean verification.
The initial search used: all-order accidental symmetries, non-derivative
interactions, invariant rings, covariants, generic stabilizer, spurion
saturation, baryon/lepton number selection rules, and flavor symmetries.

## R1 — All-Order Accidental Symmetries

B. Grinstein, X. Lu, C. Miró, P. Quílez, *Accidental symmetries, Hilbert series,
and friends*, JHEP 03 (2025) 172.

- [Pinned preprint: arXiv:2412.05359v1](https://arxiv.org/abs/2412.05359v1).
- [Publication DOI](https://doi.org/10.1007/JHEP03(2025)172).
- [Published full text inspected](https://escholarship.org/content/qt1t19h386/qt1t19h386_noSplash_993f2e81391bf4798f8679692cb42df3.pdf).
- Locations: Sec. 2 (non-derivative all-order examples); Sec. 4.1, Eq. (4.18)
  (friendship); Sec. 4.2, Eq. (4.24) (all-order criterion); Sec. 4.3,
  Eqs. (4.71)–(4.72) (finite-order criterion); Eqs. (4.30), (4.32)
  (occurrence and generic-stabilizer criterion).
- Intended use: invariant-space comparison and later bosonic structural tests.
- Conditions/limits: Sec. 4.2 uses bosonic building blocks and a generic
  stabilizer. The explicit “Caveat: fermionic case” after the proof of
  Eq. (4.24) says the proof is not guaranteed for Grassmann-odd fields.
- Status: principal criterion and caveat inspected; complete hypothesis
  dictionary and Lean bridge unverified. Publication and preprint pagination
  differ; use the published equation locations above for implementation.

## R2 — Spurion Saturation And MLFV

B. Grinstein, X. Lu, C. Miró, P. Quílez, *Most general EFTs from spurion analysis:
Hilbert series and minimal lepton flavor violation*, JHEP 07 (2025) 259.

- [Pinned preprint: arXiv:2412.16285v1](https://arxiv.org/abs/2412.16285v1).
- [Inspected preprint full text](https://arxiv.org/html/2412.16285v1).
- [Publication](https://doi.org/10.1007/JHEP07(2025)259).
- Locations in inspected preprint: Sec. 2.2, Eqs. (2.4), (2.6), (2.8);
  Sec. 3 (MLFV scenarios); Sec. 4, Eqs. (4.1)–(4.2).
- Intended use: covariant evaluation into the invariant space of the actual
  residual stabilizer, and the distinction between flavor and total L.
- Conditions/limits: arbitrary spurion powers, generic values, and the
  underlying covariant theorem hypotheses. Conjugate spurions are included
  in the listed flavor examples. Special values and finite spurion-degree
  truncations require separate analysis. The result describes allowed
  coefficients, not UV-generated coefficients.
- Status: theorem argument and exceptional-value discussion inspected;
  published numbering/convention comparison and generic evaluation
  surjectivity bridge still require audit before implementation.
- Ancillary [HilbCalc](https://github.com/HilbertSeries/Group_Invariants_and_Covariants)
  is a Mathematica diagnostic lead only; not executed, not a Lean library or
  proof premise, and no Mathematica dependency is planned.

## R3 — Covariant Modules And Rank Saturation

B. Grinstein, X. Lu, L. Merlo, P. Quílez, *Hilbert series for covariants and
 their applications to minimal flavor violation*, JHEP 06 (2024) 154.

- [Pinned original preprint: arXiv:2312.13349v1](https://arxiv.org/abs/2312.13349v1).
- [Publication](https://doi.org/10.1007/JHEP06(2024)154).
- [Erratum: JHEP 03 (2025) 072](https://doi.org/10.1007/JHEP03(2025)072).
- Locations: covariant-module/rank discussion and MFV saturation argument;
  the Erratum corrects Eqs. (2.113c)–(2.113d) and deletes the discussion
  of powers of secondary invariants following Eq. (2.15).
- Intended use: organize covariants as modules over invariant rings and
  understand the mathematical input to R1/R2.
- Status: module discussion inspected and Erratum existence verified.
  The [Erratum full text](https://link.springer.com/content/pdf/10.1007/JHEP03(2025)072.pdf)
  was read in the feasibility pass; its claim that conclusions are unaffected
  is an author statement, not an independent certificate. Complete corrected
  theorem assumptions remain unaudited. No corrected formula is a proof premise.
- Limit: rank over an invariant ring is not automatically the dimension of
  the evaluation image at every specified value.

## R4 — Mathematical Original

M. Brion, *Sur les modules de covariants*, Annales scientifiques de l'École
Normale Supérieure, série 4, 26 (1993), no. 1, pp. 1–21.

- [Stable publication and metadata](https://numdam.org/articles/10.24033/asens.1665/).
- [Inspected original PDF](https://www.numdam.org/article/ASENS_1993_4_26_1_1_0.pdf).
- Locations: Sec. 1.1 setup; Sec. 1.2 corollary, printed p. 4: for a generic
  closed orbit G/H, covariant-module rank equals the dimension of M^H.
- Intended use: audit R1/R2's cited mathematical premise at its original source.
- Conditions/limits: reductive group actions and finite-type algebraic
  hypotheses; stronger than the repository's arbitrary abstract-group layer.
- Status: setup and the cited corollary inspected. Its reductive rational,
  finite-type, irreducible-variety and generic closed-orbit hypotheses are
  recorded in [feasibility](feasibility.md). No existing Lean bridge was
  identified in the bounded pass; no general rank theorem is claimed.

## R5 — B/L/Dimension Selection

A. Kobach, *Baryon Number, Lepton Number, and Operator Dimension in the Standard
Model*, Physics Letters B 758 (2016), pp. 455–457.

- [Pinned preprint: arXiv:1604.05726v1](https://arxiv.org/abs/1604.05726v1).
- [Publication](https://doi.org/10.1016/j.physletb.2016.05.050).
- Target: parity relation between operator dimension and (Delta B–Delta L)/2.
- Intended use: exact all-degree support restrictions in an admitted SM
  dictionary, not a complete arbitrary-model protection theorem.
- Status: main result and counting argument consulted; signed-charge and
  engineering-weight correspondence to Lean remains unverified.

## R6 — Flavor-Strengthened B/L Selection

A. Helset, A. Kobach, *Baryon number, lepton number, and operator dimension in
 the SMEFT with flavor symmetries*, Physics Letters B 800 (2020), 135132.

- [Pinned preprint: arXiv:1909.05853v1](https://arxiv.org/abs/1909.05853v1).
- [Publication](https://doi.org/10.1016/j.physletb.2019.135132).
- Locations: flavor-representation selection argument and Weinberg exception.
- Intended use: distinguish bounded suppression from all-degree protection
  and make flavor-representation assumptions explicit.
- Status: relevant argument consulted; generation, spurion and representation
  dictionary not admitted as a Lean comparison.

## R7 — Secondary Discrete-Symmetry Lead

H. K. Dreiner, C. Luhn, M. Thormeier, *What is the Discrete Gauge Symmetry of
 the MSSM?*, Physical Review D 73 (2006), 075007.

- [Pinned preprint: hep-ph/0512163v1](https://arxiv.org/abs/hep-ph/0512163v1).
- [Publication](https://doi.org/10.1103/PhysRevD.73.075007).
- Intended use: possible finite-cyclic selection controls, not a premise for
  the generic mixed-statistics theorem.
- Status: abstract/search lead only. MSSM superpotential and anomaly
  assumptions cannot be imported into the present SM coefficient scope.

## Existing Repository Prerequisites

- [Graded completeness dossier](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md)
  and [source](../../../Math/RepresentationTheory/GradedMixedCompleteness.lean):
  selectedEquiv, selected_forbidden_iff, allEquiv, all_forbidden_iff,
  all_nonzero_iff, all_bounds_forbidden_iff.
- [Naturality dossier](../../proof/current/core/Math/GRADED_COMPLETENESS_NATURALITY.md),
  [restriction](../../../Math/RepresentationTheory/GradedCompletenessRestriction.lean),
  [all-degree restriction](../../../Math/RepresentationTheory/GradedCompletenessAllRestriction.lean):
  independent quotient transport and subgroup injectivity/monotonicity.
- [Content grading](../../../Math/RepresentationTheory/MixedContentGrading.lean)
  and [separated Hom](../../../Math/RepresentationTheory/TypedMixedSeparatedHom.lean):
  support, local coinvariants and statistics relations.
- [Earlier selection topic](../residual-selection-criteria/README.md):
  bounded concrete controls, not all-degree protection.
- [Dipole results](../clfv-dipole-completeness/results.md):
  specified flavor selectors versus full nonzero Hom and UV generation.

Repository records/source signatures were inspected at the recorded base.
That initial inspection was planning-only. The new algebraic results and their
46 strict transitive checks are recorded in [results](results.md) and
[verification](verification.md). See [interfaces](interfaces.md) for the
implemented source dictionary. R1/R2 motivated the direction but their general
geometric conclusions are not certified by these proofs. No literature
coverage certificate is added for a theorem whose semantic bridge remains open.

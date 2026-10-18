# Proof Dossier Reference Review

Reviewed: stage 01. This is a bibliographic and attribution review of the
69 Math/Physics/GUT dossiers current at that checkpoint, not a new proof verification baseline.
Historical plans and logs preserve their dated outcomes and are not promoted
to current theorem dossiers. Repository document links are supplementary
context; Lean source/audit links identify implementation evidence.

## Current coefficient and selection-rule literature

The [related-literature map](RELATED_LITERATURE.md) connects the 19 supplied
references to current result guides and dossiers. Publisher/arXiv records,
abstracts and book contents establish identity and subject relevance; they do
not constitute full-text or semantic bridge audits. The Grinstein published
fermionic caveat was checked directly; existing Li/Heeck–Le and model ledgers
remain authoritative only for their selected comparisons.

Kobach and Helset–Kobach arXiv histories expose v1; the existing source register's
v2 labels were corrected to v1 without changing a formal result or claiming
its previously unverified dictionary bridge. Background references add no
external theorem inputs and support no novelty or priority claim.

## External Theorem Input

- [Raghunathan lecture notes, Proposition 38, PDF page 37](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=37):
  checked the stated maximal-torus surjectivity and its derivation from
  Proposition 37 and the quotient fibration. The notes explicitly caution that
  the lecturer did not proofread the typed text. The E6 application uses only
  surjectivity, not the full kernel assertion. Its reparametrized Lean premise
  and application conditions remain explicit in
  [E6 literature boundary](current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).

## Mathematical Interpretation And Proof-Route References

- [Etingof, Lie Groups and Lie Algebras, Theorem 9.12 and Corollary 9.14, PDF page 56](https://ocw.mit.edu/courses/18-755-lie-groups-and-lie-algebras-ii-spring-2024/mit18_755_s24_lec_full.pdf#page=56):
  checked the simply-connected Lie correspondence. The named compact-E6
  interpretation also refers to the real-form and compact-group classification
  chapters; it is not a Lean equivalence to an independently defined E6 group.
- [Raghunathan, PDF pages 34–38](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=34)
  and [Conrad, Size of fundamental group, Section 3, PDF page 4](https://math.stanford.edu/~conrad/210CPage/handouts/pi1size.pdf#page=4):
  checked the regular-locus/covering route used in the
  [torus-surjectivity map](../topics/e6-global-topology/decisions/E6_TORUS_SURJECTIVITY_MAP.md).
  These describe a considered construction route, not a formal proof of the
  general topology premise. Conrad's Proposition 3.1 gives the regular-locus
  covering statement.
- [Evans, Topology of Lie groups](https://jde27.uk/lgla/16_topology_accessible.html):
  checked the sphere-fibration induction for special unitary groups.
  This is a proof-route reference for the
  [Spin standard-chain dossier](current/applications/GUT/SPIN_STANDARD_CHAIN.md), not an additional
  assumed Lean theorem.
- [Alonso et al., arXiv:1405.0486, Section III.B](https://arxiv.org/html/1405.0486#S3.SS2):
  the HTML labels this subsection III.2, “Grand Unified Theories”. Checked the
  common SU(5) flavor transformations and operator transformation discussion.
  The [Georgi–Glashow dossier](current/applications/GUT/GEORGI_GLASHOW_QQUE.md) uses it as context
  for the flavor-singlet observation, not as a premise or a novelty claim.
  Its RGE and numerical conclusions are not imported into the formal endpoint.

## Feasibility Context, Not Proof Inputs

The [E6 feasibility dossier](../topics/e6-global-topology/decisions/E6_FEASIBILITY.md) cites the following as
construction/comparison possibilities. Checking them does not certify an
implemented equivalence or change the dossier's historical decision.

- [Britto, arXiv:2102.13465v1, Chapter 3](https://arxiv.org/html/2102.13465v1):
  checked the E6 construction and Spin(10) extension chapter. This is a
  mathematical construction reference, not a formalized global identification.
- [Bernardoni et al., arXiv:0710.0356](https://arxiv.org/abs/0710.0356):
  checked bibliographic metadata and the abstract's compact-E6 parametrization
  description. No detailed proof or page-level dependency is claimed here.
- [SageMath branching documentation](https://doc.sagemath.org/html/en/thematic_tutorials/lie/branching_rules.html)
  and [GAP/SLA, Chapter 6](https://gap-packages.github.io/sla/doc/chap6.html):
  checked the documented branching/subalgebra interfaces. These are potential
  computational comparison tools, not proof certificates.
- [Chirality project repository](https://github.com/emad-ii/chirality-standard-model):
  checked the public project description only. This is related work; its code,
  proofs and license compatibility are not certified by this review.

## Attribution And Verification Limits

The cited explanations above are paraphrases, not verbatim quotations. No new
quotation, author attribution or page number is inferred for uncited legacy
mathematical prose. Such prose remains the repository's proof explanation,
not a claim that an external paper proves its Lean statements.

Local links and numbered dossier structure are checked in the documentation
pass. The earlier recorded builds and axiom audits are not rerun. In particular,
checking a reference does not prove an external premise, and checking a link
does not establish the correctness of a theorem's implementation.

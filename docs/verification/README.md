# Literature Verification Coverage

This directory indexes comparisons between external literature and this
project's formal results across topics. It is neither a proof dossier nor a
work queue. See the [Li basis coverage ledger](li-basis-coverage.md) and
[Heeck–Le existing-sector ledger](heeck-le-coverage.md), and the
[proton protection model ledger](proton-protection-model-coverage.md), and
[Weyl extraction input ledger](weyl-extraction-coverage.md), and
[structural exterior-support ledger](structural-exterior-support-coverage.md).
The [derivative interface ledger](derivative-interface-coverage.md) records
bounded scalar, component-polynomial and mixed-sign comparisons, including
their partial physical-dictionary and basis boundaries.

## Findings across comparisons

The [scoped findings summary](literature-findings.md) explains three distinct
outcomes: a printed-list flavor boundary, a fixed-reading normalization
comparison and a conditional coefficient comparison. Each has explicit source
conventions, proof links and limits. The summary indexes existing evidence;
it adds no new source-to-Lean certificate.

## Source View and Model View

The organizing unit here is a **source location and its formal comparison**.
An entry answers: which expression, candidate basis or stated claim has been
compared with a formal result, using which input conventions and limitations?
The source may describe a physical model, an operator basis or a mathematical
construction. A coverage entry is not itself a whole-paper certification.

[Model studies](../model-studies/README.md) instead organize the explanation
around a **concrete model or constructed input**: its fields and actions,
what follows, and which model premises remain unverified. Those studies include
project-constructed examples without a direct literature comparison. Such an
example does not need a coverage row merely because it has been tested.

For example, the [B-L study](../model-studies/minimal-bl/README.md) explains the
model input and its residual-action result, while the
[model coverage ledger](proton-protection-model-coverage.md) indexes the source
locations and bounded certificates. The [Li ledger](li-basis-coverage.md) can
index basis comparisons without a separate model study. A
[constructed S3 study](../model-studies/s3-flavor-qque/README.md) needs a row here
only when an external source is actually compared.

These are complementary views. Link the ledger to the model explanation and
proof evidence; keep each source-to-result row short rather than duplicating
the model narrative. Model studies do not replace coverage maintenance for
work that compares a specific literature source.

## Reading A Ledger

Each row identifies a pinned source and location, the comparison target,
the verified claim, its conditions and limits, and links to evidence.
“Verified” means a Lean theorem about an explicit algebraic interpretation
and an independently defined coefficient sector. It does not automatically
certify amplitude conventions, software output, other paper versions or the
whole paper. PDF page numbers are not journal page numbers.

Candidate expressions may come from literature without assuming their
completeness as an axiom. Any actual external theorem premise must instead
be identified explicitly in the dossier and assumptions ledger.

## Authoritative Records And Maintenance

- Model studies own reader-facing model inputs, outcomes and unresolved model premises.
- Proof dossiers own statements, hypotheses, conventions and proof structure.
- Topics own investigations, unresolved comparisons, verification commands,
  checkpoint results and integration status.
- Assumptions ledgers own verified inputs and applicability boundaries.
- Coverage ledgers own only the cross-topic source-to-result index.

For work involving a literature comparison, update the relevant row at a
verified milestone, a hypothesis/convention change or a source correction.
At completion, check it against the dossier and actual theorem statement.
Link to build records; do not duplicate job counts or chronological logs.
General theorems without a literature comparison need not have a row.

Keep these documents in English. Substantial pending investigations belong
in a topic, not in an ever-growing coverage table. Maintaining this index
does not authorize a new proof topic, dependency change or scope expansion.
See the [workflow](../architecture/WORKFLOW.md).

## Evidence And Publication Claims

Lean proofs establish the stated formal claims. Transitive axiom audits check
dependencies, not the physical adequacy of a field dictionary. Exact external
scripts and negative controls supplement proofs within their recorded domains;
they are not trusted proof premises. Rebuilding the same definitions checks
reproducibility, not an independent physical interpretation. External review
does not turn an unproved mathematical decomposition into a proved result.

A suitable publication claim is: “We machine-checked explicit algebraic
interpretations of specified derivative-free literature candidates against
independently defined invariant coefficient sectors, under the listed inputs
and conventions.” Do not replace this with “the paper/software was verified.”

State counterexamples with their exact source version, conventions, sector
and multiplicity assumptions. A deficient printed list does not by itself
establish an error in a paper-wide counting polynomial or every residual model.

No completeness percentage is meaningful until a source-wide inventory defines
the denominator. The current ledger indexes selected results only. This
directory creates no obligation to implement derivatives, EOM/IBP, matching,
RGE or other excluded foundations.

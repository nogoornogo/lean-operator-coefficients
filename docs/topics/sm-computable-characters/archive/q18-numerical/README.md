# Retired Q18 numerical certificate sources

The user approved replacing the exact Q18 multiplicity/rank statements by
zero/nonzero support statements at stage 01. These UTF-8 source snapshots
preserve the preceding implementation at commit `checkpoint 01`. They are text
records, not active Lean modules or inputs to the new proof.

The numerical checkpoint `checkpoint 02` had verified the 48 coefficient equalities
in twelve chained modules and their Q18 assembly. The prior commands, budgets
and outcomes remain in [kernel verification](../../kernel-verification.md).
That historical verification is not a new verification of these archived
sources, nor does the structural replacement rederive the old numbers.

- [Q18 assembly](Q18.lean.txt)
- The twelve `Q18Part0.lean.txt` through `Q18Part11.lean.txt` snapshots
- [Old numerical consumers](SMNeutralSparseExamples.lean.txt)
- [Old sparse audit](AuditSMSparseCharacter.lean.txt)
- [Source paths, commits and SHA-256 hashes](manifest.json)

The consumer/audit snapshots also contain other examples to preserve their
original context. Those other active examples retain their statements.
Only Q18's numerical declarations and active imports were retired; current
structural consumers and their strict audits are described in
[Q18 support results](../../q18-support-results.md).

At the later user-directed retirement, the other numerical example modules
were also removed from builds; see their
[separate source snapshots](../remaining-numerical/README.md). The paragraphs
above describe this Q18 archive's original checkpoint.

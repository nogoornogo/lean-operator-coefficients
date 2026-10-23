# Verification

Focused proof and source comparisons pass. Source-owned strict transitive axiom
audits cover every declaration in the new implementation modules and accept
only propext, Classical.choice and Quot.sound. Math imports reject Physics/GUT;
Physics imports reject GUT. No audit exception or dependency change is used.

The focused audit build passes 3,980 jobs. Its source-owned inventories check
310 mathematical declarations and 9 physical declarations transitively, for
319 checks. The aggregate full build passes 8,041 jobs. New-source warnings
are advisory legacy/module-system import notices; inherited repository lint
warnings remain. All Lean commands use default elaboration limits, two threads, a
16 GiB address-space cap and a 540-second wall-clock guard. Logs stay outside
source control.

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditEulerNaturality Physics.FieldTheory.Jets.Audit.AuditEulerNaturality
LEAN_NUM_THREADS=2 lake build
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

The guide snippet is compiled as a disposable Lean file. Literature and
artificial statements are included by strict audits. Existing direct/generated
input definitions, dependency pins and audit allowlists are unchanged.


Layout passes 2,544 modules. Navigation covers 168 topics and their outcomes.
Metadata checks 1,279 portable documents/evidence files. Link validation checks
1,287 Markdown files, 8,312 local links and 156 fragments with zero errors.
The guide compiles with its explicit noncomputable section; the diff whitespace
check passes. The unchanged link checker was rerun with Git subprocess access
after a sandbox EPERM; no checker or acceptance rule was changed.

The previous child topic was integrated into its non-master parent with a
no-fast-forward merge. Its merged-state full build passed 8,027 jobs, including
its strict audits, before its local branch was deleted. Euler naturality is now integrated into its recorded parent, and the series
is integrated into master.
[Master integration verification](../interacting-lagrangian-classification/integration-verification.md)
records the merged-state checks. No remote mutation is performed.

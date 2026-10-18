# Verification And Scope

The frozen bounded endpoint is reached: the three previous model dictionaries
have explicit shared-constituent admission/obstruction and original-mass
compatibility decisions. No new Lean source is added. The parent commit
`checkpoint 01` owns the general proof's full build (6625 jobs) and 31 strict audits;
this application pass does not invent another Lean baseline.

Checks:

- `python3 tools/species-surplus-model-checks/audit_models.py`: passed, five
  exact controls; full split gauge labels/counts, all 729 small rectangular
  matrices, full/light parity, PS charged/neutral separation and all 27 small
  neutral symmetric matrices, B/L charged exotic weights.
- `python3 tools/species-copy-surplus/audit_controls.py`: passed, six controls.
- `python3 tools/proton-protection-model-checks/audit_models.py`: passed,
  seven controls, preserving earlier model checks.
- `node tools/docs/check-links.mjs`: passed, 584 Markdown files, 3719 local
  links, 88 heading fragments, zero errors. The read-only checker was rerun
  outside the sandbox after its git subprocess encountered `EPERM`.
- `git diff --check`: passed.
- No Lean build was rerun: changes are documentation and supplemental exact
  controls; existing theorem statements and dependency content are unchanged.

Pinned original sources were reopened: [B/L v2 HTML](https://arxiv.org/html/1304.0576v2),
[split SU5 v2 PDF](https://arxiv.org/pdf/1706.08535v2),
and [PS v2 PDF](https://arxiv.org/pdf/2211.02054v2). The B/L v2 PDF endpoint
returned an access error; its versioned HTML contains the needed Table I and
Eqs.(11),(12). No newer variant replaces the frozen source.

The initial script's full split dimension expectation was corrected from 315
to 375: 5+10+4×40+4×50=375. This was an arithmetic expectation error, not a
changed supplied branching. Full-label/count regression remains in the script.
The B/L model note now distinguishes SM-selected charged fields from full
SM-gauge-equivalent exotic copies. No preceding Lean charge dictionary changes.

The new applications are documented conditional algebraic deductions, not new
Lean proofs of literature branching, copy Hom counts or all NoPairings inputs.
The generic implication is formalized; each concrete UV carrier/action remains
supplied. No matching, generated coefficients or all-operator stability claim
is introduced. Child integration targets the unmerged proof parent only.

Parent merge `checkpoint 02` was rechecked: all 18 controls, the link checker and
`git diff --check` passed. No worktree uses the local child branch; its HEAD
is reachable from the parent. Master remains unchanged.

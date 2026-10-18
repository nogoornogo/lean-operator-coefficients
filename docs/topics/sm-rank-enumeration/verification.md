# Verification

Branch `proof/sm-rank-enumeration`, base `checkpoint 01`, target
`proof/sm-statistical-finite-kernel`. No integration or push performed.

Commands:

    python3 tools/sm-rank-enumeration/enumerate.py
    python3 tools/sm-rank-enumeration/enumerate.py --csv
    lake build Physics.StandardModel.Operators.Audit.AuditSMChargedKernelRank Physics.StandardModel.Operators.Audit.AuditInverseCyclicFollowups
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

The new persistent audit checks four declarations transitively, permitting
only `propext`, `Classical.choice` and `Quot.sound`, and checks the Physics
dependency layer. The existing audit covers the bounded finite count theorems.
The script independently checks every saved candidate and orbit invariant.
No resource limit, dependency, pin, custom axiom or audit exception is changed.

Acceptance results:

- Exact recount and CSV regeneration passed, including all 572 saved rows.
- Focused build passed (4151 jobs): new four-declaration audit and existing
  38-declaration inverse-cyclic audit.
- Serialized full `lake build` passed (6882 jobs), with no warning/error
  lines in `/tmp/sm-rank-enumeration-build.log`.
- Layout passed: 1539 modules.
- Links passed: 817 Markdown files, 5034 links, 94 fragments, zero errors.
- `git diff --check` passed.

An initial cutoff-rank proof hit the default heartbeat bound. Separating the
carrier-dimension lemma and composing dimension equalities without dependent
rewrites resolved it; no resource setting changed.
Neutral matrix ranks and all-degree assignment classifications are explicitly
not verified.

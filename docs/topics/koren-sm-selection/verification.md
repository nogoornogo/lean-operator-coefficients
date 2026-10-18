# Verification

stage 01, branch `proof/koren-sm-selection`, base
`checkpoint 01`.

- Focused source build: `lake build Physics.StandardModel.Operators.KorenSMSelection`
  passed (3881 jobs).
- Persistent audit: `lake build Physics.StandardModel.Operators.Audit.AuditKorenSMSelection`
  passed (3883 jobs); 19 declarations checked transitively, allowing only
  propext, Classical.choice and Quot.sound. GUT-layer imports are rejected.
- Serialized `lake build` passed (6675 jobs). No residual warnings.
- `node tools/layout/check-layout.mjs` passed (1348 modules).
- `node tools/docs/check-links.mjs` passed (638 Markdown files, 3981 local
  links, 91 heading fragments, zero errors). Its first sandbox execution hit
  git subprocess EPERM; the same read-only command passed with escalation.
- `git diff --check` passed.

Initial elaboration errors involved type-tag simplification, unreduced casts
and a character-to-circle coercion. They were resolved through explicit
character/zsmul identities, without changing the frozen mathematical assumptions
or weakening the audit. No custom axioms, sorry or dependency changes.

Review checked printed left-handed versus signed species, opposite signs,
neutral Higgs charges, the finite subgroup embedding/restriction, the three-way
union and actual coefficient/residual transport. The only selection claimed
is a necessary obstruction. Finite neutrality is not full continuous neutrality;
there is no existence claim on the remaining contents. Source anomaly and
quantum-survival arguments remain outside this proof.

The work branched directly from master, independently of the unmerged BGW
branch. No BGW code or commits were incorporated. Master integration is not
authorized by completion. Build output remains disposable under /tmp.

## Authorized Master Integration, stage 01

Merged with its completed child by checkpoint 02; BGW follows as checkpoint 03.
Combined focused audits passed (33 + 19 + 74 strict checks, 3947 jobs),
serialized lake build passed (6681 jobs), layout passed (1354 modules),
links passed (650 Markdown files, 4026 links, zero errors), and diff check
passed. See the child's integration record for additive conflict resolution.

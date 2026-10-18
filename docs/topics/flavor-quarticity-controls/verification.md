# Verification Record

stage 01. Working branch `proof/flavor-quarticity-controls`, base
`checkpoint 01`, target
`proof/koren-sm-selection` under the recorded child-branch exception.
No master integration is authorized.

## Proof Checks

- `lake build Physics.StandardModel.Operators.DgtFlavorRestriction Physics.StandardModel.Operators.QuarticityAdapters`
  passed (3905 jobs).
- `lake build Physics.StandardModel.Operators.Audit.AuditFlavorQuarticityControls`
  passed (3907 jobs), finally 74 declarations checked transitively. Only
  propext, Classical.choice and Quot.sound are allowed. The audit also rejects
  GUT-layer imports, and is registered in Physics.lean.
- Initial serialized `lake build` passed (6678 jobs, then 72 audit declarations).
  The final build after adding the right-charged-lepton dictionary bridge is
  recorded below. No audit or dependency pin was relaxed.
- `node tools/layout/check-layout.mjs` passed (1351 modules).

Initial elaboration failures concerned modular literal reduction, extensionality
and composed representation simplification. All were repaired with explicit
casts, group/linear extensionality and proved action equality. No sorry or
custom axiom was introduced; no residual warning remains in focused builds.

## Semantic Review

DGT: checked the m=1,n=3 Table I specialization, signed opposite charges,
neutral Higgs, actual restriction, lepton/electron flavor correspondence,
muon-to-electron/tau coordinate conventions, independent B/W channels and
explicit nonzero coefficient transport. The restriction map on flavor Homs
uses the same underlying linear map. Non-surjectivity is proved, not inferred
only from dimensions or neutral charges. UV generation and mass-basis
identification are not premises or conclusions.

Quarticity: checked nuR right chirality, SM gauge neutrality, Z4=1 and Z2 odd,
eta charges 2/0 and real-sign action, exterior fermion statistics, right-Weyl
invariance and the normalized dressed evaluation. Bare, dressed and original
SM/Higgs-only inputs remain different domains. No unsupported all-alphabet L2
prohibition, vacuum, neutrino mass or dark-matter stability claim is made.

The requested adapter assessment succeeded within existing APIs. Two source
modules and one persistent audit suffice; no new foundational project or
external computational environment was needed. Disposable build logs are under
/tmp and are not tracked. Documentation/assumptions/coverage are reviewed
against the actual theorem statements.

## Final Acceptance

- Final serialized `lake build` passed (6678 jobs), with the 74-declaration
  audit replayed and no residual warnings.
- `node tools/docs/check-links.mjs` passed (644 Markdown files, 4007 local
  inline links, 91 heading fragments, zero errors). Its first sandbox run hit
  git subprocess EPERM; the same read-only check passed with escalation.
- `git diff --check` passed. Source/dependency review found no unrelated edits
  or pin changes. The source modules total 405 lines; no new foundations were
  necessary for the bounded adapters.
- Result, dossier, assumptions and literature coverage agree on the selected
  field domains and their physical exclusions. Both frozen endpoints are
  complete; integration into parent or master is outstanding.

## Authorized Integration, stage 01

User closed the current verification series and authorized master integration.
Child-to-parent merge: checkpoint 02; Koren/child-to-master merge: checkpoint 03.
BGW merged subsequently as checkpoint 04. Additive conflicts in Physics.lean,
Physics assumptions and the topic index retained both branches' entries.
Merged-state focused audits passed (3947 jobs): 33 BGW, 19 Koren and 74
flavor/quarticity strict transitive checks, 126 in total. Serialized lake build
passed (6681 jobs); layout passed (1354 modules); links passed (650 Markdown
files, 4026 links, 91 fragments, zero errors); git diff --check passed.
No physical scope, proof assumptions, pins or audit allowances changed.

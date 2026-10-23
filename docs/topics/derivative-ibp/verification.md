# Verification

## Original Survey Checkpoint

### Evidence Level

- Pinned local source reads plus the 19-name `#check` probe in
  [the library inventory](library-survey.md): `lake env lean` passed without warnings.
- Two unchanged generic Physlib files from the pinned external revision:
  separate `lake env lean` checks passed without warnings under local pins.
- Disposable copies with eight selected `#print axioms` commands: passed;
  all reports contain only `propext`, `Classical.choice`, `Quot.sound`.
- Source inspection only for the larger external SM jet and analytic packages;
  no build, compatibility claim or transitive audit of those packages.
- No new proof implementation, imported external premise, dependency change or
  new formalization baseline. No repository-wide `lake build` was rerun.

Temporary downloaded sources, probe files and output logs remain outside
source control. Exact pins, imports, checked names and reconstruction details
are recorded in [references](references.md) and [the library inventory](library-survey.md).

### Documentation Gates

- `node tools/docs/check-links.mjs`: passed; 1113 Markdown files,
  6959 local inline links, 114 heading fragments, zero errors.
- `python3 tools/docs/check-topic-index.py --pending-topic derivative-ibp`:
  passed; 148 topics indexed, 147 with outcomes, this planned topic explicitly pending.
- `git diff --check`: passed.

The topic remains planned for proof work after this completed survey. Its
research checkpoint is not a settled proof stop and receives no outcome-guide
entry yet. No master merge, push or branch deletion is authorized by this survey.
Before integration, reconcile the final used sources into RELATED_LITERATURE.md.

## Authorized Dependency Checkpoint

The later user-authorized v4.35.0 dependency change and proof compatibility
port have separate [verification evidence](dependency-integration.md).
The original survey above retains its original pins and evidence level;
it is not a claim that dependency integration added no source changes.


The initial dependency checkpoint was a failed full compatibility gate. Its
inventory recorded ScalarBlock conversion, generation-support recursion and
duplicate `SymmetricAlgebra.map_id` declarations. Individual strict
audits pass as listed there; no aggregate baseline is claimed. Original failing
consumer proofs are preserved. No parent/master merge or push was performed.

Final repository checks: layout coverage passed (2075 modules); topic index
passed (148 topics, all with outcomes); portable metadata passed (1107 files);
local links passed (1115 Markdown files, 6991 links, 118 fragments, zero errors);
`git diff --check` passed. These structural/documentation checks do not override
the failed Lean compatibility gate. Compiler/linter diagnostics include the
intentional inferred proof `defProp` warning and upstream module-system
recommendations; no warning policy was relaxed.


## Compatibility Repair Checkpoint

The [repair result](compatibility-repair.md) supersedes the initial name-collision
and injection failures. It records the passing Math aggregate, 12 connection
checks, 8 generation-injection checks and the remaining consumer failures.
No accepted full-project upgrade or parent integration follows.

## Carrier And Projection Compatibility Gate

The [carrier/projection pilot](carrier-pilot.md) supersedes the consumer stops
above while preserving their failed-route evidence. These commands pass:

```sh
LEAN_NUM_THREADS=4 lake build \
  Math.Audit.AuditCarrierPresentation \
  Physics.StandardModel.Operators.Audit.AuditSMGenerationSupport \
  Physics.StandardModel.Operators.Audit.AuditSMCarrierConnection \
  Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport \
  GUT.SU6.SelectionRules.Audit.AuditScalarBlockQque
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
```

The focused build passes 4910 jobs, with respectively 11, 9, 20, 354 and 83
strict transitive checks. The full build passes 7569 jobs, including Math,
Physics and GUT. The actual Q18 representation, restricted coefficient,
lower-generation local coefficient and Q18 local kernel all pass; a standalone
carrier theorem is not substituted for these consumers. Default recursion and
kernel limits are retained. Layer/import and axiom policies are unchanged.
Layout coverage passes for 2081 modules.

Root/docbuild share the v4.35.0 toolchain and all shared dependency revisions.
Installed Mathlib, TauCeti and Physlib match the root manifest and have clean
source trees. Optional doc-gen4 execution and HTML generation were not tested.
Residual warnings include module-system recommendations, deprecated APIs,
unused tactic/simp/section-variable lint and the intentional inferred-proposition
`mem_radical_iff` warning. No warning suppression or policy relaxation is added.

Final child checks pass: local links (1117 Markdown files, 7030 inline links,
119 fragments, zero errors), topic index (148 topics, all with outcomes),
portable metadata (1109 files) and `git diff --check`.

## Merged Parent Verification

The dependency child was merged with `--no-ff` into `proof/derivative-ibp`
under its recorded exception. Merged-state `LEAN_NUM_THREADS=4 lake build`
passes (7569 jobs) and layout coverage passes (2081 modules). The final topic
and outcome records are documentation-only changes after that build; no Lean
source or pin changed afterward.

Final local links pass (1117 Markdown files, 7031 inline links, 119 fragments,
zero errors); topic index passes (148 topics, all with outcomes); portable
metadata passes (1109 files); `git diff --check` passes. The bibliography and
assumptions ledgers agree with the final narrow algebra connection and proved
carrier/projection consumers. Master integration and remote push were not
performed. This compatibility endpoint supplies no derivative/IBP semantic
bridge or new physical result.

## Scalar Jet And IBP Proof Endpoint

The subsequent [implementation contract](implementation-plan.md) authorizes
the scalar proof package on the original `proof/derivative-ibp` branch.
The dependency child was already merged and deleted before this implementation;
no additional merge was needed. All toolchain/root/docbuild pins are unchanged.

```sh
lake build Math.Algebra.Audit.AuditScalarJetIBP
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The focused build passes (3177 jobs), including 62 strict transitive checks.
The audit rejects Physics/GUT imports and permits only `propext`,
`Classical.choice`, `Quot.sound`. It checks the actual unbounded jets,
ordinary derivatives and commutation, joint grades and finite-dimensionality,
divergence/range, covariance/stability, both coefficient-descent directions,
the graded formal IBP identity and local/residual-Hom zero/nonzero criteria.

The same audit checks complete reconstruction of the quadratic source and
primitive, the derivative-derived relation span, reduction kernel,
surjectivity, quotient-line equivalence, quotient dimension one, the
surviving class and its IBP identity. This is not just an audit of generic
quotient descent or a hand-supplied relation matrix.

The full build passes (7574 jobs), including all three aggregates and their
persistent audits. Layout coverage passes (2086 modules). New proof files
retain default recursion/kernel limits. An initial monomial-relabel
elaboration timeout was resolved by explicit intermediate types and a separate
weight identity; no resource limit was increased and no failed trial proof is
retained. New-file residual warnings are module-system import recommendations;
the previous full-project deprecation/linter warnings remain. No warning,
import or axiom policy is relaxed.

Final local links pass (1119 Markdown files, 7048 inline links, 119 fragments,
zero errors); topic index passes (148 topics, all with outcomes); portable
metadata passes (1111 files); `git diff --check` passes.
The result dossier, source register,
RELATED_LITERATURE and Math assumptions ledger agree on the scalar/permutation
scope and the absence of EOM, analytic integration or mixed-statistics claims.
The final documentation edits follow the successful full build and do not
change Lean sources or pins. The explicit successful stopping gate is reached;
master integration, remote push and a new mixed-statistics/spacetime project
are not performed.

## Extension Planning Assessment

The [extension assessment](extension-assessment.md) records prerequisites,
recommended ordering, relative work estimates and proposed acceptance gates.
It is a documentation-only checkpoint. No Lean source, dependency pin, audit
policy or proved scope changes. No Lean build or axiom audit was rerun; the
7574-job scalar baseline above remains the last verified proof baseline.

Inspection covered the current scalar/mixed/Weyl sources, pinned free-algebra
and grading APIs, Lorentz derivative interfaces, commutative derivation descent
and QED equation definitions. R1/R2 were rechecked for free/linearized EOM
scope. The [source register](references.md#extension-assessment-source-inspection)
distinguishes previously checked interfaces from newly inspected candidates.
No new result or literature-comparison coverage is claimed.

Documentation gates pass:

- `node tools/docs/check-links.mjs`: 1120 Markdown files, 7060 local inline
  links, 121 heading fragments, zero errors.
- `python3 tools/docs/check-topic-index.py`: 148 topics, all with outcomes.
- `python3 tools/docs/check-work-metadata.py`: 1112 portable files.
- `git diff --check`: no errors.

Only topic documentation changes. The scalar stopping gate remains complete;
no new foundation, branch integration or remote push is performed.

## Internal Linear And Mixed Jet A/B Endpoint

The later user direction authorizes the
[A/B implementation contract](mixed-implementation-plan.md). All proof gates
pass on `proof/derivative-ibp`. The [result dossier](../../proof/current/core/Math/MIXED_JET_IBP.md)
records actual sources, conventions, representation equivalences and limits.
No dependency pin or previously checked proof is changed.

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditMixedJetIBP
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The focused build passes 3265 jobs. The new persistent audit checks 223
declarations transitively, permits only `propext`, `Classical.choice` and
`Quot.sound`, and rejects Physics/GUT imports. It covers internal jet maps,
the actual scalar symmetric/polynomial bridge, non-permutation shear,
mixed even derivatives and commutation, joint subspaces and finite grades,
arbitrary internal covariance, both actual-source/coefficient directions,
the equivariant derivative-free boundary, divergence stability and the
local/residual-Hom correspondence. The shared descent includes inverse
evaluation and zero/nonzero criteria.

The same audit checks full mixed source/current spans, exterior Pauli and
reordering cancellations, the derivative-derived relation range, coordinate
extraction, reduction kernel, surjectivity, the actual quotient-line
equivalence, quotient dimension one, surviving class and IBP identity.
No candidate relation matrix or basis completeness is supplied as a premise.

Full build passes 7594 jobs, including Math/Physics/GUT and their persistent
audits. A temporary process-tree monitor applied the nine-minute and 16 GiB
per-process RSS ceilings. The warm-cache aggregate check stopped normally;
observed peak process RSS was 6031164 KiB. This is a check-specific measurement,
not a bound for new Lorentz/EOM work. Layout passes for 2100 modules.

Default recursion/kernel and heartbeat limits are retained. Recursive simp
rules on singleton coefficients and jet index normalization were replaced by
explicit identities. Tensor equality and module-instance inference were
split into typed factor equalities and local reducible carrier instances;
the symmetric-source finiteness proof transports finite generation through
the inverse equivalence. Failed trials are not retained. New-module residual
warnings are module-system recommendations; existing project deprecation and
linter warnings remain. No warning/import/axiom policy was relaxed.

The bibliography, source register and Math assumptions ledger now distinguish
the proved A/B bridges from the still-inspected external SM/Lorentz/EOM APIs.
No literature comparison coverage row is added. Final documentation gates pass:

- Local links: 1122 Markdown files, 7098 inline links, 122 fragments, zero errors.
- Topic index: 148 topics, all with outcomes.
- Portable metadata: 1114 files.
- `git diff --check` and the unchanged root/docbuild pin diff: no errors.

Final documentation changes follow the successful full build and change no
Lean source or dependency. The successful stop is A/B; C–E, master merge and
remote push are not performed.

## C/D/E Direction, Lorentz And Free Scalar EOM Endpoint

The [C/D/E contract](direction-lorentz-eom-plan.md) continues on the existing
parent branch without a separate estimate stop after D. The original scalar
and A/B baselines above are retained. C supplies actual direction actions,
symmetric-power/multi-index connections, covariant currents and inverse mixed
source/IBP descent. D supplies the locally proved Pauli/Weyl adapter and
scalar contractions. E supplies all equation descendants, an inverse
EOM-ideal/free-algebra presentation, equivariant combined-source comparison
and actual on-shell IBP coefficients.

Focused endpoint/audit command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditDirectionalJetIBP Math.Algebra.Audit.AuditJetEquationIBP Physics.FieldTheory.Jets.Audit.AuditLorentzScalarEOM
```

The audit target closure passes 3279 jobs. The audits check **112**, **94**
and **67** declarations respectively, **273** total, transitively. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. The Math audits
reject Physics/GUT imports, and the physical audit rejects GUT imports.
Historical import-origin diagnostics retain the layout normalization rule.
No audit allowlist or import policy is relaxed.

The complete one-direction regression proves all quadratic source relations,
a zero EOM/IBP quotient and dimension zero, starting from the prior off-shell
quotient of dimension one. Four-dimensional controls prove the full trace
relation and every derivative descendant, retention of pure time jets of
arbitrary order in the generator quotient and algebra before IBP, and the
kinetic term's membership in the actual divergence range modulo EOM.
The combined-source comparison also intertwines the actual group actions.

Full aggregate command:

```sh
LEAN_NUM_THREADS=4 lake build
```

It passes **7612 jobs**, including Math, Physics, GUT and every persistent
old/new audit. Heavy commands are serialized with a 540-second timeout and
an inherited **16 GiB per-process address-space limit** using the operating
system resource limit. This is a resource guard, not a measured RSS or a
prediction for future work. Disposable wrappers/logs remain outside source
control. No elapsed-time estimate is inferred from the build.

Default heartbeats, recursion/kernel limits and dependency pins are unchanged.
Local instances, explicit maps and coercion/evaluation lemmas resolve the
adapter elaboration without raising limits. New-module residual warnings are
module-system recommendations. Existing project warnings remain. No `sorry`,
custom axiom or external equation/counting premise is introduced.

Layout validation passes for **2118 modules**, including aggregate coverage,
layer direction, local imports, cycles and relocation audits. The bibliography,
source register and Math/Physics assumptions distinguish the actual local
Lorentz/EOM proofs from inspected external APIs. No literature-comparison
coverage row or whole-library/physical equivalence claim is added. Final
local-link, topic-index, portable-metadata, diff and unchanged-pin checks are
recorded with the completed endpoint below.

The completed documentation checks pass:

- Local links: 1125 Markdown files, 7144 local inline links, 125 fragments,
  zero errors. The unchanged checker was rerun in a permitted context after
  the sandbox rejected its Git subprocess (`spawnSync git EPERM`).
- Topic index: 148 topics, all with outcome links; no pending exceptions.
- Portable metadata: 1117 files; external source metadata retained.
- `git diff --check` and root/docbuild dependency-pin diff: no changes/errors.

Final documentation follows the successful full build without further Lean
source changes. The successful C/D/E stop is reached on the topic branch.
Master integration and remote push are not performed.

## Linear EOM, Weyl And Conjugate Child Integration

The verified kernel/conjugate child was merged with preserved history into
its recorded `proof/linear-eom-weyl` parent. That intermediate merged tree
passed its four-audit closure (3424 jobs, 255 strict checks), 7637-job full
build, layout and documentation checks. The combined parent was then merged
into this branch with `git merge --no-ff proof/linear-eom-weyl`.

The integration target was clean and had no independent advance. Neither
merge required conflict resolution, and the final Lean/dependency tree equals
the verified combined child tree. No unrelated worktree or contributor changes
were incorporated. The source registers were reconciled into the literature
list before both integrations; no source inspection or physical scope claim
was expanded by the merge.

Final merged-state focused command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditDirectionalJetIBP Math.Algebra.Audit.AuditJetEquationIBP Physics.FieldTheory.Jets.Audit.AuditLorentzScalarEOM Math.Algebra.Audit.AuditJetSpurionEvaluation Physics.FieldTheory.Jets.Audit.AuditLorentzSpurionEvaluation Math.Algebra.Audit.AuditLinearJetEquation Physics.FieldTheory.Jets.Audit.AuditWeylLinearEquation Math.Algebra.Audit.AuditJetEOMCompletion Physics.FieldTheory.Jets.Audit.AuditWeylJetAdjoint
```

It passes 3444 jobs and 625 strict transitive checks:
112 + 94 + 67 + 87 + 10 + 94 + 51 + 38 + 72. The standard-axiom policy and
import-layer restrictions remain unchanged. Full `LEAN_NUM_THREADS=4 lake build`
passes 7637 jobs, including all project aggregates and persistent audits.
Heavy checks retain four Lean threads, a 540-second command timeout and an
inherited 16 GiB per-process address-space guard. Existing module-system,
deprecation and linter warnings remain; no policy or limit is relaxed.

Layout passes for 2143 modules. Local links, topic/outcome coverage (151 topics),
portable metadata and `git diff --check` pass. Root/docbuild dependency pins
and root README are unchanged by integration. The earlier scalar, A/B and
C/D/E counts remain checkpoint evidence; this section owns the enlarged
merged-state baseline. Final integration documentation is checked separately,
with no additional Lean build for those documentation-only changes.

The completed child work now resides on `proof/derivative-ibp`. This branch
remains unmerged into master; no remote mutation is performed.

The local `proof/jet-eom-completion` and `proof/linear-eom-weyl` branches were
deleted with `git branch -d` only after confirming reachable HEADs, no attached
worktrees and no pending child dependency. The parent branch and historical
topic branch names are retained. No worktree removal or remote deletion is done.

## Free Abelian Field-Strength Child Integration

Under explicit user direction, the completed free Abelian child was merged
into this clean parent with `git merge --no-ff proof/abelian-field-strength`.
The target had no independent advance; no conflict resolution was required.
The merged Lean sources, root README and dependency pins equal the verified
child tree. No unrelated worktree or contributor changes were incorporated.
The source register was already reconciled into the bibliography before
integration, including the convention guidance and inspected-library boundaries.

Merged-state focused command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditDirectionalJetIBP Math.Algebra.Audit.AuditJetEquationIBP Physics.FieldTheory.Jets.Audit.AuditLorentzScalarEOM Math.Algebra.Audit.AuditJetSpurionEvaluation Physics.FieldTheory.Jets.Audit.AuditLorentzSpurionEvaluation Math.Algebra.Audit.AuditLinearJetEquation Physics.FieldTheory.Jets.Audit.AuditWeylLinearEquation Math.Algebra.Audit.AuditJetEOMCompletion Physics.FieldTheory.Jets.Audit.AuditWeylJetAdjoint Physics.FieldTheory.Jets.Audit.AuditMaxwellLinearEquation
```

It passes 3450 jobs and 737 strict transitive checks:
112 + 94 + 67 + 87 + 10 + 94 + 51 + 38 + 72 + 112. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted; import-layer restrictions
remain unchanged. Full `LEAN_NUM_THREADS=4 lake build` passes 7643 jobs,
including all project aggregates and persistent audits. Heavy checks retain
four Lean threads, a 540-second command timeout and an inherited 16 GiB
per-process address-space guard. Existing module-system, deprecation and
linter warnings remain; no policy, limit or dependency pin is changed.

Layout passes for 2149 modules. Local links pass for 1148 Markdown files,
7338 local inline links and 125 heading fragments, with zero errors. The
unchanged link checker runs where its read-only Git subprocess is permitted.
All 152 topics have indexed outcomes, with no pending exceptions. Portable
metadata passes for 1140 files, and `git diff --check` is clean. Integration
record edits after the successful proof gates are documentation only; no
further Lean build is run for them.
The child result now resides on `proof/derivative-ibp`. This parent remains
unmerged into master, and no remote mutation or new proof topic is performed.

The local `proof/abelian-field-strength` branch was deleted with `git branch -d`
after verifying that its HEAD is reachable from this parent, no worktree uses
it and no pending child work needs it. The parent and historical topic branch
name are retained. No worktree removal or remote branch deletion is performed.

## Final Master Integration

The [merged-state record](../derivative-ibp/master-integration.md) supersedes
the earlier unmerged integration status. The original proof endpoints and
checks above remain checkpoint evidence; all recorded parent merges and the
master merge are verified without changing theorem assumptions.

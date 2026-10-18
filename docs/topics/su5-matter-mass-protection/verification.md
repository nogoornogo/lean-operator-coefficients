# Verification — SU(5) Matter/Mass Protection

Verified at stage 01, working branch `proof/su5-matter-mass-protection`,
base `checkpoint 01`, target master.
No merge or remote push is authorized or performed.

- `lake build GUT.SU5.Audit.AuditScalarBlockQque`: passed, 3,900 jobs.
  73 declarations passed strict transitive axiom checks allowing only
  `propext`, `Classical.choice`, `Quot.sound`. The import-origin check
  rejects transitive SU(6) modules and passed. New source builds had no warnings.
- Serialized `lake build`: passed, 6,594 jobs; existing informational
  axiom-audit reports were replayed. No new proof baseline is inferred from
  the earlier documentation-only plan.
- `node tools/layout/check-layout.mjs`: passed, 1,267 modules.
- `python3 tools/su5-matter-mass-protection/audit_mass_patterns.py`:
  five exact tests passed. Their scope is the supplied hypercharge table,
  fixed rational mass ansatz and one copy-swap flavor map, not a Lean oracle.
- `python3 tools/qque/audit_one_generation.py`: four exact tests passed.
- `node tools/docs/check-links.mjs`: passed, 536 Markdown files,
  3,486 local links, 88 heading fragments, zero errors.
- `git diff --check`: passed; source statements, dossier and assumption
  ledger reviewed together before the topic checkpoint.

Initial focused checks exposed ordinary elaboration errors and a timeout in
joint-action transport. The final proofs use named representation group-law
identities and restriction lemmas, without enlarging heartbeat/recursion limits,
adding axioms or changing dependency pins. The successful focused/full checks
above supersede those failed attempts.

## Reviewed Assumptions And Stop Gate

The SU(5) input class is inhabited by identity residual action. Pointwise factors
need not have group laws; genuine species characters are derived from the field
action. Arbitrary-mass light membership is supplied explicitly. The orthogonal
extra-pair mass proves nonzero mass and retained zero modes, not UV covariance
or a scalar/Yukawa origin of that extension. Physical coefficients remain typed
on Q and the right-handed duals of uc/ec, with existing spinors and alternation.

C1/C2 exact checks do not instantiate the mixed candidates as Lean inputs.
General compensated flavor transport and species-by-species mixed-kernel
identification are explicitly unresolved interfaces at the bounded stop gate.
This is proof plus a feasibility assessment, not a general SU(5) no-go or proof
of proton stability/instability. No outside physical calculations were started.


## Additional Independent-Row Mass Phase — stage 01

The subsequent user request authorized other bounded mass checks on the same
branch; the frozen scope is [mixed-mass plan](mixed-mass-plan.md).

- `lake build GUT.SU5.Audit.AuditMixedTenMass`: passed, 3,897 jobs;
  95 strict transitive declaration checks and original SU(6) import rejection
  passed. Only the standard three axioms are permitted; new sources have no
  warnings. No heartbeat/recursion limit or dependency change.
- Serialized `lake build`: passed, 6,596 jobs. The captured build output had
  no warning/error diagnostics; disposable output is not committed.
- `node tools/layout/check-layout.mjs`: passed, 1,269 modules.
- `python3 tools/su5-matter-mass-protection/audit_mass_patterns.py`:
  six exact tests passed, including affine splitting/cancellation controls.
- `python3 tools/qque/audit_one_generation.py`: four exact tests passed.
- `node tools/docs/check-links.mjs`: passed, 538 Markdown files,
  3,494 local links, 88 heading fragments, zero errors.
- `git diff --check`: passed; statements, source-derived light maps,
  right-handed dual convention and scope ledger reviewed together.

The independent-row family proves nonzero physical exterior coefficients on
actual light species for arbitrary complex rows. Active rows give nonzero mass
and radical dimension 15; zero mass gives dimension 35. Partial masses derive
additional light maps without a new finrank-21 Lean claim. The finite script's
partial dimension 21 is explicitly separate. The common scalar ten character
remains an input; arbitrary compensated/residual mixing and UV coupling origin
remain outside scope. No merge or remote push is performed.


## Arbitrary-Copy Matrix Phase — stage 01

Authorized continuation on the existing branch from checkpoint `checkpoint 02`;
[matrix-mass plan](matrix-mass-plan.md) fixes the endpoint.

- `lake env lean GUT/SU5/SelectionRules/MatrixTenMass.lean`: passed without warnings.
- `lake build GUT.SU5.Audit.AuditMatrixTenMass`: passed, 3,898 jobs;
  47 strict transitive declaration checks passed, only `propext`,
  `Classical.choice`, `Quot.sound`; original SU(6) import rejection passed.
- Serialized `lake build`: passed, 6,598 jobs; no warning/error diagnostics
  in captured disposable output.
- `node tools/layout/check-layout.mjs`: passed, 1,271 modules.
- `node tools/docs/check-links.mjs`: passed after final documentation updates;
  540 Markdown files, 3,504 local links, 88 heading fragments, zero errors.
  The final sandbox attempt hit `spawnSync git EPERM`; the identical read-only
  check passed on an approved escalated retry.
- `git diff --check`: passed. Reviewed the exact radical criterion, kernel
  dimension bound, actual injective/equivariant embeddings, right-handed dual
  transport and participating-range scope together.

No pins, heartbeat/recursion limits or axiom allowances changed. Existing
finite scripts were not rerun: their definitions and inputs are unchanged,
and they do not cover the new arbitrary-copy theorem. The new result is
verified directly by Lean and its persistent audit, with no computational
oracle premise. The frozen endpoint is complete; common scalar action and
species Dirac ansatz remain fixed. No merge or remote push is performed.

## Assumption-Removal Feasibility — stage 01

Documentation-only assessment after `checkpoint 03`, with current source inspection
of `QqueCommonIrreducible` and the matrix-family result. It introduces no new
Lean theorem or proof baseline. No Lean build or axiom audit was rerun.

- `node tools/docs/check-links.mjs`: passed, 541 Markdown files, 3,506 local
  links, 88 heading fragments, zero errors. Sandbox `spawnSync git EPERM`
  required an approved identical read-only escalated retry.
- `git diff --check`: passed.
- Reviewed the distinction between common non-scalar copy representations and
  independently arbitrary species actions. The proposed invariant-mass normal
  form, constituent-index extension and C3 diagnostic remain unformalized;
  their model conditions and actual-field obligations are explicit.


## Invariant Normal Form And Non-Scalar Copies — stage 01

Authorized continuation from `checkpoint 04`, with statements and stop gates in
[normal-form/copy plan](normal-form-copy-plan.md).

- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditBipartiteNormalForm
  Physics.FieldTheory.Mass.Audit.AuditCommonCopyKernel
  GUT.SU5.Audit.AuditInvariantMassNormalForm
  GUT.SU5.Audit.AuditNonScalarCopyMass`: passed, 3,957 jobs.
- The four persistent audits passed 13 + 13 + 52 + 37 = 115 strict transitive
  declaration checks; only `propext`, `Classical.choice`, `Quot.sound` are
  allowed. Both SU(5) original-import-origin gates passed.
- The initial normal-form audit detected a historical SU(6) circle-lattice
  dependency through an existing charge-separation helper. The final proof
  uses a direct bounded circle-phase separation lemma and minimal actual SM
  charge proofs instead. No import-origin or axiom gate was relaxed.
- Serialized `lake build`: passed, 6,607 jobs, without warning/error diagnostics
  in disposable captured output.
- `node tools/layout/check-layout.mjs`: passed, 1,280 modules.
- `node tools/docs/check-links.mjs`: passed, 544 Markdown files, 3,526 local
  links, 88 heading fragments, zero errors. The final sandbox retry encountered
  `spawnSync git EPERM`; the identical read-only escalated check passed.
- `git diff --check`: passed.

Reviewed the arbitrary symmetric-mass quantifier, derived species matrices,
actual radical memberships, common non-scalar kernel splits, right-handed
conventions and physical exterior transport. A named `PhysicalQqueEndpoint`
property packages the existing coefficient type without extra premises or
changed heartbeat/recursion limits. Dependency pins are unchanged. Earlier
finite diagnostic scripts were not rerun: their inputs are unchanged and they
are not proof premises for these new Lean theorems.

The two endpoints are complete separately. A single theorem removing both
assumptions simultaneously, full-light transport and UV/global-group bridges
remain explicitly documented. No merge or remote push is performed.


## Unified Arbitrary-Mass/Common-Copy Phase — stage 01

Authorized continuation from `checkpoint 05`; [unification plan](unification-plan.md)
freezes the statement and endpoint. The earlier two-stage verification remains
valid for those unchanged statements.

- `lake build GUT.SU5.Audit.AuditNonScalarInvariantMass`: passed, 3,956 jobs;
  27 strict transitive declaration checks passed with only `propext`,
  `Classical.choice`, `Quot.sound`. The original SU(6) import-origin gate passed.
- Serialized full `lake build`: passed, 6,609 jobs. The final run includes
  the direct audit of the tensor-coordinate evaluation lemma as well as all
  its transitive uses. No warning/error diagnostics in captured output.
- `node tools/layout/check-layout.mjs`: passed, 1,282 modules.
- `node tools/docs/check-links.mjs`: passed, 546 Markdown files, 3,538 local
  inline links, 88 heading fragments, zero errors.
- `git diff --check`: passed.

Reviewed the actual tensor-to-finite-copy equivalences, vanishing same-side
pairings, arbitrary-B quantifier, entire cross-map reconstruction including
the bar-five block, derived residual-equivariance, equality of mass forms and
B-radical memberships. The source uses existing compact-kernel and physical
exterior transports; no new classification certificate or literature premise
is added. No pins, axiom allowances or heartbeat/recursion limits changed.

The unified endpoint is complete. Full-light transport, actual global descent,
UV residual mechanisms and all-BNV/model matching claims remain separate.
No merge or remote push is performed.


## Supplied Target Unitarity Removed — stage 02

Authorized continuation from `checkpoint 06`; [target-unitarity plan](target-unitarity-plan.md)
freezes the metric/action boundary and original-field endpoint.

- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditCommonCopyKernel
  GUT.SU5.Audit.AuditNonScalarCopyMass
  GUT.SU5.Audit.AuditNonScalarInvariantMass`: passed, 3,958 jobs.
- Extended persistent audits passed 22 + 39 + 28 = 89 strict transitive checks,
  with only `propext`, `Classical.choice`, `Quot.sound`. Both SU(5) original
  SU(6) import-origin rejection gates passed. Earlier declarations are covered
  together with all new proof interfaces; previous checkpoint counts remain
  historical evidence for their own revisions.
- Inspected elaborated types of `exists_common_split_of_continuous` and
  `arbitrary_mass_light_exterior_of_continuous` with targeted `lake env lean`:
  neither includes a supplied target-unitarity argument. The latter retains
  original fields, original B and actual B-radical membership in its conclusion.
- Serialized full `lake build`: passed, 6,609 jobs; no warning/error diagnostics
  in captured disposable output.
- `node tools/layout/check-layout.mjs`: passed, 1,282 modules.
- `node tools/docs/check-links.mjs`: passed, 548 Markdown files, 3,551 local
  inline links, 88 heading fragments, zero errors. The final sandbox attempt
  encountered `spawnSync git EPERM`; the identical read-only escalated check
  passed.
- `git diff --check`: passed.

Reviewed the derived finite-basis unitary target, actual representation
equivalence, both kernel directions, dimension equality, original-kernel split
transport, physical range transport and the arbitrary-B mass-form equality.
No pin, proof limit or axiom allowance changed. No new literature certificate
is assumed. Finite diagnostic scripts were not rerun; they are unchanged and
are not proof premises. Compactness and joint continuity remain; this does
not claim algebraic-only generalization or automatic invariance of the given
metric. The authorized endpoint is complete. No merge or remote push is performed.


## Algebraic Source-Semisimple Phase — stage 02

Authorized continuation from `checkpoint 07`; [algebraic-copy plan](algebraic-copy-plan.md)
freezes the source-only replacement condition and original-field endpoint.

- Focused `lake build Math.RepresentationTheory.Audit.AuditAlgebraicCommonKernel
  Physics.FieldTheory.Mass.Audit.AuditAlgebraicCommonCopyKernel
  GUT.SU5.Audit.AuditNonScalarCopyMass
  GUT.SU5.Audit.AuditNonScalarInvariantMass`: passed, 3,961 jobs, without warnings.
- Persistent audits passed 7 + 6 + 41 + 29 = 83 strict transitive checks, only
  `propext`, `Classical.choice`, `Quot.sound`. Both model original-SU6-origin
  rejection gates passed. New Math/Physics files and audits are registered in
  their layer aggregates.
- Inspected elaborated shared-kernel and arbitrary-B endpoint types with
  targeted `lake env lean`: no H topology, compactness, continuity, target
  semisimplicity or unitarity arguments occur. Source semisimplicity is explicit.
  The model conclusion retains original B and original participating ranges.
- Serialized full `lake build`: passed, 6,613 jobs, without warning/error
  diagnostics in captured disposable output.
- `node tools/layout/check-layout.mjs`: passed, 1,286 modules.
- `node tools/docs/check-links.mjs`: passed, 550 Markdown files, 3,567 local
  inline links, 88 heading fragments, zero errors.
- `git diff --check`: passed.

Reviewed isotypic-component representative selection, target-image independence
without target semisimplicity, assembled injection and dimension contradiction,
actual kernel simple-submodule inclusions, derived equivariant retractions and
physical exterior transport. The representation/group-algebra bridge locally
uses the same definitional-transparency settings as the existing library
`equivLinearMapAsModule` interface; no heartbeat/recursion limit, dependency pin
or axiom allowance changes. No new literature premise or computational oracle
is supplied. Existing finite diagnostic scripts are unchanged and were not rerun.

The source-semisimple arbitrary-group endpoint is complete. Removing source
semisimplicity, independent species actions, whole-light transport and UV/global
bridges remain separate scope decisions. No merge or remote push is performed.


## Pure Finite-Dimensional Copy Carriers — stage 02

Authorized continuation from `checkpoint 08`; [carrier plan](algebraic-carrier-plan.md)
fixes the requested finite-dimensional complex representation endpoint.

- `lake build GUT.SU5.Audit.AuditNonScalarCopyMass
  GUT.SU5.Audit.AuditNonScalarInvariantMass`: passed, 3,959 jobs without warnings.
- Existing persistent audits passed 41 + 29 = 70 strict transitive checks,
  including both broadened algebraic signatures and retained analytic endpoints.
  Only `propext`, `Classical.choice`, `Quot.sound`; both original-SU6-origin
  rejection gates passed. Declaration names and audit coverage are unchanged.
- Targeted `lake env lean` elaborated-type inspection confirmed
  `arbitrary_mass_light_exterior_of_semisimple` takes only `AddCommGroup`,
  `Module complex` and `FiniteDimensional` for copy carriers. No norms, inner
  products, H topology, continuity, compactness, unitarity or target semisimplicity
  occur in its inputs. Original B-radical and actual range conclusions remain.
- Serialized full `lake build`: passed, 6,613 jobs, without warning/error
  diagnostics in captured disposable output.
- `node tools/layout/check-layout.mjs`: passed, 1,286 modules.
- `node tools/docs/check-links.mjs`: passed, 552 Markdown files, 3,580 local
  inline links, 88 heading fragments, zero errors.
- `git diff --check`: passed.

Reviewed every broadened structural declaration, local analytic rebindings,
actual range and dual representations and the arbitrary symmetric B quantifier.
No surrogate carrier, Hilbertization or metric certificate is introduced in
the algebraic endpoint. No pins, proof limits or axiom allowances changed.
Existing finite scripts are unchanged and are not premises of this theorem.
The requested statement is achieved on the current matter/SM/common-copy action;
source semisimplicity and positive dimension difference remain explicit.
Whole-light and UV/global bridges remain documented. No merge or remote push.

## Model-Independent Physical Common-Copy Bridge — stage 02

Authorized continuation from `checkpoint 09`; [plan](model-independent-plan.md) freezes
the actual-field mass-square interface and shared/SU(5) consumer endpoint.

- `lake build Physics.FieldTheory.Mass.Audit.AuditPhysicalCommonCopyModel
  GUT.SU5.Audit.AuditPhysicalCommonCopyAdapter`: passed, 3,958 jobs without warnings.
- New persistent audits: 16 shared + 6 adapter = 22 strict transitive axiom checks,
  only `propext`, `Classical.choice`, `Quot.sound`. The shared audit rejects all
  current GUT-layer imports and all original SU(5)/SU(6) origins; the adapter's
  original-SU6 exclusion also passed.
- Targeted `lake env lean` elaborated-type inspection confirmed the shared
  `Model.arbitrary_mass_light_exterior` takes arbitrary H and actual carrier F,
  finite complex S/T, source semisimplicity and dim T < dim S. No SU(5) carrier,
  H topology, metric, continuity, compactness, target semisimplicity or supplied
  light/coefficient certificate occurs. The explicit model realization contains
  injective full-copy embeddings and mass squares, rather than the conclusion.
  The generic Dirac constructor needs finite actual target for biduality.
- The initial shared import audit found an unused transitive dependency through
  `SMEpsilonTensor → StandardModelLocalOperator → ChargeResolved → WeylOrbit`.
  Replacing the first import by direct library imports removed it. Circle is
  now imported directly by `StandardSMGaugeTensor`.
- The first full build exposed a now-unused `open Math` in the existing embedding
  audit. It was removed without changing any theorem, axiom or import-origin
  check. Targeted `lake env lean GUT/SU5/Audit/AuditStandardModelEmbedding.lean`
  then passed. The final full-build result is recorded below.

Final checks:

- Serialized full `lake build`: passed, 6,617 jobs, with no warning/error
  diagnostics in the final captured disposable output. The initial failure and
  its scoped correction are recorded above; all audit checks remain enabled.
- `node tools/layout/check-layout.mjs`: passed, 1,290 modules.
- `node tools/docs/check-links.mjs`: passed, 554 Markdown files, 3,595 local
  inline links, 88 heading fragments, zero errors.
- `git diff --check`: passed.

Reviewed the original B mass-square equation, injective actual kernel embeddings,
radical support, restricted ambient action, finite-copy dual conventions and
fermionic physical exterior transport. The SU(5) model instance derives its
interface for every invariant symmetric B using the existing normal form and
branching, then directly consumes the shared theorem. No general classification
of other unified models, whole-light extension or UV matching is inferred.
No pins, proof limits or axiom allowances changed; no numerical script is a
premise of the new theorem. No merge or remote push is performed.


## Master Integration — stage 02

The user explicitly authorized master integration at the current completed
endpoint. The worktree was clean, master remained at the recorded base
`checkpoint 10`, and no target-only commits or semantic conflicts required reconciliation.
Topic endpoint `checkpoint 11` was merged with `git merge --no-ff
proof/su5-matter-mass-protection` as `checkpoint 12`.

Merged-state verification:

- Serialized `lake build`: passed, 6,617 jobs; registered strict transitive axiom
  and dependency audits passed. No warning/error diagnostics in captured output.
- `python3 tools/su5-matter-mass-protection/audit_mass_patterns.py`: six exact
  supplementary tests passed.
- `python3 tools/qque/audit_one_generation.py`: four exact supplementary tests passed.
- `node tools/layout/check-layout.mjs`: passed, 1,290 modules.
- `node tools/docs/check-links.mjs`: passed, 554 Markdown files, 3,596 local inline
  links, 88 heading fragments, zero errors after integration-record updates.
- `git diff --check`: passed.

The post-record link checker initially hit sandbox `spawnSync git EPERM`;
an identical read-only escalated retry passed with the counts above.

Confirmed topic HEAD reachable from master, no worktree using the topic branch,
and no topic child branch needing it. Deleted the local topic branch with
`git branch -d`; its historical name and endpoint remain in this record.
The separate detached worktree was left untouched. No remote push or remote
branch deletion was performed. Remaining model-realization, whole-light,
global/UV and physical interpretation boundaries are unchanged.

The final integration-record update is documentation-only; no further Lean
build was rerun after it. The merged source verification above remains its
proof baseline.

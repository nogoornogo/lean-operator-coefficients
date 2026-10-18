# Topic And Branch Workflow

This supersedes status-partitioned work tracking.

## Document Roles

- `AGENTS.md`: concise instructions for agents working in this repository.
- `docs/topics/README.md`: the complete subject navigation index for topic folders
  containing a README, including active and retained topics, not a second status database. Link to topics rather than copy their progress narratives.
- `docs/topics/<topic>/README.md`: the canonical plan, status and result for
  one bounded topic, before and after completion. The path does not depend on status.
- `docs/topics/_history/`: an append-only outcome guide, with topic names,
  relative folder links and brief results/stopping reasons. It does not own
  detailed status, open obligations or verification.
- `docs/proof/current/core/`: the current general completeness theorem and its direct
  structural extensions.
- `docs/proof/current/inputs/`: supplied-data interfaces and optional constructions of
  residual groups, field identifications and multiplicity actions.
- `docs/proof/current/applications/`: bounded consumers, local classifications and
  literature certificates. Within each role, use Math / Physics / GUT labels.
  Dossiers describe completed results, not chronological work diaries.
- `docs/proof/current/`: result-oriented guides for general theorems, decidable
  classifications, input constraints, model inputs and independent results.
  Detailed dossiers remain in the three role directories.
- `docs/proof/ASSUMPTIONS.md` and the per-layer assumptions ledgers: indexes of
  verified theorem inputs, application conditions and boundaries; see below.
- Root `README.md`: the user-selected main claims of the project. Agents must
  not automatically add achievements or change its emphasis. Propose updates
  when useful and edit only on explicit user direction. This restriction does
  not prevent maintaining topic or proof indexes.
- `docs/proof/INTERFACES.md` and role/subject `interfaces/`: declaration and
  implementation maps supplementing the proof dossiers, not a status database.
- `docs/model-studies/`: reader-facing model-specific applications and bounded
  exploration results, separate from the selected main claim. Stopping a model
  search does not make its results historical; its work records stay in topics.
- `docs/verification/`: English cross-topic literature coverage indexes and
  their reading/publication rules; not proof dossiers or work queues.
- Historical records: evidence about their own checkpoints, not current instructions.

Independent model applications belong under `docs/model-studies/`, with their
work records under `docs/topics/`. Topic records remain in their own folders
when complete, stopped or deferred. Reuse an existing topic when the objective
continues; use predecessor/successor links to explain changes of direction.
Do not move a record because it is old. Proof statements and their hypotheses
stay in `docs/proof/` by role; moving a dossier does not make it a premise of
the current main claim or close an old conditional boundary.

Git preserves earlier versions and exact edit timing. Topic records preserve
meaning: goals, result, stopping reasons, assumptions, verification and unresolved
conditions. Retained reviews/drafts are checkpoint evidence, not active instructions.
Proof and work records are organized by their current role and topic. No
knowledge of an earlier directory layout is needed. Preserve mathematical
assertions, assumptions, failed-route boundaries and verification evidence;
new work must not be appended to an earlier checkpoint as though checked there.

### Topic Outcome Guide

Append a short entry to [topics/_history](../topics/_history/README.md) after a
successful topic integration and merged-state verification. Also record an
explicitly settled unmerged stop or deferral, with its scope clear. Active
work remains in its topic rather than being recorded as a finished outcome.

Each entry has a topic name, relative link to its folder, and a brief outcome
or stopping reason. **Do not include dates, timestamps or commit IDs.** Detailed
state, hypotheses, residual work, checks and integration evidence belong only
to the topic record; link rather than duplicating that state in the guide.
A changed later outcome can receive a concise new entry linked to the same
topic, without silently rewriting the earlier outcome.

Use `001_topics_history.md`, `002_topics_history.md`, and so on. The file
sequence determines reading order only; it does not number topics or entries.
Aim for about 25 entries per file, allowing a coherent phase boundary. Append
to the last file and start the next volume when needed. Do not reorganize old
volumes by subject. During parallel integrations, coordinate appends in the
integration checkout, retain both outcomes when resolving a conflict, and avoid
duplicate entries for the same integration. Update the guide's volume links.

The initial backfill is a navigational order of retained records, not a claim
to exact chronological completion. Maintained records follow the portable
metadata rule below. The guide is an allowed global navigation index; it does not
replace canonical topic-owned records or create a second status database.

### Navigation Coverage Check

Run `python3 tools/docs/check-topic-index.py` to check both indexes. Every topic
folder with a README must appear directly in the subject index. Every settled
or integrated topic must also appear in the outcome guide. During active work,
pass `--pending-topic <topic>` for each explicitly pending integration/outcome;
this exception does not excuse missing subject links. Remove the exception
and run the default check after recording its verified integration or settled
stop. The checker reports pending exclusions; it does not infer completion
from status prose or certify Git integration evidence.

Run `python3 tools/docs/check-work-metadata.py` for the Markdown/JSON metadata
check. It applies to all maintained documentation and evidence files, with
narrow source exceptions for dependency revisions and publication dates.
Neither navigation nor metadata checks require earlier Git history.

### Portable documentation metadata

Do not embed local Git commit IDs, work dates or timestamps in maintained
Markdown or structured verification records. Use named milestones and, when
ordering matters, document-local stage/checkpoint numbers. These are navigation
labels, not reconstructed dates, Git revisions or cross-document identifiers.
Record commands, results, assumptions and limitations instead of requiring a
local revision ID to understand the evidence. Do not add Base commit fields.

Exceptions are external dependency revisions and content checksums; publication
dates and source versions; and required license or attribution metadata.
No document is exempt merely because it was retained from an earlier layout.
No Git history rewrite is implied by documentation cleanup.

## Documentation During Work And At Completion

Keep plans, investigations, alternative assumptions, decisions, progress and
checkpoint verification in `docs/topics/<topic>/`. Unproved expectations and
proposed scope changes belong there, not in the assumptions ledgers as results.

Update the relevant `ASSUMPTIONS.md` during work at verified milestones,
normally alongside coherent commits; do not wait until the whole topic ends
or update it for every intermediate edit. Record the actual inputs and scope
of implemented, verified theorems, including added or removed hypotheses,
explicit external literature premises and application limits. A conditional
theorem must remain conditional: verification of an implication does not
establish its premise. Link to detailed dossiers and Lean declarations rather
than duplicating proofs or progress narratives. Keep unaffected entries intact.

At completion, write or update the relevant proof dossier from the completed
result's perspective: statements, hypotheses, proof structure, applicability,
limits, citation roles and verification. A feasibility/refutation endpoint must
be identified as such, not presented as the originally hoped-for theorem.
One topic need not correspond to one new dossier; update an existing dossier
for an extension or cross-link several dossiers for a cross-layer result.
Retain the completed topic record with its outcome and links to the dossiers.

Before marking the endpoint complete, check agreement between the Lean theorem
statements, proof dossiers and assumptions ledgers. Completion does not authorize
changes to the root README or a merge into `master`; those require user direction.

## Topic Record

### Literature Coverage Maintenance

For topics comparing literature candidates or claims, maintain the relevant
row under [docs/verification](../verification/README.md) at verified milestones,
when hypotheses/conventions change, or when source attribution is corrected.
Record a pinned source/location, target, verified claim, conditions/limits and
evidence links. Keep the ledger short and in English; dossiers own theorem
details and topics own investigations, commands and build history. Do not
duplicate those records or register new build baselines through index edits.

Before completion, check agreement between the coverage row, dossier and actual
theorem statement. General results without a literature comparison need no
row. Pending research belongs in topics. The index is not a global task list;
maintaining it does not authorize additional sectors, foundational work or
claims of paper-wide/software-wide verification. Do not report a coverage
percentage without a defined source-wide inventory.

### Topic Metadata

Start from [the template](../topics/TEMPLATE.md). Record:

- ID/title, status (`planned`, `in-progress`, `blocked`, `deferred`, `completed`).
- Working branch and integration target; leave these unassigned for a merely
  proposed topic instead of inventing branches.
- Endpoint, hypotheses, motivation, finite deliverables and non-goals.
- Open obligations and the exact next action, or an explicit stopping decision.
- Result type: proved, conditional, refuted, feasibility decision, or documentation.
- Verification commands/outcomes, limitations and integration evidence linked
  to the relevant topic record.

Completion means that topic's acceptance gate passed, not that every related
question was solved. A deferred proof is not a proved theorem. Completion and
integration are separate: a completed topic can still await a merge.
Git ancestry is authoritative for integration, not a copied status field that
would immediately become stale on merge. Record the target and actual
integration outcome after success (or explicitly report an outstanding merge). Local Git IDs belong in Git or conversation,
not maintained documentation.

Keep the overview about 100-150 lines or less. Before it grows, split by
subproblem or bounded milestone into sibling Markdown files/subdirectories.
Put only a short outcome and link in the overview; do not append every session
transcript. A materially different objective gets its own topic and branch.
Do not split files merely to reset an exhausted investigation bound.

## Resume Protocol

1. Inspect Git status, branches and the topic record.
2. Resume on its recorded branch. If no top-level branch exists, wait for the
   user's branch direction; do not create one from `master` implicitly.
3. Read only the linked proof/implementation dossiers and relevant sources.
4. Consult old completion/review logs only to answer a specific historical question.

For Lean source discovery and proof-state inspection, follow the
[Lean tooling workflow](LEAN_TOOLING.md): use `rg`, source inspection and
targeted `lake env lean` / `lake build` checks. The user has disabled the
Codex Lean MCP integration; do not use `lean-lsp-mcp`, probe its availability,
start/reconnect a server or repair the integration unless explicitly requested.
Do not repeatedly report its absence. This policy does not disable the user's
editor LSP or change the build and axiom-audit verification gates below.

## Endpoint And Stop Gate

Before implementation specify the endpoint/consumer, frozen assumptions,
required inputs, finite interfaces/tests, allowed routes and exit condition.
Distinguish necessary inputs from prerequisites of one possible construction
and from optional extensions. Record resource caps only if actually specified.

For feasibility work, default to one pass over at most two named routes,
without implementing new foundations. For a proof package, helpers may stay
inside the agreed interfaces. A new theorem-level prerequisite needing a
separate milestone is a plan change, not an automatic next task.
Freeze unresolved theorem-level prerequisites before coding. A failed route
cannot restart the investigation budget by renaming or splitting the task.

Stop for approval before changing physical scope, dependencies, the agreed
external-mathematics boundary, or reopening deferred foundations. User absence
is not consent. Save partial work and name the blocker. At each checkpoint
report closed/open endpoint inputs and evidence, not merely lemma counts.

A coherent commit is a checkpoint, not a default stopping condition. Unless a
user decision, new authority or scope change is required, continue autonomously
through the recorded endpoint, its verification and further coherent commits.
Large accumulated context should be compacted or summarized while preserving
the topic record and current proof state; context size alone is not a reason to
stop or return an unfinished topic to the user.

The project is limited to exact symbolic/algebraic formalization and bounded
repository-scale computational checks. RGE evolution, nonperturbative QCD or
hadronic matrix elements, lattice/Monte Carlo computation and numerical
simulation requiring more than lightweight reproducible scripts are outside
scope. A topic may expose such information as a documented external input, but
must stop its claimed result before the excluded calculation. Do not introduce
dedicated computing environments or dependencies for that work.

## Branch Lifecycle

1. The top-level integration target is `master`, despite informal references to
   `main`; do not rename it. Creating a top-level topic branch from `master`
   requires explicit user direction, as does merging one back into `master`.
   Topic approval, completion and verified commits do not imply either action.
2. When directed to create the top-level branch, use `proof/`, `audit/`, `docs/`
   or `refactor/` plus a short topic ID. Never reset an existing branch of the
   same name. Reuse a recorded branch when resuming its topic.
3. Record the working branch and target. A child task on an unmerged parent branch
   must say so and merge back there; it must not incidentally integrate its parent.
   Bounded child branches may be created and merged into that non-`master` parent
   at agent discretion.
4. Work and commit per verified milestone. For parallel work use separate
   worktrees, not simultaneous branch switching in a shared worktree.
5. At the endpoint, review the full diff, assumptions, dependency pins and tests.
   If the intended target advanced, integrate/test its changes on the work branch
   before a user-directed integration.
6. Commit the verified endpoint. Merge a top-level topic into `master` only on
   explicit user direction, with `git merge --no-ff <topic-branch>`, and repeat
   relevant checks on the merged state. Resolve only understood conflicts;
   otherwise preserve work and report the blocked integration. Child-topic merges
   into their recorded non-`master` parent do not require separate user direction.
7. After the merge and merged-state checks succeed, record the topic outcome
   in `docs/topics/_history/`, then delete the local topic
   branch with `git branch -d`. First confirm its HEAD is reachable from the
   recorded integration target, no worktree checks it out, and no pending child
   work needs it as an integration target. Switch away before deletion. Retain
   it if these conditions fail, and report the reason; do not use force deletion.
   Keep the historical branch name and integration outcome in the topic record.
   To reopen a completed topic, create a new branch from the current integration
   target with user direction. Remote branch deletion, remote pushes, force
   updates and history rewrites require separate authorization. Report topic
   and merge commits and whether local branch cleanup succeeded.

## Worktree Safety And Cleanup

Before integration or worktree cleanup, run `git worktree list --porcelain`.
Check whether the target branch is already checked out in another worktree;
do not bypass that protection with an ignore/force option.

For each explicitly selected obsolete worktree:

1. Inspect tracked, staged and untracked changes with `git -C <worktree> status
   --short`; check ignored files for unique user data as well.
2. Confirm its HEAD is retained by a branch/tag or reachable from the intended
   integration target. A detached HEAD alone is not evidence of expendability.
3. Remove only the resolved worktree path with `git worktree remove`, without
   `--force`. Stop on dirty files, unretained commits or uncertain ownership.
4. For missing directories, inspect `git worktree prune --dry-run --verbose`
   before pruning stale metadata. Do not delete a live worktree's metadata.
5. Recheck the worktree list and main worktree status. Report removed paths and
   retained refs. Worktree removal alone does not authorize branch deletion;
   post-merge branch cleanup follows the lifecycle conditions above.

Cleanup needs explicit user direction. Never recursively delete a workspace
root or use a broad temporary-directory glob. Ignored build caches may be
discarded only when identified as reproducible, not merely because ignored.

Proof acceptance requires focused builds, strict axiom audits and full `lake build`.
Documentation acceptance requires link and diff checks and an explicit skipped-build
statement. Documentation changes do not create a new Lean verification baseline.
Record failures honestly. Never weaken the audit to obtain a successful merge.

## Computational Cross-Checks

Computational tests supplement Lean builds and strict axiom audits; a passing
script is not a Lean proof, a trusted oracle, or evidence for cases outside
its tested domain. Distinguish exact finite calculations from numerical or
sample-based checks in both the test description and the reported result.

- Keep reusable scripts and test inputs in source control. Document their
  purpose, covered definitions/conventions, limitations, dependencies and
  execution command in the owning topic or a nearby tools README. Keep
  disposable output out of source control.
- Rerun the relevant tests when their corresponding definitions, sign or
  normalization conventions, coefficient constructions, input data, test
  implementation or execution dependencies change. Include them in audits
  of the covered result and in its pre-merge/merged-state verification.
  Unrelated changes do not require running every computational test;
  documentation-only edits follow the documentation acceptance rule above.
- Record commands, outcomes and unexecuted checks with reasons in the owning
  topic's verification section. If sampling is used, record its domain,
  bounds and seed where applicable; never report sampling as exhaustive.
- If a test fails or disagrees with Lean, investigate the correspondence of
  assumptions, definitions, conventions and implementations. Do not infer
  that either side is automatically correct, weaken a test merely to pass,
  or integrate the affected result with the discrepancy unresolved. If a
  required test cannot run, report that verification gate as outstanding.
- When correcting a test or expected result, document why the old expectation
  was wrong and retain an appropriate regression control. A computed identity
  used as a premise of a formal theorem must still be proved or verified inside
  the accepted Lean trust boundary, not imported as an unchecked assumption.

For example, the [qque statistics audit](../topics/qque-lorentz-statistics/README.md)
records the exact one-generation Grassmann expansion test and its limited
relationship to the Lean exterior-power probes. Changes to the covered qque
contraction or exchange-sign conventions require rerunning that check.

## Documentation retention

Keep a technical topic when it explains proof verification, dependency changes,
source ownership or mathematical provenance. Pure editorial reorganizations,
obsolete tooling trials and local scratch cleanup need no separate topic once
current guidance and any relevant technical evidence have been absorbed.
See [distribution and attribution](DISTRIBUTION.md) for licensing context.
Retiring a topic removes its navigation/outcome entries; it does not weaken
proof qualifications or authorize deleting source proofs and audit evidence.

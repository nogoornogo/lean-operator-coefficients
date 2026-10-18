# Verification

## Planning Checkpoint — stage 01

Documentation only: topic overview, frozen staged plan, source register and
navigation link. No Lean sources, theorem hypotheses, dependencies or audit
allowances changed. No Lean build or axiom audit rerun; this is not a new proof
verification baseline.

- `node tools/docs/check-links.mjs`: passed; 622 Markdown files, 3,911 local
  inline links, 91 heading fragments, zero errors. The initial sandboxed
  invocation failed with `spawnSync git EPERM`; the same read-only command
  passed on an approved unsandboxed retry.
- `git diff --check`: passed; staged diff check also required before commit.
- New topic files and navigation diff reviewed against the requested scope.
- No merge or remote push authorized or performed.

## Scoped Proof Endpoint — stage 01

Stages A/B and the elementary Stage D evaluation interface/examples are proved.
The bounded Stage C and general Stage D feasibility passes reached the frozen
foundational stop; neither general literature theorem is claimed.

- Focused builds of the six new source modules passed. Final focused audit:
  `lake build Math.RepresentationTheory.Audit.AuditSymmetryProtection` passed
  (3,772 jobs), including 46 strict transitive checks and layer-origin checks.
- `lake build` passed (6,665 jobs). The full build log contains no `warning:`
  diagnostics. Existing audit output was replayed by Lake as appropriate;
  this is a full aggregate build, not a claim to rebuild every cached dependency.
- `node tools/layout/check-layout.mjs` passed: 1,338 modules; layer, local
  import, cycle, aggregate coverage and relocation checks OK. The first new
  audit diagnostic lacked the required original-module annotation; adding
  `SourceLayout.originalModule` fixed that layout failure without changing
  axiom policy or layer restrictions.
- `node tools/docs/check-links.mjs` passed: 626 Markdown files, 3,928 local
  inline links, 91 heading fragments, zero errors. A final sandbox invocation
  hit `spawnSync git EPERM`; the identical read-only approved retry passed.
- `git diff --check` passed; final staged check also passed before commit.
- Reviewed the independent actions, restriction squares, scalar descent,
  coefficient-dual orientation, product/finite-support distinction and actual
  stabilizer target against the frozen plan. No `sorry`, custom axioms,
  dependency changes or audit exceptions were introduced.
- Updated the assumptions dossier, current proof dossier, literature register
  and topic results. No literature comparison certificate is asserted for
  the deferred geometric conclusions. No master merge or remote push performed.

## Master Integration — stage 01

User explicitly authorized integration. `master` remained at the recorded base;
`git merge --no-ff proof/all-degree-symmetry-protection` produced `checkpoint 01`,
retaining verified topic commit `checkpoint 02`. An initial invocation lacked a
committer identity; the retry supplied the existing identity per command.

- Merged-state `lake build`: passed, 6,665 jobs, including the replayed 46 strict
  symmetry-protection checks; no warning diagnostics in the build log.
- Layout check: passed, 1,338 modules.
- Documentation link check: passed, 626 Markdown files, 3,928 local links,
  91 heading fragments, zero errors. Diff and staged whitespace checks passed.
- Integration record changes are documentation-only; no additional Lean build
  was rerun after those record edits.
- Topic HEAD is reachable from `master`; no worktree uses the topic branch and
  no child branch depends on it. Local topic branch deleted with `git branch -d`.
- No remote push or remote branch deletion performed. General friendship and
  saturation remain deferred at the recorded feasibility boundaries.

## Adopted Terminology — stage 01

User authorized the proposed names and documentation update, including the
reader-facing theorem title. Adopted names (recorded here in English):

- All-degree coefficient-space decomposition theorem for derivative-free
  operators (short: all-degree coefficient-space decomposition theorem).
- Coefficient-space symmetry-extension criterion (necessary and sufficient).
- All-degree charge selection rules (sufficient obstruction).
- Four-sector coefficient classification for the earlier bounded application collection.

Updated the root introduction, current dossiers/assumptions, navigation and
related topic descriptions. Kept file paths, Lean declaration names and the
Lake package identifier unchanged; historical checkpoint records are retained.
Documentation-only: no Lean build or axiom audit rerun. Local link check passed
(626 Markdown files, 3,929 links, 91 fragments); sandbox `spawnSync git EPERM`
was resolved by the identical approved read-only retry. Diff and staged
whitespace checks passed. No theorem statements or hypotheses changed.

## README Main-Result Presentation — stage 01

User authorized presenting decomposition, symmetry extension and charge
selection as the three main results, with the conditional ΔB=1 model
constraints as a secondary application. Updated only the README and this
record. The constraint summary retains actual embedding/mass and shared
irreducible surplus hypotheses; scalar copy-count surplus is a specialization,
not an arbitrary-action dimension criterion. Nonzero symmetry-allowed qque is
kept separate from generation and decay. General friendship/saturation remain
unproved. No Lean build or axiom audit rerun for this documentation-only change.
Local link and whitespace checks passed before commit.

## Sector Application Heading — stage 01

User approved retaining the four examples under “Verified Sector Applications”
and explicitly stating that they do not exhaust the main theorems' scope.
Updated the README heading/introduction; the classification table is retained.
Documentation-only; no Lean build or axiom audit rerun. Local links and
unstaged/staged whitespace checks passed before commit.

## English Documentation — stage 01

User requested English throughout repository documentation. Replaced Japanese
name annotations in the README, current proof dossiers and terminology record
with English names. A repository Markdown scan found no remaining Japanese
text. File paths, Lean declarations and theorem content are unchanged.
Documentation-only: no Lean build or axiom audit rerun. Local links and
unstaged/staged whitespace checks passed before commit.

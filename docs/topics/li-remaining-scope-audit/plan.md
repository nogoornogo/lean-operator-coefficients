# Investigation Plan

## Frozen Objective

Use the pinned 2201.04639v2 primary text and existing repository interfaces
to select bounded verifications and complete their implementations and audits,
or recommend deferral. Claims about
paper contents must be checked in the primary source, not inferred from
abstracts, prior LLM reviews or the current coverage ledger. The user's scope
extension authorizes implementation of all recommended bounded candidates.

## Phase 1: Source Map

Recover the pinned PDF or author source and record version and provenance.
Read the contents and relevant construction/example/appendix passages.
Separate general mathematical claims, worked candidates, finite counting
claims and executable-software claims. Mark whether a passage was inspected
in full, skimmed or not read. Retain exact source locations and resolve
symbolic tables visually if extraction loses indices or signs.

Produce `source-map.md`. Map major groups once; do not claim an exhaustive
inventory of individual formulas or any coverage percentage. If the pinned
source cannot be recovered reliably, record the gap and stop attribution
rather than substituting another version silently.

## Phase 2: Existing-Asset Match

Screen the mapped groups against the verified comparisons and existing
derivative-free/statistics/invariant-Hom infrastructure. Candidate searches
must use `rg` and inspect declarations and their hypotheses, not just filenames.

Use five categories in `candidates.md`:

| Category | Required evidence |
|---|---|
| Existing API | Named inspected declarations provide the required interfaces; dictionary/transport work is identified |
| Small helper | A finite list of local lemmas with precise statements; no new theorem-level foundation |
| New foundation | A missing theorem/interface requires a separate proof milestone |
| Excluded | Endpoint crosses the agreed physical/computational boundary |
| Unresolved | Insufficient primary-source or API evidence; no feasibility assertion |

For each selected row state the source location, comparison claim, supplied
representations/dimensions/conventions, independent target space, existing
declarations and remaining obligations. Distinguish a supplied-invariance
transport theorem from actually classifying gauge/Lorentz invariants.

Prioritize targets with a different statistical or invariant structure from
the six existing comparisons, an explicit inverse/independence/span endpoint,
and little new infrastructure. Additional examples of the same structure are
secondary. “Small” must describe the interfaces needed, not promise elapsed
time or successful proofs.

## Phase 3: Bounded Selection

Perform one source/API screening pass. Candidate count follows the evidence,
without a numerical quota. Inspect at most two named construction routes per
target. If a route requires a prerequisite, assess its size and effect on
existing decisions. The user's further authorization allows bounded new
helpers and foundations at agent discretion. Defer large foundational
projects or changes conflicting with existing decisions, and record why.

Targeted read-only `lake env lean` probes may check existing elaborated types
when source inspection is insufficient. Keep scratch output outside version
control and distinguish such probes from proof acceptance. No audit
exceptions, software environments or dependency changes.

Produce `recommendations.md` with the selected proposed statements and their
assumptions, reusable interfaces, missing lemmas, literal-source dictionary
obligations, focused audit plan and stop conditions. A failed-feasibility or
deferral recommendation is an acceptable result. Freeze this finite selection
before implementation; do not recursively add targets discovered while coding.

## Phase 4: Implementation And Acceptance

Implement the selected candidates using the inspected existing interfaces and
bounded local helpers. Keep the target space independently defined, and prove
the actual source dictionary, inverse/span/independence claim as applicable.
Register sources and persistent strict transitive axiom audits in aggregates.
Run focused builds and audits, the layout check, full `lake build`, documentation
links and `git diff --check`. Record actual commands and outcomes. At verified
milestones update proof dossiers, assumptions and the English coverage ledger;
commit coherent checkpoints and continue through the selected set.

## Stop And Handoff

The normal stopping condition is audit completion for every recommended
candidate. Stop earlier if source provenance, physical conventions or
an endpoint-changing hypothesis needs user judgment. Bounded prerequisite
development is authorized when it preserves existing decisions and is not a
large new project; record its scope and verify it normally. No reopening six-quark
counting or large general p/y/m/j development,
derivative/EOM/IBP foundation, amplitude equivalence, matching, RGE or rates.

Unproved findings remain in this topic. Update the cross-topic coverage index
at verified proof milestones or corrected attribution; do not convert a merely
assessed target into a verified comparison. At completion, record
inspected/uninspected scope and actual verification commands, review the
statements and assumptions, and commit the verified package. Master merge
still requires explicit authorization.

# Verification

- Focused `lake build GUT.SU6.Audit.AuditLightPlacementObstruction`: passed,
  4309 jobs; two strict transitive checks permitting only propext,
  Classical.choice and Quot.sound. No new warnings.
- Serialized full `lake build`: passed, 6702 jobs, on this master-based branch.
  The separate Dev–Mohapatra branch's larger build baseline does not apply.
  Existing diagnostics replayed; no new-source warning. Disposable output:
  `/tmp/su6-light-placement-build.log`.
- `node tools/layout/check-layout.mjs`: 1375 modules, all checks passed.
- `node tools/docs/check-links.mjs`: final pass recorded below; an initial
  check correctly reported this not-yet-created verification file missing.
- `git diff --check`: passed.
- Assumption review: generated Yukawas, fixed scalar/VEV and zero bare mass
  are the existing input family. The new result is actual radical inclusion
  and an exact-radical obstruction, not an arbitrary-H protection theorem.
  No external paper, new axiom, pins, rate computation or master integration.
- No computational script rerun: no mass/action definitions changed and the
  new statements are direct audited Lean consequences of existing theorems.

Final documentation check: 679 Markdown files, 4170 local links,
92 heading fragments, zero errors.

## Four authorized bounded changes

- `python3 tools/su6-light-placement-search/check_four_directions.py`: four tests passed. Six rank-12 coordinate masses, 29 hypercharge-allowed upper-triangular entries with ten forced-zero rows, 512 selected Z4 charge/placement cases (56 pass selected gates, 24 split, zero qque-charged), one 57-field rank-42 mass, and the independent-phase qque control/failed E03 root-diagonal UV gate checked exactly.
- Reused controls: `python3 tools/su6-twisted-protection/audit_block_phase.py` passed six tests; `python3 tools/qque/audit_one_generation.py` passed four tests.
- `node tools/docs/check-links.mjs`: 682 Markdown files, 4177 local links, 92 fragments, zero errors. `git diff --check`: passed.
- No Lean source or theorem dependency changed in this phase; no Lean build or new axiom audit was rerun. The preceding 6702-job proof baseline is unchanged. Computational results are explicitly not Lean certificates or formal theorem premises.
- Scope review: maximal scalar test is a hypercharge mass screen, not a chosen small scalar/VEV model. Enlarged-field count is selected ten-sector admission, not 56 UV models. Independent-phase action passes finite broken-phase gates and forbids the named qque polynomial, but fails only the specified root-diagonal inner covariance gate. No general automorphism exclusion or all-B1 certificate is inferred.

## New Z5 pattern-search validation

- `lake build GUT.SU6.Audit.AuditCyclicPatternSearch`: passed (3784 jobs), eight strict transitive checks with only propext, Classical.choice and Quot.sound permitted. New source/audit emitted no warnings.
- Serialized `lake build`: passed (6704 jobs), on this branch. Existing diagnostics replayed. Disposable output `/tmp/su6-pattern-search-build.log`.
- `python3 tools/su6-light-placement-search/check_z5_patterns.py`: all 125 triples checked, twenty matches (four neutral-Higgs, sixteen charged-Higgs); arithmetic equalities and positive/negative controls passed.
- Layout: 1377 modules, all checks passed. Documentation: 684 Markdown files, 4184 links, 92 fragments, zero errors. `git diff --check`: passed.
- Assumption review: generic iff explicitly takes genuine scalar representations and nontrivial carriers. Character-line instance is a real mathematical example, not a physical qque/LLHH identification. Search counts are not Lean-proved. No claim of all-degree B1 prohibition, anomaly-free Z5, or SU(6) UV realization. Prior Z4 tests are not recycled as the new application.
- Existing matrix/Grassmann scripts not rerun: their definitions and dependencies are unchanged. No new literature input, dependency change or master integration.

## Z5 orbit reduction and SU(6) screen

- Focused `lake build GUT.SU6.Audit.AuditCyclicPatternOrbits`: passed (3785 jobs); six strict transitive checks with only propext, Classical.choice and Quot.sound. No new warnings. The ZMod prime fact is proved by decide, locally scoped; no new axiom.
- Serialized `lake build`: passed (6706 jobs); existing diagnostics replayed. Disposable logs `/tmp/su6-orbit-focused.log` and `/tmp/su6-orbit-build.log`.
- `python3 tools/su6-light-placement-search/check_z5_orbits.py`: reruns the original census, checks five disjoint four-element orbits covering twenty inputs, exactly one normalized representative in each, zero fits against 125 scalar/block phase inputs for each representative, and charge-level hypercharge-dressing connectivity. Positive neutral fitting control passed.
- Layout: 1379 modules, all checks passed. Documentation: 686 Markdown files, 4191 links, 92 fragments, zero errors. `git diff --check`: passed.
- Review: orbit counts are computational, generic selected-charge identities and no-fit are Lean-proved. Generator-change equivalence is the declared quotient. Hypercharge dressing is explicitly a second charge operation, not an unsupported full UV-model equivalence. Physical carrier admission and changed-placement realization remain open. No new literature, dependency change, numerical physics or master integration.

## Reverse-placement feasibility

- Focused `lake build GUT.SU6.Audit.AuditChargeProfileObstruction`: passed (3786 jobs); three strict transitive checks, only propext, Classical.choice and Quot.sound permitted. No new warnings.
- Serialized `lake build`: passed (6708 jobs); existing diagnostics replayed. Disposable log `/tmp/su6-charge-profile-build.log`.
- `python3 tools/su6-light-placement-search/check_small_branching.py`: passed complete-character decomposition/reconstruction and named dimensions, conjugate decompositions, neutral-SM positive index control and all five normalized target-index tests. Each 35-column coefficient system has rank 24 and inconsistent augmented system. Exact Fraction elimination; no numerical tolerance or sampling. Disposable output `/tmp/su6-small-branching-results.txt`.
- Layout: 1381 modules, passed. Documentation: 688 Markdown files, 4198 local links, 92 fragments, zero errors. `git diff --check`: passed.
- Scope review: selected small-representation pool, uniform scalar copy charges, fixed embedding and one-generation exact chiral target. Complete spectator characters are included. This is a computational necessary index screen, not actual mass existence or a Lean branching equivalence. The separately audited profile lemma is conditional and does not certify the numerical character matrix. No external literature premise, dependencies, anomalies, rates or integration added.
- Earlier scripts not rerun because their inputs/definitions did not change; the new script has its own neutral-spectrum positive control. The tentative expectation for the 70 component count was corrected during implementation to (2,1,1), as established by full-character reconstruction; no scalar weight was used as an irrep certificate.

## Lean finite-index obstruction certificate

- Focused `lake build GUT.SU6.Audit.AuditFiniteIndexCertificate`: passed (3787 jobs); 16 strict transitive declaration checks permitting only propext, Classical.choice and Quot.sound. No new warnings.
- Serialized `lake build`: passed (6710 jobs), existing diagnostics replayed. Disposable log `/tmp/su6-finite-index-build.log`.
- Finite target dictionary, all annihilation equations and target separation are proved by `decide +kernel`, not native_decide. No-solution follows by finite linear algebra for every rational coefficient assignment. An initial norm_num enumeration timed out; it was replaced by kernel decision without raising heartbeats or adding axioms.
- `PYTHONDONTWRITEBYTECODE=1 python3 tools/su6-light-placement-search/check_small_branching.py`: all character/index checks passed again.
- `PYTHONDONTWRITEBYTECODE=1 python3 tools/su6-light-placement-search/check_lean_index_data.py`: exact static branching and target tables match the independent character calculation; 175 annihilation and five separation controls passed. Neither script is a Lean premise.
- Layout: 1383 modules, passed. Documentation: 690 Markdown files, 4206 local links, 92 fragments, zero errors. `git diff --check`: passed.
- Scope review: explicit finite branching data and mass-index admission remain the model dictionary. The theorem certifies matrix nonexistence, not continuous SU(6) branching equivalences or a new physical radical. No custom axiom, audit exception, dependence change, physical rate or integration.

## Actual physical radical-index connection

- `lake env lean GUT/SU6/SelectionRules/Models/PhysicalIndexObstruction.lean`:
  initial source elaboration passed after qualifying the actual SU(6) subgroup
  namespace and removing unused simp arguments.
- `lake build GUT.SU6.Audit.AuditPhysicalIndexObstruction`: passed, 4200 jobs;
  10 strict transitive checks, only propext/Classical.choice/Quot.sound allowed.
  Includes genuine cyclic-character injectivity and kernel-decided correspondence
  to all five earlier finite light-profile charge lists. No new warnings.
- `lake build`: passed, 6712 jobs. Existing diagnostics replayed; no new warnings
  in the new source or audit. Focused and full builds were serialized.
- `node tools/layout/check-layout.mjs`: 1385 modules; passed.
- `node tools/docs/check-links.mjs`: 692 Markdown files, 4222 local inline links,
  92 heading fragments, zero errors. The first sandboxed invocation encountered
  EPERM starting its git subprocess; the same read-only check passed with the
  permitted execution context.
- `git diff --check`: passed.
- Branch tables and Python computational definitions were unchanged; their
  scripts are not premises of the new actual-representation theorem.

Assumption review: actual product-group representation, standard physical
embedding, invariant symmetric restricted mass, and the requested infrared
radical dual target are explicit. Charge-profile equality and mass-index
preservation are derived. Individual 20/21/35/70 branching equivalences are
not claimed; they are unnecessary for this alternative exclusion certificate.
No dependencies, custom axioms, audit exceptions, merge or push introduced.

## Master integration

User-authorized no-ff merge: checkpoint 02, topic checkpoint 01.
The target had not advanced beyond the recorded base; no conflicts occurred.
Merged-state lake build passed (6712 jobs), including persistent strict
transitive audits. Layout passed (1385 modules). All five exploration scripts
passed, including the four-direction tests and the independent Lean data
checker. Local links passed (692 Markdown files); git diff --check passed.
The historical topic branch has no child branches or checked-out worktree
and its HEAD is reachable from master; local branch cleanup follows the
repository workflow. No remote push or unrelated worktree cleanup is included.

## Input-axis applicability inventory

Documentation-only follow-up requested after integration: residual action,
embedding, and light/mass evidence are mapped to existing theorem routes.
This adds no proof, model partition or automatic classifier. Reviewed against
StandardChain, the SU6 physical endpoint, current GUT assumptions, partial
conjugation targets, full light-species classification, compact light qque,
and species copy-surplus dossiers. Local links passed (693 Markdown files,
4241 links before this verification entry); git diff --check passed.
No Lean build was rerun; no new proof verification baseline is claimed.

## Proof-route inventory structure correction

Following the shared review, the applicability document now separates
ambient/index routes, actual-field routes, the unresolved covariant-action
route, and inputs lacking evidence. R1–R7 retain the old row correspondence.
Completed physical adapters are distinguished from model-specific dictionaries;
no claim of a disjoint or exhaustive partition is made. Documentation only:
links passed (693 Markdown files, 4244 links), git diff --check passed.
No Lean build was rerun and no proof verification baseline changed.

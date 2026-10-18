# B1 minimum attempt: verified partial intervals and resource stop

This report describes the earlier stopped checkpoint. The subsequent
[bounded connection revision](../sm-b1-weak-connection/results.md) verifies
a split weak-envelope proof and closes all 326 minima. The measurements and
partial claims below retain their original checkpoint meaning.

## Outcome and boundary

The full 326-minimum endpoint was **not achieved**. The planned 10 GiB
sampled process-group RSS guard interrupted the strengthened lower-bound
connection at 69.9 seconds and 10496820 KiB. No guard, heartbeat option,
dependency or audit exception was raised. Further work on that route stopped.

The retained result supplies actual upper-bound witnesses and universal
lower bounds for all 326 all-degree-allowed B1 assignments. Among them,
160 have matching bounds and therefore exact global minima; 166 remain
nontrivial intervals. The 246 all-degree-forbidden assignments retain None,
not a numerical minimum. The original 572-row identity domain is unchanged.

| Engineering-dimension interval | Rows | Interpretation |
| --- | ---: | --- |
| [6,7] | 48 | unresolved by retained certificates |
| [9,9] | 98 | exact minimum nine |
| [10,10] | 62 | exact minimum ten |
| [12,14] | 28 | unresolved |
| [12,15] | 16 | unresolved |
| [15,19] | 16 | unresolved |
| [15,20] | 10 | unresolved |
| [18,24] | 28 | unresolved |
| [18,27] | 10 | unresolved |
| [21,31] | 10 | unresolved |

The exact/interval totals are Lean kernel results; the detailed interval
grouping above is the retained diagnostic output, reproducible with the
script below. Every row's actual bound semantics are proved in Lean. The
grouping is not a supplied verdict table or a proof premise.

## What the retained proofs say

`SMB1DimensionBounds` proves the independent-left-chirality consequence and
the engineering-grade congruence
`(twiceDimension - 3*B3 + L) % 4 = 0` for every actual allowed original
content. Its retained `lowerGrade L=3*(3+abs(L))` is deliberately conservative.
The normalized candidate preserves actual absolute lepton charge and the
grading bound; no source-conjugation premise is assumed.

`SMB1DimensionProposals` proves eight new explicit full joint supports using
balanced occupations and the first live component. All eight passed their
single support probe. `SMB1DimensionWitnesses` reconnects these and the other
ten selected old/small families to actual original spaces at **specified
grades** for all 18 normalized B1 charges. An ungraded existential theorem
is not substituted for a graded upper bound.

`SMB1MinimumClassification` minimizes the proved charge lower grades and
the selected actual witness grades separately over the finite neutral
charge set. Its row lower bound also incorporates the already proved
below-ten prohibition when applicable. `row_certificate` supplies, for
every allowed row, an attained original upper grade U and a bound L for
all original selected contents, either baryon sign and all Higgs bidegrees.
`row_exact` yields `IsMinimum` only when these values agree.

The kernel checks interval consistency and None/flag agreement for every
row and proves 160 exact and 166 unresolved entries. `exact_check_semantics`
connects the counted exact class to actual minimum certificates. None for
the upper minimum is equivalent to all-degree prohibition, using the
existing exact finite-charge theorem. No unknown numerical minimum is
silently replaced by a default zero.

## Diagnostic inventory and stopped route

The [pre-gap inventory](inventory.md) records the initial 160 matching and
166 nonmatching proposed intervals, before testing new templates. The
diagnostic script uses standard-library Python and reads the old Lean
witness declarations; it never writes proof inputs or calls a solver.

```sh
python3 tools/structural-support/b1-minimum-inventory.py --rows
python3 tools/structural-support/b1-minimum-inventory.py --retained --rows
```

The second command prints the complete retained 326-row inventory and its
exact unresolved keys. `--refined` is explicitly an **unverified** proposal:
its apparent 326 matching rows depend on the stopped weak-envelope proof.
It must not be quoted as a proved classification. The retained and refined
lower-bound recipes differ; conservative retained intervals can be wider
than the unverified initial proposal despite improved upper witnesses.

The proposed strengthening is `abs(7*L-B3) ≤ 12+twiceDimension`, using the
existing complementary weak-capacity API, combined with grade congruence.
The interrupted build completed the new support-template module, then
stopped while checking the lower-bound module. It had no finer declaration
progress diagnostic, so the precise allocation bottleneck is not isolated.
There is no evidence here for optimizer miscompilation or for the necessity
of a new representation foundation.

The stopped source is retained only as
`tools/structural-support/probes/b1-weak-envelope-stopped.lean.txt` for review
and reproduction. It is **unverified**, outside active imports and audits,
and is not rerun automatically. Its proposed weak lower bound and apparent
all-row matches are excluded from the retained theorem claims.

## Failure accounting and verification

The first Python draft had a parenthesis SyntaxError, corrected before
inventory generation. Early lower-bound proof drafts failed on cast/bounds
elaboration (6.8 s, 5216916 KiB), then a deterministic 200000-heartbeat
limit in the combined proof (19.0 s, 5309952 KiB). A split draft still
failed the weak connection and finite arithmetic bounds (15.0 s,
5699748 KiB). No proof limit was raised. The next shared build hit the
external RSS guard as recorded above; this ended the strengthened route.

Post-stop work only verifies the retained partial artifacts. Two witness
connection drafts failed on negative-literal parentheses and casts (9.8 s,
5233512 KiB; 5.8 s, 5230492 KiB). The next retained build accepted witnesses
but rejected interval-wrapper elaboration/API details (23.3 s, 6232888 KiB).
Those acceptance errors were corrected without retrying the stopped route.
They are failures, not successful baselines or prohibition evidence.
An additional importing-example draft lacked an explicit dependent pattern
binder (21.5 s, 6239804 KiB including the accepted interval build); this
acceptance error was corrected without changing a mathematical statement.

Successful commands, source hashes, audits and resource measurements are
retained in [verification evidence](verification.json). New modules and
persistent strict audits are registered in Physics. Only propext,
Classical.choice and Quot.sound are permitted; no `sorry`, custom axiom,
`native_decide`, numerical/CSV premise or allowlist exception is accepted.

The accepted final retained checks are:

| Accepted check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Importing examples and persistent audit build | 7.0 | 5209892 |
| Direct audit re-execution: 288 strict transitive checks | 4.0 | 5126176 |
| Fresh importing consumer re-elaboration | 3.5 | 5087152 |
| Full default-root `lake build GUT`: 7358 jobs | 8.3 | 6698312 |

The full build has zero warnings/errors and includes the new persistent
audit alongside unchanged parent audits. Layout passes 1972 modules. Final
links pass 1006 Markdown files, 6106 links and 115 fragments, zero errors;
diff and retained-source policy checks pass. The unchanged read-only link
checker uses its permitted outside-sandbox retry for git subprocess EPERM.
The retained diagnostic is byte-identical across two runs, with unique keys
and the 326/160/166 counts matching the kernel classification. Existing proof
definitions, tables and dependency pins were untouched; unrelated optional
historical table regressions were not rerun.

These checks accept the retained partial library, not the stopped weak
source. No re-attempt of that source was made after the RSS stop.

## Stopping decision

This is a verified partial result plus a resource stop, not complete
exclusion for all 326 minima. Further attempts to optimize/restructure the
weak-envelope connection require a new bounded scope decision; this topic
does not silently restart its budget. Existing bounds or the arithmetic
proposal do not establish minimum dimensions for the 166 unresolved rows.
The other three user-selected follow-ups remain untouched. No root README,
master integration, remote push or physical scope change is authorized.

The verified partial checkpoint `checkpoint 01` was
[integrated into its recorded parent](integration.md) at `checkpoint 02`.
Fresh direct merged audit and full cached build pass. The local child was
safely deleted; no master merge or remote push occurred. This integration
does not resume or close the stopped 326-minimum objective.

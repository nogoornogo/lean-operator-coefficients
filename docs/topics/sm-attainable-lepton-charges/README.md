# Attainable finite SM lepton charges

- ID: `sm-attainable-lepton-charges`
- Status: completed
- Result type: proved
- Working branch (historical): `proof/sm-attainable-lepton-charges`; safely deleted after parent merge
- Integration target: `proof/sm-finite-charge-support`, not master; merged as `checkpoint 01`
- Parent exception: bounded child of the unmerged approved two-stage topic;
  merging into that parent is discretionary under WORKFLOW.md. This never
  authorizes merging the parent into master or a push.

## Endpoint And Frozen Interfaces

This is stage 2 of the [approved initial plan](../sm-finite-charge-support/plan.md).
Determine the attainable L sets for absolute B3=3/6 in the unchanged
three-generation, derivative-free signed SM dictionary, independent Lorentz
action and neutral-residual Higgs/dual. Candidate sets are
`R_b={L∈[-18,18] | (b+L)%2=0}`, specialized to b=3,6. They are upper bounds
until every member has an actual joint-support witness.

1. Prove per-content capacity, |L|≤18 and parity on actual nonzero original
   coefficients. Reuse SMContentCapacity and sum-by-species; no new exterior
   or representation foundation.
2. Positive route: retain the existing 23 families; test the remaining 14
   charges with explicit balanced occupation and first live joint branch.
   For a=|L|≥12, split leptons between doublets (12) and singlets (a-12).
   Proposed extra families use quark/antiquark pairs and the existing typed
   source dictionary. All proposals must pass kernel checks; a failed choice
   is not an exclusion. Permit a bounded alternate joint branch/occupation
   within these same families if the first branch fails.
3. Negative route: use only existing capacity, parity, hypercharge and
   weak/chirality filters. If proposals fail and these filters cannot settle
   a value, record it unresolved; do not exhaustively enumerate all contents.
4. For arbitrary k≠0,q,l, prove OriginalAllowed iff some L in the proved
   finite set solves `b*q+L*l=0`. For negative B3, normalize both charges by
   sign in the necessity direction. Positive-B3 witnesses suffice for the
   converse if every candidate is realized; then no representation-conjugation
   foundation is needed. Explicitly prove this arithmetic sign bridge.
5. Register committed witness and criterion modules in Physics and persistent
   strict audits. Recover the 572 results as fresh general-theorem corollaries
   and compare with the original certificates/CSV before replacing any path.

## Acceptance And Stop

One Lean process/build at a time; one thread, 300 s per run, 10 GiB sampled
process-group RSS and 4 GiB reserve, unchanged pins/options. Focused builds,
strict audits, full default-root build, layout/links/diff and exact table
comparison are required. Commit verified witnesses into the active library;
ordinary build/import must then protect the general criterion. Keep scratch
sources/logs in /tmp and measurements in the topic.

One pass over the positive and negative routes, no new foundational theory,
generic compiled solver, exhaustive content search, minimum dimension,
physical extensions or raised limits. If needed finish as a bounded
feasibility result with exact inner/outer sets and unresolved charges.
Proceed to parent integration after successful child verification, then check
the parent result. No master merge or publication is authorized.

## Work And Result

Both candidate sets are exact: all odd |L|≤17 at B3=3 and all even |L|≤18 at
B3=6. All 37 committed joint witnesses, the arbitrary-k,q,l exact/absolute
original-space equivalences, and the 572 committed assignment corollaries
are verified. The [results](results.md) and [machine-readable evidence](verification.json)
record focused/full builds, 1154 strict checks, original-certificate and
degree-bound cross-checks, failed attempts and boundaries. No candidate is
unresolved. Minimum operator dimension and UV/decay physics remain outside
scope. Child checkpoint `checkpoint 02` was integrated into its recorded parent
and that state was reverified; see the [integration record](../sm-finite-charge-support/integration.md).
No further child work remains. Master integration remains unauthorized.

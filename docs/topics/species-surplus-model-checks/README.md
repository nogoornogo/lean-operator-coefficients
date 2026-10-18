# Species Surplus: Three Model Rechecks

- ID: `species-surplus-model-checks`
- Status: completed
- Working branch: `audit/species-surplus-model-checks`
- Integration target: `proof/species-copy-surplus`
- Topic commit: `checkpoint 01`
- Parent integration: `checkpoint 02` (`--no-ff`), merged-state checks passed
- Local child branch removed after reachability/worktree checks; name retained here
- Branch exception: bounded child of the unmerged parent; child integration is
  authorized by repository workflow, not permission to merge the parent to master.

## Frozen Endpoint

Recheck the same pinned B/L, split SU(5) and minimal Pati–Salam dictionaries
against [the new theorem](../species-copy-surplus/result.md). For each action,
calculate species-wise source/target Hom surpluses for a common irreducible R,
check the source/opposite/rest pairing dictionary and original-mass invariance,
and distinguish theorem admission from coefficient generation.

Use two routes: supplied SM-sector decompositions and exact finite charge/mass
controls. No new UV representation foundations, quotient descent, simultaneous
UV coupling point, post-EW mixing or matching are opened. Full UV branching
remains literature data. Stop at an explicit application or obstruction on
these dictionaries, with conditions and exact checks documented. No new Lean
full-model admission theorem is required or claimed in this bounded recheck.

The [result](result.md) and [verification](verification.md) own this pass.

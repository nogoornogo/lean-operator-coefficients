# Exact Species Surplus Model Controls

Run `python3 tools/species-surplus-model-checks/audit_models.py` from the repository
root. Five deterministic tests use exact integers/rationals and Python's standard
library; the rational matrix helpers are reused from the parent topic.

Inputs are the pinned branching/charge dictionaries linked in the
[model recheck](../../docs/topics/species-surplus-model-checks/result.md).
SU3 irreducibles are labelled by Dynkin (p,q), SU2 by dimension and hypercharge
by 6Y. Opposite gauge labels swap p,q and negate Y. Residual entries label
all-left source and target copy actions; targets are duals of actual opposite
field sectors. Cyclic character Hom dimensions are counted by equal weights.

Checks cover full supplied split SU(5) branching dimension 375 and 3→2/3→2/1→0
copy counts; all 729 integer 2×3 masses with entries in {-1,0,1}; full versus
light parity; PS charged/neutral separation and all 27 small neutral symmetric
matrices; B/L charged exotics and common-constituent obstruction. Tests are not
Lean oracles, a proof of branching/Schur/NoPairings, or simultaneous UV parameter
points. Rerun when supplied dictionaries, conventions or matrix helpers change.

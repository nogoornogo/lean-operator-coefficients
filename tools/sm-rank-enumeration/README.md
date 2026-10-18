# Exact q/l recount

Run `python3 tools/sm-rank-enumeration/enumerate.py` for counts and the size
diagnostic; append `--csv` to reproduce [candidates.csv](candidates.csv).
The script verifies the committed CSV row by row, fixed-order orbit closure,
effective action image sizes, and all existing Lean count controls.

Orders 2 through 12 and `3q+l != 0` are exactly the domain of
`InverseCyclicSMCharges.candidates`. Orbit representatives are lexicographic
minima under simultaneous multiplication of q,l by a unit modulo k.
`bounded_b2_forbidden` and `bounded_llhh_forbidden` refer only to the previously
proved one-copy sector predicates (`6q != 0` and `2l != 0`). No column means
all-degree protection. No numerical complex rank calculation is used.

The CSV and Python assertions are reproducible external checks. They do not
introduce premises into Lean. The existing kernel-checked counts are in
`InverseCyclicSMCharges`, `InverseCyclicChargeOrbits` and
`InverseCyclicSectorProperties`; the associated persistent audit is
`AuditInverseCyclicFollowups`.

The content-box count is the product of `(species dimension + 1)`, before
gauge or charge filters. The middle exterior dimension is an ambient size,
not a claim about a single matrix or its rank. See the
[topic](../../docs/topics/sm-rank-enumeration/README.md) for the remaining
executable-coordinate and compression prerequisites.

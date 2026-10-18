# Bounded verification plan

## Target and semantic bridge

Start at `SMJointHiggsSupport.HiggsSupport` and
`SMJointContentSupport.supports_iff_choices`. The evaluator must decide the
same joint branch choices: color, weak and both spins cannot choose different
core branches independently. Its eventual bridge is a proved Boolean iff to
`SMJointContentSupport.Supports c m`, then to `HiggsSupport p h d` via the
existing finite weak/admissibility filter. Reattach the two charge conditions
through `original_ql_iff`; do not build another coefficient-space bridge.

A timeout, missing instance or unsupported case is unknown, never false.
A positive-only witness checker does not meet the negative-check endpoint.
For a partial implementation use an explicit unknown outcome and state exactly
which returned true/false answers have proved soundness. A complete Boolean
claim requires both directions on its stated domain.

## Route A: direct finite decision

One source/type inspection and small probe pass:

- Trace `GenerationTensorSupport.Choice`, actual signed-core `.expression`,
  expression branches, `RestrictedColorWordSupport.Supports`, owner validity
  and `SU2TensorWordSupport.Path`. Check finite bounds and executable instances.
- Separate classical representation equivalences from metadata projections.
  Attempt local constructive decision instances without reducing analytic maps.
- Test both a known witness and a known failure. Distinguish elaboration,
  generated-code execution and kernel reduction failures in the record.

Do not infer executability merely from finiteness or `classical`. If direct
execution reaches noncomputable data or factorial search, record the exact
blocking declaration/search size and proceed to Route B once.

## Route B: one data-only refinement

Extract natural-number core/occupation/branch metadata into an executable
syntax, with a proved connection to existing expressions. A manually transcribed
branch table is candidate data until every relevant entry is proved correct.
A new decomposition theorem is outside this route.

For SU2, compute reachable degrees by finite-set dynamic programming and prove
membership iff a CG path has that degree. Preserve joint branch dependence.
For color, first use exact owner-level matching/triple backtracking; symmetry
quotients, memoization or pruning need a completeness proof before they can
justify false answers. Triality/capacity alone are only rejection filters.
No general LR classification or saturation foundation is permitted here.

Freeze one algorithm after inspection. Do not restart failed investigations
through alternative formulations. If the needed semantic bridge or complete
color search requires a separate theorem-level project, stop and describe it.

## Probe domain and order

Commit an exact input/expected-status manifest before measurements. Use species
indices from the existing signed dictionary, not newly invented conventions.

1. Unit and local controls: empty/unit sources, zero/overflow branches,
   SU2 degrees with and without a degree-zero path; color pair, determinant,
   forbidden same-owner pair/triple and triality failures. Include both color
   orientations and actual dual kinds used by the SM adapters.
2. Original-space controls: LLHH and conjugate LLHH positive, a charge-neutral
   inactive-spin failure, and selected DUQL/QQUE/QQQL/DUUE neutral witnesses.
   Include a mixed conjugate source and a whole-source failure whose charge
   filters pass. Validate expected values independently before freezing them;
   disagreement is a result to investigate, not a reason to edit expectations.
3. Stress controls: Q6 at (m,delta)=(2,-2), Q18 at (6,-6), and one previously
   difficult zero row selected from the neutral diagnostic domain. Retain at
   most twelve original-space probes total including stage 2. Passing easy
   witnesses alone is insufficient evidence for prohibition usability.
4. Only after stages 1-3 pass, run a compiled structural comparison on the exact
   107 keys in `neutral-sparse-results.csv`. Compare local support to extracted
   multiplicity > 0, with identical species, degree, weak label, hypercharge
   delta and trivial residual. Check key uniqueness/completeness first. This
   tests local `Supports`, not arbitrary original Higgs bidegrees. Independently
   exercise the Higgs filter/stability in stage 2.

The CSV/Weyl/Python route is an external regression reference, never a structural
proof premise. Compare the reported 41 positive/66 zero split only after keywise
comparison. Compiled agreement is not a kernel certificate of all 107 values.

## Verification, budgets and decision

Use existing guarded runner with one Lean process/build at a time, at most
300 seconds per closed probe, 6 GiB sampled process-group RSS and 4 GiB host
memory reserve. No raised Lean proof limits, `native_decide`, custom axioms,
`sorry`, audit exceptions or retired numerical imports. Record cold versus
cached execution, process command, elapsed time, peak sampled RSS and whether
checking was compiled or kernel-based. Stop at the first resource interruption
on each route; do not retry with larger limits. Existing runner budgets are
measurement guards, not hard OS guarantees.

For any refinement, prove its semantic bridge, test deliberately wrong
positive/negative candidates are rejected, and kernel-check at least one true
and one false nontrivial original-space result. For usable negative results,
show exhaustive enumeration/pruning completeness, not absence of found witnesses.
Register new modules and persistent strict transitive audits in their owning
Math/Physics aggregates. Run focused builds, strict audits, one serialized full
`lake build`, layout, links and diff checks before accepting proof changes.
Documentation-only milestones use links/diff checks and explicitly skip Lean.

Report separately: (a) mathematical decidability/interface availability,
(b) proved evaluator correctness, (c) closed kernel performance on the frozen
probes, (d) compiled 107-row agreement, (e) any implication for a future B1 search.
Do not extrapolate (c)/(d) to all contents or 572 assignments.

A future B1 solver also needs a complete finite target-domain reduction using
fermion capacity, hypercharge and Higgs stability, plus an agreed definition
of the assignments being enumerated. Identify this dependency; do not silently
start that solver. Finish this topic with a feasibility decision and a concrete
next-step recommendation, even if the tested route fails.

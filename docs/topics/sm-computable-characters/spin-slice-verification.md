# Retained spin-weight slice verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](spin-slice-results.md)
and [continuation plan](colored-support-completion-plan.md).

## Trust and resources

Eight Math modules add 53 persistent strict transitive checks. The existing
layer/original-module checks, numerical import exclusions and the axiom
allowlist (`propext`, `Classical.choice`, `Quot.sound`) are unchanged.
No dependency pin, numerical certificate or Lean proof limit changed.

Focused checks use the existing one-thread guarded runner with a 6 GiB
sampled process-group RSS cap, 4 GiB host reserve and 300-second wall cap.
The default full build uses 10 GiB with the same reserve/wall cap and
the previously recorded mimalloc environment settings.

## Successful checks

- `Math.RepresentationTheory.TorusWeightSlice`: passed after the explicit
  identity-on-vectors weight cast was added.
- `TorusWeightTensor`: actual matching tensor slices, explicit inverse
  coordinates and absent-weight exclusion passed.
- `TorusWeightProducts`: passed for arbitrary dependent carrier families.
- `SU2WeightSlice`: the uniform interval/parity iff, actual matching
  equivalence and absent-weight exclusion passed.
- `SU2StringSliceSum`: complete retained-action filtering passed;
  successful check 5.8 s, peak 4,799,916 KiB.
- `SU2ConsecutiveSlices`: actual k / k+2 split passed, 5.0 s,
  peak 4,772,152 KiB.
- `SU2IsotypicSlices`: the actual complete-source construction and final
  consecutive-slice equivalence passed, 6.3 s, peak 4,882,908 KiB.
- `OccupationExteriorDecomposition`: actual projection/sum inverses
  passed; the module compiled in 3.3 s.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  passed, 1008 strict checks before the occupation extension; the
  final checkpoint verification below includes all 1016 checks.
- Guarded default `lake build`: passed, 7207 jobs including GUT,
  9.0 s, peak 6,628,580 KiB. The unchanged Physics structural audit
  replayed its 300 checks; the combined structural count is 1308.
- Final successful focused/audit/full logs contain zero warnings/errors.

The initial direct equality-transport form of the filtered sum failed the
default kernel limit in 94.9 s at peak 4,971,228 KiB. It is not proof
evidence. The final explicit `castWeight`, separate linear maps and small
application lemmas preserve the mathematical statement and avoid that
large equality transport. No guard triggered in the successful checks.

Final occupation checkpoint: the strict Math audit passes all 1016 checks
(6.0 s, peak 5,339,476 KiB); Physics retains its 300 checks. The default
`lake build` passes all 7208 jobs including GUT (9.5 s, peak 6,629,420 KiB),
with zero warnings/errors and no resource guard triggered.

Repository layout passes 1832 modules; links pass 922 Markdown files,
5708 local links and 111 fragments, with zero errors. The retired
certificate check passes all 19 hashes and confirms 15 retired modules
remain absent. `git diff --check` passes. Disposable output remains
under `/tmp`.

## Scope

The continuous consumer requires the actual joint continuity and torus
bound of its source; it constructs its complete isotypic decomposition.
It does not identify exterior-doublet weight spaces automatically, prove
Q degree-five/six branching, classify restricted color products or finish
the full q/l support endpoint. Those remain the active continuation.

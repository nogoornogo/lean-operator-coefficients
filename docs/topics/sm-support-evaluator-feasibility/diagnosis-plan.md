# Q18 obstruction diagnosis contract — stage 01

The user authorized further cause isolation after the initial feasibility stop.
Reuse the existing topic branch. Keep its original failed experiment intact;
this is not authorization to raise proof limits, resume the 107-row comparison,
implement a general evaluator or merge into master.

Endpoint: determine which prerequisite can reproduce Q18's recursion failure
without executing color/CG support search, and which smaller isolated pieces
can pass. Separate an observed failure from a claim that it is the only cost.

One pass over two source routes: (A) finite generation-occupation enumeration,
(B) core metadata and individual factor decisions. At most six diagnostic
source variants after inspecting the selected instance. Freeze the precise
variants in the generator before executing them. Maintain 300 seconds, 6 GiB
sampled group RSS, 4 GiB host reserve, existing Lean options, and serialized
runs. Stop a failing component without retrying it at larger limits. Tests of
other independent components remain allowed for isolation. No repeated full
Q18 `decide` run. Retain scripts/templates, commands and results; failed
recovery declarations never count as proofs. No production module changes.

## Frozen variants

Source inspection selects `Set.fintypeRange (counts 18)`, not the generic
ambient-count subtype filter. It images all generation words before removing
duplicate occupations. `Fintype.decidableExistsFintype` consumes that enumeration.

Six variants in `tools/structural-support/diagnose.py`:

1. `occupation6`: decide an occupation exists, predicate `True` (positive control).
2. `occupation18`: identical trivial predicate at degree 18; no gauge support.
3. `words18`: decide a raw three-generation word exists, predicate `True`.
4. `metadata`: extract Q core degree-six syntax with a kernel `rfl` bridge;
   assemble three such cores and weak degree six; compile and kernel-check
   the branch count 20^3=8000 without deciding support.
5. `occupied`: decide support of that one fixed (6,6,6) occupied expression,
   omitting enumeration over occupations. This is a component, not a replacement
   for the original coefficient space. Its actual support is a diagnostic target,
   not assumed as a premise.
6. `spins`: same expression with every color atom replaced by the unit. This
   deliberate projection isolates remaining three-spin searches; no equivalence
   to original support is claimed.

The instance-inspection probe is reconnaissance, not a seventh algorithm or
stress candidate. Its source prints the selected instances and definitions.
Run occupation controls, then raw words, metadata, projected spins and finally
the fixed occupied support; no repeated full-content evaluation.

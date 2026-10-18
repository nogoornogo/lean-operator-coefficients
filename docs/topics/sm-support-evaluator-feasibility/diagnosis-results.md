# Q18 cause isolation

The user authorized this bounded follow-up at stage 01. It reuses the topic
branch after `checkpoint 01`, with no merge/push or larger resource limits.
The [diagnosis contract](diagnosis-plan.md) freezes six component probes;
[the generator](../../../tools/structural-support/diagnose.py) reproduces them.

## Finding

**The existing generation-occupation enumeration is independently sufficient
to reproduce the recursion failure.** Removing occupation enumeration and fixing
(6,6,6) makes the occupied Q18 expression's positive support check pass under
the same settings. This identifies a concrete first repair, not a proof that
all color/CG searches or negative decisions are efficient.

The actual selected instance, confirmed by `#synth`, is:

```text
Set.fintypeRange (FiniteExteriorExhaustion.counts 18)
```

Its implementation in the pinned mathlib
`Mathlib/Data/Set/Finite/Range.lean` is `Fintype.ofFinset` of
`Finset.univ.image (f ∘ PLift.down)`. The source domain is generation words
`Fin 18 → Fin 3`; the image removes repeated count vectors.
`GenerationTensorSupport.choiceFinite` uses that instance at its leaves, and
`Fintype.decidableExistsFintype` uses the resulting enumeration for existence.
This is **not** direct enumeration of count triples, nor the alternative generic
subtype filter over all bounded count vectors.

A source domain of 3^18 = 387420489 words represents only 190 nonnegative
triples summing to 18. These numbers describe the domain and distinct intended
counts, not an observed traversal count: the failed run does not enumerate
387420489 words to completion. A small exact Python comprehension confirms
190 triples (127 additionally have every count <=12). No new Lean theorem
about these cardinalities is claimed.

## Isolated results

Every run uses cached imports, one Lean thread, unchanged proof options,
300 seconds, 6 GiB sampled group RSS and a 4 GiB host reserve. All are separate
runs; none repeats the failed full-content Q18 decision.

| probe | exit | elapsed s | sampled peak KiB | outcome |
| --- | --- | --- | --- | --- |
| selected-instance reconnaissance | 0 | 3.3 | 5039932 | range-image instance and finite-exists decision confirmed |
| `occupation6` | 0 | 9.3 | 6204380 | an occupation exists, predicate True; 28 strict checks pass |
| `occupation18` | 1 | 5.8 | 5657988 | same trivial existence predicate fails kernel recursion |
| `words18` | 0 | 4.5 | 5442460 | raw word existence, predicate True; 28 strict checks pass |
| `metadata` | 0 | 4.0 | 5441056 | compiled branch count 8000 and kernel equality; 28 strict checks pass |
| `spins` | 0 | 4.8 | 5449184 | fixed occupied expression with color erased has support; 28 strict checks pass |
| `occupied` | 0 | 4.0 | 5451184 | fixed occupied expression with color retained has support; 28 strict checks pass |

`occupation18` fails before any color, CG or branch-validity predicate is
required. `words18` succeeds, so a trivial existential over raw words alone
is not enough to reproduce the failure: the range/image occupation enumeration
is the discriminating additional layer. Existence may short-circuit; the
successful raw-word test does not measure exhaustive word enumeration.

`metadata` uses the actual Q core degree-six presentation, reflected to data
with a kernel `rfl` correspondence. Three such expressions plus weak degree
six have 20^3=8000 branch choices. The size check is not support search.
The `occupied` check uses one fixed occupation with both color and all three
SU2 factors retained jointly. It proves an existential witness, not that all
8000 branches were visited. It is not connected here as a new theorem about
the original whole Q18 coefficient space. The deliberately color-erased test
is only a diagnostic projection and asserts no equivalence to full support.

The failed occupation candidate is rejected again by the strict audit because
Lean error recovery uses `sorryAx`. It is not accepted as a proof. No timeout,
RSS interruption, raised option, new axiom, numerical input or dependency change
was used. No seventh component or alternative algorithm was tried.

## Consequence for the next implementation

The later authorized [remedy investigation](remedy-results.md) proves the
previously missing uniform count-triple attainability in a diagnostic
prototype and specifies how the enumeration must be selected explicitly.
The original cause-isolation evidence above remains unchanged.

Prioritize a compact generation-occupation enumerator over a general color
classifier or a broad evaluator rewrite:

1. Enumerate triples (a,b,c) with a+b+c=n directly, retaining the existing
   statistical source and joint branch predicate.
2. Prove correspondence in both directions with
   `FiniteExteriorExhaustion.Occupation`; `occupation_sum` supplies the existing
   forward direction, while attainability of each triple needs a proved inverse.
3. Transport existential decisions through that correspondence. Any capacity
   pruning must be justified by the existing core-overflow theorem.
4. Re-test full Q18 with unchanged limits, then a nontrivial negative case.
   Only then decide whether CG/color refinement is also needed.

This is a recommendation, not implementation authorization inferred from this
diagnosis. A compact enumerator may remove this obstruction; no performance
claim for arbitrary content, negative all-branch search, 107 rows or 572
assignments follows from the positive fixed-occupation test.

## Reproduction and repository checks

Materialize a probe, then use the existing runner:

```sh
python3 tools/structural-support/diagnose.py occupation18 > /tmp/sm-diagnosis.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/sm-diagnosis.lean /tmp/sm-diagnosis.log
```

Run other frozen stages separately; `occupation18` is an expected resource
failure, never a valid closed theorem. The instance reconnaissance is retained
in `tools/structural-support/probes/instances.lean.txt`. Each successful component
checks all 28 local declarations transitively against exactly propext,
Classical.choice and Quot.sound. Logs remain disposable outside source control.
No active Lean module, import or aggregate changed; full library build/audit
rebuild was not rerun and this introduces no new library proof baseline.
Repository checks pass: Python AST parsing for both generators; layout
(1934 modules); retired-certificate check (19 hashes, 15 absent modules);
local links (964 Markdown files, 5891 links, 111 fragments, zero errors);
and `git diff --check`. The link checker used its previously required
sandbox escalation for the read-only git subprocess. No checker was modified.

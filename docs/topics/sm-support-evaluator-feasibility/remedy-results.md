# Compact occupation remedy investigation

User-authorized follow-up after `checkpoint 01`, stage 01. The
[bounded contract](remedy-plan.md) covers one compact prototype and two color
controls. No production module or full evaluator was implemented.

## Stronger feasibility result

The compact remedy's essential semantic obligation is now **proved in the
prototype**, uniformly in n:

```text
v ∈ Set.range (FiniteExteriorExhaustion.counts n)
  iff sum_s (v s).val = n,
where v : Fin 3 -> Fin (n+1).
```

The reverse implication constructs a word with contiguous blocks of a zeros,
b ones and c twos, proves its actual `counts`, then transports the length
using an equality of natural numbers. No supplied occurrence or source
comparison premise is used. The forward implication uses the existing
`occupation_sum`. The statement is specific to the existing three-generation
occupation problem, not a new arbitrary-flavor classification.

A triangular list enumerates a=0..n and b=0..n-a, taking c=n-a-b. Its membership
iff a+b+c=n is also proved uniformly. At n=18, both compiled length output
and a closed kernel equality give **190**. These two uniform theorems supply
the needed completeness/attainability ingredients, rather than trusting a
Python enumeration. They do not yet construct a production `Fintype`, wire
it into `Supports`, or prove a full-content executable evaluator correct.

The prototype is retained in
[compact.lean.txt](../../../tools/structural-support/probes/compact.lean.txt),
with the [generator](../../../tools/structural-support/remedy.py). Successful
runs audit all locally introduced declarations transitively.

## A new instance alone will not repair existing decisions

`GenerationTensorSupport.choiceFinite` takes a content tree and returns a
`Fintype (Choice t)`. Its leaf branch's `inferInstance` was elaborated when
that constant was defined, selecting the range-image occupation instance.
Its recursive branches call that same constant. It does not accept a new
occupation enumerator as an argument.

Likewise, the earlier probe's `contentDecision`/`higgsDecision` have already
selected their finite-existence instances. Merely declaring a higher-priority
compact instance elsewhere does not rewrite these already elaborated terms.
A remedy must explicitly build a fresh recursive choice enumeration with
compact leaves, and fresh decisions using it, or pass the enumerators as
explicit arguments. Keep the old library instances and theorem interfaces
intact until the alternative path is tested. Do not assume a local instance
change propagates through previously defined constants.

This is separate from the known compiled-code problem: core presentation
metadata and higher decision definitions are still noncomputable for code
generation. The first integration test should therefore be a closed **kernel**
Q18 check using compact choices. A general compiled evaluator is a later gate.

## Remaining color cost: bounded evidence

The two new occupation-free probes both pass under unchanged limits:

- symmetric degree six tensor opposite-symmetric degree six is supported
  (evaluation pairing supplies a witness).
- one symmetric degree-six leaf is unsupported (determinant triples cannot
  have three distinct owners).

The selected permutation instance is `Equiv.instFintype`. Its pinned mathlib
implementation uses `fintypePerm`/`permsOfFinset`/`permsOfList`, whose cardinality
is factorial. Six flags have 720 labelled permutations. This is a source-level
scaling concern, not a new measured failure: the positive and negative probes
both pass, and the positive existential can short-circuit. No larger color
probe, worst-case benchmark, owner-matching rewrite or general LR route was
started. These results support prioritizing the occupation fix first.

## First implementation contract now supported by the evidence

1. Add a Math-owned compact three-count enumeration over the **same** existing
   occupation subtype. Use the prototype's sum/attainability and list-membership
   proofs to establish exact coverage. Avoid enumerating source words, even
   inside a hidden membership or deduplication decision.
2. Build explicit recursive compact `Choice` enumeration and fresh support
   decisions that select it at every leaf. Preserve all joint expression
   branches and the original `Supports` proposition; do not change its meaning.
3. First test trivial occupation existence/cardinality, then full original Q18
   at h=0,d=6 with unchanged limits. Confirm the compact instance is selected.
4. Test a neutral negative source and both prior rejection controls. If another
   component stops, isolate it instead of claiming the first fix solved general
   evaluation. Do not proceed to the 107 rows until these gates pass.
5. Only after kernel feasibility is established decide how much executable
   metadata/reflection is needed for a compiled implementation. A count fix
   alone does not remove noncomputable presentation dependencies.

The outstanding work is now implementation/transport and end-to-end performance,
not an unresolved existence theorem for realizing count triples. Production
Lean modules would require owning aggregates, strict audits, focused/full builds
and assumptions records; no such integration is claimed by this investigation.
No content/assignment classification, rates, dependencies or physical scope were
changed. Implementation remains a future step, not silently included here.

## Verification

Commands, one at a time, with already cached imports:

```sh
python3 tools/structural-support/remedy.py compact > /tmp/sm-remedy.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/sm-remedy.lean /tmp/sm-remedy.log
```

Substitute `color-positive` or `color-negative` for the other two variants.
All use a 300-second cap and one Lean thread, with no proof-option changes.

| variant | exit | elapsed s | sampled group peak KiB | strict local checks |
| --- | --- | --- | --- | --- |
| compact (final) | 0 | 4.5 | 5456688 | 18 |
| color-positive | 0 | 4.0 | 5445024 | 28 |
| color-negative | 0 | 5.0 | 5586044 | 28 |

Compact prototype development corrected one ordinary rewrite mismatch caused
by `sum_boole`'s natural cast; the final proof uses the simplifier and has no
warnings. No raised limits, source `sorry`, unexpected axioms or resource
interruption occurred. Audits allow only propext, Classical.choice and
Quot.sound, with no exceptions.

All Lean inputs remain diagnostic text outside the active library graph;
no full library build/audit rebuild was rerun and no new library proof baseline
is claimed. Repository checks pass: Python AST/prohibited-construct scans,
layout (1934 modules), retired-certificate check (19 hashes, 15 absent modules),
local links (966 Markdown files, 5898 links, 111 fragments, zero errors) and
`git diff --check`. The link checker used its existing read-only subprocess
sandbox escalation; no checker was modified.

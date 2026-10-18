# first rigorous stages of the A1 semisimple embedding classification

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex + local qwen3.6-35b-a3b-mtp / Lean 4.33.1

- Scope: first rigorous stages of the A1 semisimple embedding classification
- Local-model role: proposed-theorem review only; all accepted statements were
  independently checked against local Mathlib sources and the Lean kernel

### Audit result

The initially generated `CompactEmbeddingClassification.lean` was not sound as
a proof bridge: it used `U(3)` in place of `SU(3)`, dropped weak blocks of
dimensions four through six, attempted to derive dimension and faithfulness
facts from an arbitrary list, used `diag(-1,1)` as an alleged `SU(2)` center
element, and contained `sorry` and `True` placeholders.  It was replaced rather
than completed in that form.

The repaired modules now kernel-check:

- finite-dimensional unitary representations are semisimple by invariant
  orthogonal complements;
- every restricted defining action along `SU(3) x SU(2) -> SU(6)` is unitary;
- the correct center element is `-I_2`, is nontrivial, central, and has order two;
- killing `(1,-I_2)` excludes every subrepresentation detecting it;
- irreducible complex representations have scalar commutant by Schur's lemma;
- scalar matrices in `SU(6)` have sixth-root coefficient;
- the `SU(3)`/`SU(2)` low-dimensional highest-weight arithmetic and the finite
  product-block/count classification.
- the trace-zero block-scalar centralizer is uniquely parameterized by
  `Y5=(-2,3,0)` and `X=(1,1,-5)`.

The global highest-weight classification and external-tensor-product theorem
remain explicit missing bridges.  The original unqualified A1 statement is
also corrected: `(3,2)` is a faithful weak-doublet counterexample unless a
commuting hypercharge circle is required.

The full build completed successfully with 3727 jobs.  Axiom audits of the
new public theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`; the highest-weight arithmetic theorem did not require
`Classical.choice`.

---

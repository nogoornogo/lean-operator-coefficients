# Structural Proof Policy

New proofs and substantive proof rewrites must explain the mathematical
structure of the result. This policy supplements the existing build, strict
axiom-audit and [scope gates](WORKFLOW.md#endpoint-and-stop-gate).
Passing those checks alone does not satisfy this proof-design requirement.

## Numerical Proofs Are Prohibited

Do not use floating-point agreement, numerical approximations, sampling or
external computed ranks/tables as a proof. Do not replace the main argument
with exhaustive evaluation of coordinates, monomials or generated cases,
even when every case is checked by Lean's kernel. A kernel-checked table
establishes those entries; it does not make this an acceptable design for
the main proof.

First prove the identities, symmetry, transport, spanning, reconstruction
or other structural facts that imply the result. A computed rank must not
stand in for a structural completeness argument. External scripts may guide
discovery and provide regression checks; their output is never an unchecked
theorem premise.

Exact arithmetic and symbolic normalization remain available within that
argument. Tactics such as `ring`, `norm_num`, `linarith` and `omega` are not
banned by name. Small fixed checks may establish a node permutation, phase,
Gram entry, index identity or similar supporting datum. State which
structural hypothesis each check discharges; it must not conceal the main
theorem's case inventory. Summaries and counts derived from a proved
classification may be computed for presentation and regression purposes.

## Repetitive Case Splitting Is Prohibited

Do not expand essentially the same expression for many index choices and
split those expansions across a large family of similar lemmas or files.
Generating the files, reducing each file's size or staying under a memory
limit does not make this decomposition acceptable. Do not raise proof or
resource limits to keep such a route going.

Use a parameterized lemma, symmetry, multilinearity, induction, invariant
tensor shape, contractions or a proved equivalence/transport. Split modules
by distinct mathematical responsibilities. A genuine mathematical case
distinction must explain why its branches differ and share the common proof.
Short wrappers preserving an existing public API are permitted when they
derive their results from the shared theorem rather than recompute them.

The [Higgs cubature refactor](../topics/higgs-cubature-structure/remaining-results.md)
is the reference example. Its ordered fourth moments follow from tensor
symmetry and Gram contractions, with the second collinear family obtained
by transport. Small node/phase/Gram checks supply structural inputs. The
former families of fixed-wave moment computations must not be recreated
for new indices or new models.

## Review And Verification

Before implementing a potentially repetitive proof, record its shared
mathematical statement and the role of any finite supporting checks in the
owning topic. Review generated Lean output under the same rules as handwritten
source. A structural-looking wrapper around a large table is still a table
proof; review its dependencies as well as its final statement.

If the structural route fails, retain the checked work and document the
obstruction under the topic's stop conditions. Do not silently substitute a
numerical enumeration, extra caller premise or a new family of certificate
chunks. Freeze any required scope change before continuing.

For proof-performance claims, measure actual source compilation under the
recorded guards; incremental `Replayed` output is not fresh compilation.
See the [build guide](BUILD.md) and
[fresh-compilation audit](../topics/proof-memory-audit/README.md).
Proof changes still require focused builds, unchanged strict transitive
axiom audits and a full `lake build`.

This policy does not invalidate retained finite certificates or authorize
rewriting unrelated checked proofs. They remain evidence for their own
statements; new work and substantive rewrites follow the structural policy.

# Upstream contribution workflow

Reusable results should be offered upstream without turning this repository
into a development checkout of every possible target project.  Upstream work
therefore uses a separate fork and Git worktree (or a separate clone), with the
target project's own toolchain, style, and review policy.

The source hierarchy identifies candidates, but does not by itself assert that
a result belongs in a particular upstream:

- `Math/` groups mathematical results by subject, not by external dependency.
  `RootSpaceDimension` now wraps the existing pinned TauCeti dimension formula;
  it is not a missing upstream theorem. `BasedLieComparison` directly uses
  mathlib's internal one-simple-target projection equivalence through `import all`.
  Its public equal-dimension/generator-preserving convenience API is a possible
  contribution, not a new projection-kernel argument or an accepted submission.
  Upstreaming should expose/reuse that API rather than export the compatibility
  wrapper unchanged. The formerly retained local license notice/text were
  removed in [subsequent maintenance](DISTRIBUTION.md).
  Project-owned material is now under [Apache 2.0](../../LICENSE).
  Confirm provenance, third-party notices and compatibility with the target
  project's license before any upstream submission.
- `Physics/FieldTheory` contains reusable finite-dimensional mass and zero-mode
  algebra.
- `Physics/StandardModel` contains Standard Model representation and operator
  constructions.
- `GUT/` contains concrete unification applications; only independently useful
  generalizations should move upstream.
- `GUT/SU5/Embeddings` supplies the identified
  [deferred Physlib geometry candidate](../topics/su5-geometry-upstream/README.md). The smallest first
  slice is the actual group/covering map, not the full selection-rule proof.

For each contribution:

1. Extract the smallest coherent theorem and its prerequisites into the target
   fork. Check its transitive imports before choosing mathlib, TauCeti, Physlib
   or another destination; directory membership is not an acceptance claim.
2. Generalize names and statements only as far as the target library needs.
3. Re-prove and test under the target project's pinned Lean toolchain rather
   than copying compiled artifacts.
4. Follow the target's authorship, review, and AI-assistance disclosure policy.
5. Keep this repository's theorem until the upstream result is released at a
   compatible revision; then replace it with an import in a separate change.

An upstream rejection or a long review does not block this formalization.  A
new dependency is accepted only when it removes maintained local mathematics
or closes a real proof obligation, not merely because the package is related.

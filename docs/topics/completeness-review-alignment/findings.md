# Review Findings And Disposition

## Statement Alignment

| Item | Source evidence | Disposition |
| --- | --- | --- |
| 1: group terminology | `GradedMixedCompleteness` assumes `[Group G] [Group H]` | Abstract groups, not algebraic-geometric groups; correct analogous current-sector descriptions |
| 2: completeness versus computation | `equiv`, `selectedEquiv`, `allEquiv` assemble inverse quotient/Hom maps | README explicitly calls this structural completeness; arbitrary Hom computation and explicit bases remain separate |
| 3: positive-weight finiteness | `MixedContentBounds.bounded_finite` uses positive weights; `all_bounds_forbidden_iff` does not | State the results separately; no new combined finite-index theorem is claimed or implemented |
| 4: orbit representatives | `MixedContentOrbits.Content` is a quotient; `Factor`, `allResidual` and field transport use `x.out` | Explain internal noncanonical representatives and the fixed-representative naturality scope |
| 6: documentation drift | Topic verification is a dated checkpoint; Physics ledger had 17 large sections | Label checkpoint counts, explain package-name provenance, shorten the index and rebase incoming fragments |

The existing orbit support result `support_iff` and stable-support result
`support_allow` are distinct from representative-reselection coherence for
the separated carrier. Field transport compares species-preserving maps at
the same `x.out`; residual restriction similarly keeps these profiles fixed.
This review does not claim the absence of every possible coherence lemma in
the library, only that the documented naturality endpoint does not establish
the additional reselection claim.

The bounded-finiteness module is separately included in the foundation audit;
it is not imported by `GradedMixedCompleteness`. The all-bounds statement
quantifies every bound and every degree; it is not a uniform finite cutoff.
For this documentation endpoint, separating those facts is sufficient.

## Deferred Management And Refactoring

Item 5 (namespace migration or a new namespace policy) and item 7 (backup,
old branches, external worktree, empty-directory cleanup and ignore policy)
are not included in this bounded documentation topic. No remote upload,
history rewrite, worktree deletion or dependency change is authorized here.

The supplied Claude report describes a successful cached/replayed 6,547-job
build and axiom checks. This topic did not rerun them and does not introduce
that report as a new independently verified build baseline.

## Source Entry Points

- [Graded equivalences and all-bounds iff](../../../Math/RepresentationTheory/GradedMixedCompleteness.lean).
- [Positive-weight bounded finiteness](../../../Math/RepresentationTheory/MixedContentBounds.lean).
- [Orbit support and representatives](../../../Math/RepresentationTheory/MixedContentOrbits.lean).
- [Separated carriers](../../../Math/RepresentationTheory/TypedMixedSeparatedHom.lean).
- [Field-presentation transport](../../../Math/RepresentationTheory/GradedCompletenessFieldTransport.lean).
- [Residual restriction](../../../Math/RepresentationTheory/GradedCompletenessRestriction.lean).
- [Foundation audit](../../../Math/RepresentationTheory/Audit/AuditGradedOperatorFoundations.lean).

# Implementation Plan

## Frozen Inputs And Output

Supply `N : ℕ`, `[NeZero N]`, five finite index types Iq,Iu,Id,Il,Ie
with decidable equality, and charge maps from each index type to `ZMod N`.
Their flavor carriers are `I → ℂ`, with diagonal action by the already proved
faithful cyclic character. Different species may have different dimensions,
including zero. The signed-species conjugate dictionary uses opposite charges;
any use of algebraic dual or bidual interfaces must have a proved dictionary.
Higgs remains a single residual-neutral doublet.

For each existing independent physical sector, construct an exact finite
coordinate equivalence with explicit residual-neutrality and exchange conditions.
Prove both inverses, finrank and allowance/prohibition criteria. For the full
signed dimension-six sector, use the existing four-family decomposition and
prove total dimension additivity and total prohibition iff every family vanishes.
Combine this with LLHH allowance. Neutrality must be derived from character
injectivity, not assumed as a proxy for invariance.

Closed formulas use cardinalities of allowed independent coordinates where
possible. For genuine coupled exchange blocks, a proved finite relation matrix
kernel and exact rank-nullity formula is acceptable, provided the matrix entries
and the operator correspondence are proved and concrete rank controls are
certified in Lean. Merely restating `Allowed ↔ Hom ≠ 0`, displaying an unproved
matrix, or running a Python rank calculation does not meet the endpoint.

## Milestones

1. **Weight foundation.** Define diagonal charge representations on finite
   coordinate carriers. Prove tensor/symmetric/exterior coordinate weight rules,
   including dual signs, empty carriers and zero-weight extraction/reconstruction.
   Reuse existing bases and finite-statistics APIs rather than rebuilding them.
2. **LLHH and DUQL.** For LLHH obtain neutral unordered lepton-pair coordinates,
   with diagonal entries included. For DUQL obtain neutral heterogeneous tuples.
   Prove cardinality dimensions and constructive iff witnesses. Transport through
   the existing physical-sector equivalences.
3. **QQUE and DUUE.** Derive allowed independent coordinates from actual repeated
   species symmetries. Preserve all symmetric/alternating branches in the existing
   classifications. Prove dimension and nonzero tests, not raw ordered-tuple counts.
4. **QQQL.** Prove neutrality is stable under species permutations, restrict the
   actual exchange relations to weight blocks and classify their solution spaces.
   Establish exact kernel/dimension and nonzero criteria with proved reconstruction.
   Reuse the finite local dictionaries; do not assume every neutral tuple survives.
5. **Physical assembly and controls.** Connect all four factors to the full signed
   exterior sector, sum their dimensions and prove simultaneous total prohibition
   and LLHH allowance. Recover the previous singleton criteria; test empty species,
   trivial charges and a nonuniform assignment exposing repeated-field constraints.
   Actual-field transport may reuse supplied existing equivariant input interfaces.
6. **Verification and closure.** Register sources/strict transitive audits in the
   proper aggregates; focused and full `lake build`, layout, links and diff checks.
   Write the completed proof dossier and verified assumptions entries, then commit.

## Decisions And Boundaries

This is finite-multiplicity diagonal cyclic classification, not arbitrary
nonabelian character theory or arbitrary-H executable Hom computation.
No anomaly cancellation, Yukawa compatibility, UV generation, RGE, rates or
observational prediction. Literature counts are not presumed correct and need
not be cited as theorem inputs. No AutoEFT dependencies or runtime verification.

The specified six-quark general-flavor selection extension is a later topic:
its 25-coordinate typed exchanges are not added as an automatic milestone here.
Likewise general p/y/m/j construction and derivative/EOM/IBP foundations remain
outside scope. Unequal finite species dimensions are essential; infinite flavor
carriers are supported by existing abstract completeness, not by these counts.

Bounded weight/basis/finite-relation helpers are authorized by this scope. Stop
for a counterexample to an intended counting formula, an essential new physical
premise or a prerequisite requiring a large new foundational project. Correct
the statement explicitly rather than silently adding nonzero or genericity inputs.

## Acceptance And Stop Condition

All six milestones must pass, including QQQL exchange constraints and full-sector
assembly. Intermediate LLHH or charge-neutrality lemmas are checkpoints, not
completion. Standard axioms only; no `sorry`, custom axioms, `native_decide`,
pin changes or audit exceptions. Master integration requires a separate request.

## Completion

All milestones passed. See [results](results.md) for the finite dictionary
implementation, the decision to avoid unused exterior/physical-dual foundations,
control theorems and verification. There is no pending obligation inside the
frozen endpoint; deferred extensions are not required for closure.

# Inheriting A Nonzero Mediator Exchange

- ID: mediator-inheritance
- Status: completed
- Result type: proved sufficient inheritance criteria and algebraic cancellation control.
- Working branch: `proof/mediator-inheritance`.
- Integration target: `master`.

## Frozen Endpoint

Investigate inheritance of the [general exchange](../mediator-qque-matching/README.md)
from a retained mediator sector to a larger one, without assuming nonzero
total exchange or no cancellation as a premise. Prove checkable sufficient
conditions on forward mass maps and current support, derive the inverse-mass
identity and coefficient equality, then transfer the existing qque exterior
endpoint. Reuse the checked SU(5) core for a family with arbitrary added
mediator space and invertible mass.

Two bounded routes: (1) a mass-intertwining inclusion with supported source;
(2) a mass-intertwining projection with a dual current factoring through it.
Use product mediators to test arbitrary spectators and to check whether a
retained nonzero core and block mass alone forbid cancellation.

Inputs remain the local paired quadratic model, invertible mass operators,
linear currents and structural identities. A genuine group inclusion or
representation restriction alone is NOT asserted to supply those identities.
No concrete larger GUT, full UV action, positive-form reinterpretation,
vacuum, Grassmann convention or amplitude is added. Stop after these algebraic
routes; physical realization of support/mass conditions is separate work.

## Interfaces And Acceptance

- [Exchange](../../../Math/LinearAlgebra/MediatorExchange.lean)
- [Qque sector and Hom adapter](../../../Physics/StandardModel/Operators/MediatorQque.lean)
- [SU(5) core](../../../GUT/SU5/Matching/MediatorMatching.lean)

Focused and full builds, persistent strict transitive axiom audits, layout,
local links, diff checks and existing exact qque regressions. Lean LSP is
unavailable; use source and targeted builds. No dependency/limit changes,
custom axioms or `sorry`. Commit, merge to master with `--no-ff`, recheck and
retain the branch without pushing.

## Results

### Structural Criteria

[MediatorInheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)
proves two sufficient criteria for exact equality of the ordered exchange.
Write M for the retained mass-squared operator, N for the full one, J,K for
the retained currents and L,R for the full currents. Both masses are invertible.

1. Source support: `N i = i M`, `L = i J`, and `R(y)(i x) = K(y)(x)`.
   The inverse identity `N^-1 i = i M^-1` is derived, and hence
   `R(y)(N^-1 L(x)) = K(y)(M^-1 J(x))`.
2. Observer support: `p N = M p`, `p L = J`, and `R(y)(x) = K(y)(p x)`.
   The inverse identity `p N^-1 = M^-1 p` is derived, giving the same result.

These conditions concern forward mass maps and actual linear current maps;
no inverse-mass pairing equality, nonzero full coefficient or no-cancellation
premise is supplied. The abstract identities need only linear compatibility
maps i,p, not injectivity/surjectivity; product inclusions/projections give
genuine split examples. The criteria are sufficient, not necessary, and need
not cover all possible nonzero exchanges or mass mixing patterns.

For product mediators the proof gives the exact sum law
`C(M direct-sum N; (J,L), (K,R)) = C(M;J,K) + C(N;L,R)`.
Either vanishing spectator source or vanishing spectator dual current therefore
preserves the full coefficient, with the other spectator current unrestricted.
No positivity or common mass eigenvalue is needed for this algebraic statement.

### Qque And SU(5)

[QqueMediatorInheritance](../../../Physics/StandardModel/Operators/QqueMediatorInheritance.lean)
transfers invariance, the internal intertwiner and the generated species-sector
element along the proved coefficient equality. It does not infer nonzero
alternation from nonzero ordered coefficients. Equality of the sector elements
also leaves their coordinate under the existing Hom equivalence unchanged.

[InheritedExchange](../../../GUT/SU5/Matching/InheritedExchange.lean) applies
the projection criterion to the checked SU(5) core. `nonzero_of_projection`
derives full invariance, equality with the old exterior coefficient and
nonzero descent from the mass/current identities plus the original nonzero
real g,v assumptions. It takes no nonzero total exchange premise.

The concrete `spectatorSector_nonzero` family permits any added complex
mediator module W, any invertible mass on W, and any extra Q/up current.
Mass is block diagonal and the extra Q/e dual current is zero. Every member
has exactly the original SU(5) exterior coefficient. This checks a family
at once, not a sequence of separately computed examples.

### Countercheck And Boundary

Keeping the original block and forbidding mass mixing alone is insufficient.
The generic `duplicate_cancellation` uses mass `M direct-sum M`, currents
`(J,J)` and `(K,-K)`, and proves the TOTAL ordered coefficient is identically
zero. `product_retains_core` checks that the original mass, projected source
and restricted dual current are retained. `retained_core_can_cancel` combines
this with the actual nonzero SU(5) core coefficient. The full source is not
confined to the retained block, and the dual current does not factor through
its projection, so neither support criterion is silently satisfied.

This is a counterexample in the algebraic paired-mediator API, NOT a constructed
GUT representation or a physical counterexample to SU(5) proton decay.
Likewise, the inheritance family is not yet a larger GUT realization. Its
external fields are the retained SU(5) fields; embedding them in a larger
matter representation and deriving current support from that action remain
application obligations. Neither a group inclusion nor branching alone has
been proved to give the required support and mass identities. The model's
full UV action, vacuum, normalization and amplitude boundaries are unchanged.

Stop here: both frozen algebraic routes are closed. Further uniform physical
generalization should derive these identities from a specified class of
representation actions and mass backgrounds, not assume the generated
coefficient is nonzero. No individual SU(N), Spin or E6 extension is certified.

Subsequent application: the [SU(6) check](../su6-tree-matching/README.md)
has now derived these conditions on a specified exterior-matter/background
benchmark. This does not broaden the frozen theorem above to arbitrary GUTs.
The [updated plan](../post-su6-generalization/README.md) proposes a uniform
exterior family as the next application milestone.

### Verification

- Focused builds of the three new audit modules passed: 11 Math, 3 Physics,
  5 SU(5) declarations checked transitively, allowing only `propext`,
  `Classical.choice`, `Quot.sound`. New proof files have no warnings.
- Full `lake build`: passed, 5791 jobs. Existing warnings were replayed;
  new proof files had no warnings. Repeat the build after integration.
- `node tools/layout/check-layout.mjs`: passed, 740 modules.
- `node tools/docs/check-links.mjs` and `git diff --check`: checked before
  integration and repeated on the merged state.
- Existing exact regressions: `python3 tools/qque/audit_one_generation.py`
  (4 tests), `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3) all passed.
  These check existing finite conventions; they do not validate physical
  realizations of the new extension family. New cancellation controls are
  Lean theorems, included in the strict audits.
- No dependency pins, heartbeat limits or existing proofs were changed.
  Git ancestry records the topic and merge; retain the branch without pushing.

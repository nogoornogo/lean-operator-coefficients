# completed su5 milestones

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Completed SU(5) Milestones

- **SU5-1: shared boundary and conventions (stage 01).** Extracted
  circle-valued charge labels, Abelian operator charge/character algebra,
  rank-four weight/profile algebra, and residual gauge tensors with no
  transitive SU(6) imports. Existing names, source adapters, and tests remain
  available through compatibility entry points. Proved that equal weight
  normal forms are exactly common diagonal shifts, and proved surjectivity
  of the normal form. A persistent audit enforces import independence and
  checks nontrivial finite charges, positive/negative tensor invariance,
  independent residual labels, and hypercharge conventions. Standard axioms
  only; shared audit 3087 jobs, combined shared/legacy audit 3935 jobs, full
  build 4262 jobs. At that checkpoint the actual embedding/source bridges
  and endpoint remained pending. See
  [the shared foundation](../../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md).
- **SU5-2: actual embedding and global kernel (stage 01).** Constructed
  the continuous matrix map `diag(z^-2 A, z^3 B)` into SU(5). Proved the
  exact kernel `(z^2 I_3, z^-3 I_2, z)` with `z^6 = 1`, its centrality,
  and its isomorphism with `Multiplicative (ZMod 6)`. The quotient embeds
  as a closed subgroup and is topologically group-isomorphic to the image.
  Persistent audits enforce SU(6)-free imports and check coordinates,
  positive/negative kernel and quotient controls, and both continuity
  directions. Targeted audit 3512 jobs, full build 4271 jobs; standard
  axioms only. Branching, the commuting-action source bridge, and the
  SU(5) endpoint remain pending. See
  [the embedding dossier](../../../proof/current/inputs/GUT/interfaces/su5-embedding.md).
- **SU5-3a: actual matter, branching, and descent (stage 01).** Constructed
  the actual `5`, contragredient `bar5`, and exterior-square `10` with
  dimensions 5/5/10, full covering-group branching equivalences, and exact
  descent through the SU5-2 kernel. Proved inequivalence of `10` and `bar5`
  by dimension. A reusable finite-basis adapter applies pinned TauCeti
  compact unitarization to proved continuous coefficients, giving equivalent
  continuous unitary realizations and quotient actions. Shared weak-dual and
  charged epsilon lemmas were extracted without changing existing SU(6)
  APIs. The persistent audit checks inverses, wedge orientations, all five
  left-handed hypercharges on arbitrary circle elements, kernel/pullback,
  and transitive SU(6)-free imports. Targeted audit 3815 jobs; full build
  4315 jobs; standard axioms only. This checkpoint left actual `bar5`/`10`
  irreducibility for SU5-3b below and the source bridge for SU5-4.
  See [the matter dossier](../../../proof/current/inputs/GUT/interfaces/su5-matter.md).
- **SU5-3b: actual matter irreducibility (stage 01).** Proved the actual
  defining, contragredient, and exterior-square SU(5) actions irreducible.
  Actual diagonal signs extract coordinates; determinant-corrected
  permutations mix all basis vectors. The subspace argument is reusable
  as `RepresentationTheory.irreducible_of_basis_coordinates`. TauCeti
  equivariant transport gives irreducibility of the continuous unitary
  models; their `10`/`bar5` inequivalence is checked independently by
  dimension. The persistent matter audit checks arbitrary subrepresentations
  are bottom or top and retains transitive SU(6)-free imports. Targeted
  audit 3821 jobs, 48 standard-axiom reports, full build 4318 jobs.
  **SU5-3 is complete.** SU5-4 and the final SU(5) endpoint remain targets.
- **SU5-4: actual ordinary-Abelian source and tensors (stage 01).**
  Constructed `n(10 + bar5)` and derived its full U centralizer as
  `U(n) x U(n)` using the actual constituent irreducibility. Arbitrary
  commuting unitary Abelian actions yield exhaustive, mutually orthogonal
  full character sectors; finite groups, repeated characters, and generation
  mixing are allowed. Positive generations supply injective SM field maps
  whose shared multiplet charges are proved, not assumed. Both neutral
  signatures and nonzero invariant ordered internal tensors on their actual
  field ranges/duals are checked. Audits cover a finite non-scalar generation
  swap, repeated/trivial sectors, zero generations, and an incompatible
  u^c/e^c action in one actual `10`. Transitive imports remain SU(6)-free.
  Targeted audit 3901 jobs, 31 standard-axiom reports, full build 4358 jobs.
  No dependency changes or amplitude/Grassmann nonvanishing claim. SU5-5
  final packaging remains pending; see [the source dossier](../../../proof/current/inputs/GUT/interfaces/su5-source.md).
- **SU5-5: scoped selection-rule endpoint (stage 01).**
  `SelectionRule.scoped_no_go` refutes universal ordinary-Abelian charge
  prohibition for retained actual `n(10 + bar5)`, `n > 0`, and returns
  supported neutral `qque`/`duql` with nonzero invariant ordered internal
  tensors. Prohibition allows independent charges at each field slot.
  The full central kernel acts trivially, and field/tensor actions descend
  to the actual SM quotient times H with exact covering pullback. A model
  wrapper and one-generation inhabitant are constructed without support or
  charge-equality premises. Final audits cover zero-generation vacuity,
  finite odd and repeated characters, both neutral and nonneutral supported
  slot choices, kernel invisibility, and the dual phase at i. Existing
  incompatible-IR and SU(6)-independence controls remain active.
  Targeted audit 3906 jobs; 28 new standard-axiom reports (82 axiom-bearing
  reports including imported audits); full regression 4362 jobs. No new
  dependencies, axioms, or amplitude/Grassmann claim. A minimal Physlib
  geometry contribution is documented, not ported/submitted.
  **SU5-1 through SU5-5 are complete in the agreed retained-spectrum scope.**
  See [the theorem](../../../proof/current/applications/GUT/SU5_SELECTION_RULE.md) and
  [the declaration dossier](../../../proof/current/applications/GUT/interfaces/su5-final.md).

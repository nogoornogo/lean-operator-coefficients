# SU(5) embedding, matter and selection rule

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

- Planned the next non-supersymmetric SU(5) target: reusable dependency
  boundary, standard embedding with exact order-six kernel and quotient,
  actual `5`/`bar5`/`10` branching, ordinary-Abelian action/source bridge,
  then the scoped supported-signature and ordered-tensor assembly. The first
  matter class retains `n > 0` copies of `10 + bar5`; no universal SU(5)
  Lagrangian, vacuum dynamics, or decay-amplitude theorem is claimed.
  Finite residual groups and family-dependent actions remain explicit.
  [The plan](../plans/SU5_FORMALIZATION.md) records acceptance gates,
  reuse boundaries, references, and upstream candidates without changing
  dependencies or Lean declarations.
- Completed SU5-1: extracted the independent Abelian charge/character and
  rank-four coefficient APIs, preserving declaration names and leaving the
  actual SU(6) source bridges at their original entry points. New consumers
  import `ResidualGaugeTensor` instead of the legacy `StandardSMResidualTensor`
  adapter. The shared audit checks Lean's transitive module environment and
  rejects any SU(6) import. Proved the exact diagonal-shift equivalence for
  weight normalization and its surjectivity; added independent residual-label
  and hypercharge-sign controls. The finite sign-character positive/negative
  tensor tests are preserved and exercise the new generic conditional tensor
  theorem. No physical-source charge equality is asserted without a source
  proof. Shared audit 3087 jobs, combined legacy/shared audit 3935 jobs,
  full regression 4262 jobs; standard axioms only, no dependency updates.
  The scoped SU(6) endpoints are unchanged and the SU(5) no-go remains a
  target. Next: actual standard SU(5) embedding, exact cyclic kernel, quotient.
- Completed SU5-2: constructed the color-first actual continuous covering
  homomorphism into SU(5), proved its full scalar sixth-root kernel, and
  identified it with the central cyclic group `Multiplicative (ZMod 6)`.
  The quotient is a compact Hausdorff topological group embedded as a closed
  subgroup, with a continuous group equivalence to the image. The audit
  checks the compensated sign kernel element, the uncompensated nonkernel
  element, quotient controls, phase conventions, and transitive SU(6)-free
  imports. Targeted audit 3512 jobs; full regression 4271 jobs; standard
  axioms only. Reused pinned TauCeti compactness and mathlib roots/strict-map
  APIs without changing dependencies. Moved the milestone from ACTIVE to
  COMPLETED. Next: SU5-3 actual representations and branching; the SU(5)
  selection-rule endpoint remains a target.
- Completed SU5-3a, not the entire SU5-3: actual defining, contragredient,
  and exterior-square representations now have checked full covering-group
  branching equivalences, dimensions, and descent through the exact kernel.
  Continuous matrix entries/inverse entries/minors feed a new generic
  finite-basis Hilbert adapter to the pinned TauCeti unitarization theorem;
  it produces equivalent continuous unitary models and quotient actions.
  Reused TauCeti's exterior-power functor and extracted the shared weak
  contragredient/charged epsilon lemmas, retaining all old SU(6) interfaces.
  Audit: 3815 jobs, standard axioms only, SU(6)-free import guard; full
  regression: 4315 jobs. Left-handed hypercharges and wedge signs are tested
  on actual fields. Next is SU5-3b actual `bar5`/`10` irreducibility, with a
  concrete sign/projection and corrected-permutation route recorded as a
  proposal only. Inequivalence by dimension is checked but does not imply
  irreducibility. No commuting-action source or final SU(5) theorem claimed.
- Completed SU5-3b, closing SU5-3: proved irreducibility of the actual
  defining, dual, and exterior-square SU(5) actions with no irreducibility
  source premise. A reusable basis-coordinate criterion reduces the proof
  to invariant coordinate extraction and nonzero mixing coefficients.
  Diagonal signs in SU(5) provide factors 2 and 4; determinant-corrected
  permutations mix the actual bases, using mathlib's extension of finite
  injective pairs. TauCeti equivariant transport proves irreducibility of
  all three continuous unitary models, and unequal dimensions prove the
  unitary `10`/`bar5` inequivalence separately. The matter audit now has 48
  standard-axiom reports and still rejects transitive SU(6) imports.
  Targeted audit: 3821 jobs; full regression: 4318 jobs. No new axioms,
  dependency changes, or native-decision trust extension. ACTIVE now starts
  at SU5-4: commuting ordinary-Abelian action, character sectors, and actual
  supported neutral operators. No final SU(5) endpoint or nonzero amplitude
  is claimed.
- Completed SU5-4: constructed the actual `n(10 + bar5)` source and derived
  its U centralizer as two named U(n) factors using Schur's lemma and the
  existing Hilbert amplification API. Pinned TauCeti common eigenvectors,
  unitary norm preservation, and invariant orthogonal complements give
  exhaustive full circle-character sectors, with distinct sectors orthogonal.
  Actual branching supplies injective supported fields with derived common
  multiplet charges. Both neutral signatures and nonzero invariant ordered
  internal tensors on the field ranges/duals are checked. The range action
  agrees with the ambient action; right-handed characters are inverted via
  contragredients and biduality. Audits include a finite two-generation swap
  that is not scalar, even/odd characters, repeated/trivial sectors, zero
  generations, and an impossible opposite u^c/e^c action in one actual 10.
  Finite-generation gauge unitarity and joint continuity are checked too.
  Source audit: 3901 jobs, 31 standard-axiom reports, SU(6)-free guard. Full
  regression: 4358 jobs. No dependency changes or new axioms. ACTIVE now
  contains only SU5-5 final packaging and contribution planning. The retained
  matter scope is unchanged; neither an amplitude nor Grassmann/Lorentz
  nonvanishing is claimed. See the [source dossier](../../../proof/current/inputs/GUT/interfaces/su5-source.md).
- Completed SU5-5, closing the scoped five-step SU(5) roadmap. The final
  prohibition predicate uses actual injective field support and permits
  independent charge choices at each operator slot. `scoped_no_go` refutes
  it for every positive-generation commuting unitary Abelian action and
  returns both neutral signatures and nonzero ordered internal tensors.
  The full central kernel acts trivially; actual range/dual tensor actions
  descend to the exact SM quotient, with covering pullback and ambient
  field-action agreement. The model wrapper adds no equal-charge/support
  input; a one-generation constructor proves non-vacuity.
  Persistent controls include zero-generation vacuity, genuinely odd finite
  sectors, a nonneutral supported mixed-slot choice in the same source,
  kernel invisibility, inversion at i, and prior incompatible-IR/UV tests.
  New audit: 3906 jobs, 28 standard-axiom reports; 82 axiom-bearing reports
  including imported audits, with no nonstandard axiom. Full build: 4362
  jobs. Dependencies are unchanged and the import closure is SU(6)-free.
  The Physlib group/covering-map geometry candidate and separate extraction
  boundary are documented, not ported or submitted. ACTIVE has no remaining
  task in the agreed roadmap. The theorem is a retained-spectrum selection
  rule, not a Lagrangian, amplitude, or Grassmann nonvanishing theorem.
  See [the endpoint](../../../proof/current/applications/GUT/SU5_SELECTION_RULE.md).

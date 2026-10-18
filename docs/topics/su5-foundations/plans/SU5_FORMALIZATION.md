# Standard SU(5) formalization plan

Archived checkpoint; not a current work queue. Consult the current topic records.

Endpoint status: **LEAN-CHECKED** in the agreed retained-spectrum scope.
Agreed direction: non-supersymmetric SU(5), stage 01.

SU5-1 through SU5-5 are complete. The
[final theorem](../../../proof/current/applications/GUT/SU5_SELECTION_RULE.md) states the proved scope; the milestone
requirements below retain the original acceptance specification.

This is the stable plan, not a running status log. Pending work lives in
[Topic records](../../README.md); verified milestones move to
[Historical milestones](../../proof-program-context/checkpoints/README.md). Existing SU(6) theorems and the generic
character/centralizer results remain unchanged.

## First Theorem Boundary

Start with a concrete, finite-dimensional matter class rather than every
SU(5) model or Lagrangian:

- Gauge group: compact matrix SU(5), with the specified standard SM embedding.
- Matter: `n > 0` copies of `10 + bar5`, with `10 = exteriorPower 2 5`,
  retained as the massless chiral matter before electroweak breaking.
  This retained spectrum is part of the first model class, not inferred from
  a virtual index alone or from arbitrary symmetry-breaking dynamics.
- Residual symmetry: any ordinary Abelian group `H` acting unitarily on this
  actual matter space and commuting with its full SU(5) action. Finite `H`
  and family-dependent actions are included. Physical charges are characters
  `H ->* Circle`, not elements of `H`. No topology on `H` is needed for the
  finite-dimensional simultaneous-sector argument.
- Intended conclusion: this action cannot, by its charge selection rule
  alone, forbid every supported Delta-B = 1 signature in the declared
  dimension-six operator class. Construct at least one supported neutral
  `qque` witness; also retain `duql` when its field-sector witnesses are built.
- Separate tensor conclusion: construct a nonzero invariant **ordered
  internal gauge tensor** on the corresponding actual field spaces.

The endpoint must quantify over the commuting action, not assume equal
charges for Q, u^c, and e^c or assume the conclusion as an orbit certificate.
The multiplicity-space form of the action must be derived. Choosing an
eigenbasis must not silently impose family-universal charges.

This is not a theorem of a nonzero Wilson coefficient, a decay amplitude,
or a proton lifetime. Ordered tensor nonvanishing is not nonvanishing after
Lorentz contraction and the fermionic/Grassmann quotient. No scalar potential,
exact-SM VEV stabilizer, or full Georgi-Glashow Lagrangian is claimed.
The [existing scope distinction](../../../proof/current/applications/GUT/SCOPED_NO_GO_THEOREM.md) remains in force.

## Milestone SU5-1: Shared Boundary and Conventions

The algebra/tensor boundary is now extracted and independently checked;
see [the shared-foundation dossier](../../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md). The
acceptance criteria below remain the specification, not a proof of later
SU(5) source bridges.

Inventory the transitive imports before moving any proof. File placement is
not proof independence: before SU5-1, `StandardModelLocalOperator` imported
SU(6) charge modules and `SMEpsilonTensor` inherited that dependency. Those
imports are now removed, but `StandardSMContragredient` and
`StandardSMExterior` still contain actual SU(6) branching. Extract only the
prerequisites required by the next milestones.
Keep old names/import paths as compatible wrappers where necessary; do not
move an entire SU(6) source adapter merely to reuse its charge-label definition.

Fix these conventions in the new definitions and audits:

1. Color-first `3 + 2` coordinates and integer hypercharge `6Y`.
2. All-left-handed matter branching, with explicit duals when using the
   existing right-handed operator signatures.
3. Distinct covering group `SU(3) x SU(2) x U(1)`, its central quotient,
   and its image in SU(5).
4. If a Laurent model is needed, use `Z^5 / Z(1,1,1,1,1)` or the existing
   canonical rank-four normal form, with a proved evaluator adapter.
   The free five-coordinate model of the SU(6) standard U(5) block is not
   faithful on the SU(5) torus: its coordinate product is one there.
   Ordinary residual charges remain an independent label, not a replacement
   for a determinant exponent. Reuse `StandardAbelianCharge` normalization
   lemmas without importing its SU(6) physical-source assumptions.

Acceptance: the extracted shared modules have no transitive `GUT.SU6`
imports; existing consumers still build with unchanged public statements.
Prefer direct actual branching for the first matter class; do not require a
new universal SU(5) Laurent-model provider merely to handle `5` and `10`.

## Milestone SU5-2: Standard Embedding and Global Form

Status: `LEAN-CHECKED` (stage 01). The three modules under
`GUT/SU5/Embeddings` construct the map, identify its exact central kernel
with `Multiplicative (ZMod 6)`, and prove that the quotient is a compact
Hausdorff topological group embedded as a closed subgroup of SU(5).
The persistent audit checks signs, noninjectivity of the cover, quotient
controls, and transitive independence from SU(6). See the
[declaration and verification dossier](../../../proof/current/inputs/GUT/interfaces/su5-embedding.md).
The statements below describe the discharged acceptance requirements;
later milestones record branching and the selection-rule source separately.

Construct a continuous homomorphism on the actual covering group:

```text
(A,B,z) |-> diag(z^(-2) A, z^3 B) : SU(3) x SU(2) x Circle -> SU(5).
```

Prove unitarity, determinant one, multiplication, and continuity. Prove the
exact kernel formula, not merely exhibit one kernel element:

```text
ker = { (z^2 I_3, z^(-3) I_2, z) | z in Circle, z^6 = 1 }.
```

Identify this kernel with the cyclic group of order six and descend to an
injective continuous map from the quotient. Identify the quotient with the
image as a topological group, with the topology justified explicitly.

Acceptance: a nonidentity kernel witness refutes injectivity of the cover;
the quotient map is injective; the block order and phases match the existing
SM actions. This geometry is independently useful without any no-go theorem.
Do not classify all SM embeddings in SU(5) at this stage.

The pinned mathlib already provides `ZMod.rootsOfUnityAddChar`,
`bijective_rootsOfUnityAddChar`, and `rootsOfUnityCircleEquiv` in
`Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`. Use these for the
finite kernel once its matrix formula is established; do not re-prove the
classification of complex roots of unity. The algebraic first-isomorphism
API is `QuotientGroup.quotientKerEquivRange`. The implementation uses
`ContinuousMulEquiv.quotientKerEquivRange` after proving strictness from
compactness and continuity, so both continuity directions are established.
Compactness of the actual special-unitary groups comes from the pinned
`TauCeti.Topology.Algebra.UnitaryGroup`; no dependency was added or updated.

## Milestone SU5-3: Representations and Actual Branching

Status (stage 01): **SU5-3 is `LEAN-CHECKED`.** SU5-3a establishes actual
algebraic/continuous-unitary representations, all three full-group branching
equivalences, dimensions, and quotient descent. The dual signs are checked
on arbitrary circle elements. The proof uses TauCeti's exterior-power
functor and compact unitarization, not an assumed character realization.
SU5-3b proves actual `5`, `bar5`, and `10` irreducibility using diagonal
sign projections and determinant-corrected permutations, and transfers it
to the continuous unitary realizations. Inequivalence of `10` and `bar5`
is a separate dimension argument, checked in both realizations. See the
[matter dossier](../../../proof/current/inputs/GUT/interfaces/su5-matter.md). The source bridge is recorded
under SU5-4, and the final selection-rule assembly under SU5-5.

Construct `5`, its contragredient `bar5`, and `10 = exteriorPower 2 5`
as actual finite-dimensional continuous unitary representations. Reuse the
generic exterior/dual transport and Hilbertization infrastructure rather
than identifying a formal character with an actual representation by fiat.

Prove full covering-group equivariant equivalences with these left-handed
SM representations (subscripts are `6Y`):

```text
5    = (3,1)_(-2) + (1,2)_3
bar5 = (bar3,1)_2 + (1,2)_(-3)
10   = (bar3,1)_(-4) + (3,2)_1 + (1,1)_6.
```

Prove dimensions 5 and 10, descend the SM actions through the checked kernel,
and connect the resulting maps to the shared field representations. Prove
irreducibility and pairwise inequivalence of `10` and `bar5` before invoking
the generic multiplicity classification with those constituent names.

Acceptance: explicit inverse/linear equivalence, full-group intertwining,
continuity/unitarity, and sign/dual checks; matching weights or dimensions
alone are insufficient. Do not assume a branching certificate that already
contains the desired equivalence.

## Milestone SU5-4: Residual Actions and Operators

Status (stage 01): **`LEAN-CHECKED`.** The actual U centralizer, full
character sectors, field injections, neutral signatures, and nonzero
invariant ordered tensors on actual field ranges/duals are proved. Finite
mixing, repeated characters, trivial actions, zero generations, and an
incompatible within-multiplet assignment are audited. See the
[source dossier](../../../proof/current/inputs/GUT/interfaces/su5-source.md). The requirements below are
discharged; the final scope assembly is recorded under SU5-5.

Apply the completed unitary multiplicity classification to the actual
`n(10 + bar5)` representation. Derive the ordinary symmetry action on its
two multiplicity spaces; use the **U centralizer**, not an unjustified
determinant-one condition on the residual symmetry.

Decompose the Abelian action into full character sectors, allowing repeated
characters and generation mixing. Through the actual branching, derive the
common charges of Q/u^c/e^c and d^c/L within their respective multiplet
sectors. Prove the selected sectors contain actual nonzero field vectors.
Reuse the charge-functional cancellation and the SM tensor transformation
laws to obtain a supported neutral signature and nonzero invariant ordered
internal tensors. At least one witness suffices to refute universal charge
prohibition; do not claim every choice of generations is invariant.

Acceptance: no assumed charge equality or support/nonzero-channel premise.
Include trivial and nontrivial finite residual actions, repeated sectors,
and an incompatible IR charge assignment as a negative control. Explain
that the latter is not a commuting UV source in this matter class.

## Milestone SU5-5: Assembly, Audit, and Upstream Candidate

Status: **`LEAN-CHECKED`** (stage 01). Universal prohibition with independent
per-slot charges is refuted using actual supported fields. Both nonzero
ordered tensors descend to the exact SM quotient, with covering pullback
and ambient-action compatibility. The one-generation model, zero-generation
vacuity, finite odd/mixed slots, kernel, and dual-phase controls are checked.
See [the endpoint dossier](../../../proof/current/applications/GUT/interfaces/su5-final.md). The
[Physlib geometry candidate](../../su5-geometry-upstream/candidate.md) is
identified separately; porting/submission is not claimed.

Assemble the scoped endpoint and an actual one-generation constructor.
Audit zero generations as an excluded/vacuous case, finite torsion charges,
branching dual conventions, kernel descent, and the difference between
signature/tensor nonvanishing and an amplitude. The theorem and each
supporting bridge must build without `sorryAx` or additional axioms; expected
audited axioms are at most `propext`, `Classical.choice`, and `Quot.sound`.

Run targeted persistent audits and the full regression build, preserving the
SU(6) endpoints. Commit each completed milestone with its scope and tests.
Identify a minimal geometry or branching contribution for Physlib and a
separate fork/worktree extraction following the
[upstream workflow](../../../architecture/UPSTREAMING.md). No new dependency,
submission, or upstream acceptance is required to close the local milestone.

## Reuse Map and Placement

| Existing result | Intended use or extraction boundary |
| --- | --- |
| `CharacterRestriction` | Generic conjugacy/restriction API if an orbit proof is used |
| `CharacterExact`, `InvariantWeylMass` | Reserved for a later mass/index extension, not a prerequisite of the first retained-spectrum model |
| `UnitaryMultiplicityClassification` | Actual commuting actions on multiplicity spaces |
| `AbelianCharacterBasis`, `FiniteSemisimpleDecomposition` | Full Abelian sectors, including repeated characters |
| `RepresentationExteriorEquiv`, `FiniteBasisHilbertization` | Actual exterior/dual representation constructions |
| `StandardSMGroup`, `StandardU5Group` | Block-matrix patterns, not an already checked SU(5) quotient theorem |
| `StandardSU5Orbit`, `StandardAbelianCharge` | Permutation/normalization lemmas; distinguish raw and reduced weights |
| `FiniteAbelianChargeSectors`, `StandardBranchProtonObstruction` | Extract generic character labels and charge-functionals only |
| `StandardSMExterior`, `StandardSMContragredient` | Reuse contractions and dual maps, not six-dimensional carriers |
| `StandardModelLocalOperator`, `StandardSMGaugeTensor`, `StandardSMResidualTensor` | Supported signatures and ordered internal tensors after dependency extraction |

Planned paths are `GUT/SU5/Embeddings`, `GUT/SU5/Representations`,
`GUT/SU5/Branching`, `GUT/SU5/ProtonStabilityNoGo`, and their persistent audit
modules. Shared prerequisites stay in `GUT/RepresentationTheory`,
`GUT/FieldTheory`, or `GUT/StandardModel` according to their actual statements.
All listed domains now contain checked modules through SU5-5. The shared,
embedding, matter, source, and final audits enforce transitive SU(6)-free
imports.

## Deferred Work and Stop Conditions

- General SU(5) UV matter with heavy vectorlike fields and invariant masses
  requires a separate actual-mass/source bridge. Reuse the checked character
  index then; do not infer a full light spectrum from its virtual difference.
- SUSY SU(5), R symmetries, non-Abelian protecting groups, SU(N), Spin(10),
  E6, and nonstandard embeddings are later targets, not implicit obligations.
- Vacuum dynamics, an exact-SM stabilizer, Wilson coefficients, decay rates,
  and Lorentz/Grassmann nonvanishing remain separate questions.
- If a target fails, record the counterexample or missing assumption rather
  than force the existing SU(6) conclusion onto the SU(5) class.
- Do not broaden the first theorem to arbitrary representations or all
  SU(5) Lagrangians without a new scope review. There is no justification for
  an unconditional assertion that every SU(5) model has proton decay.

## References and Contribution Check

- [Baez and Huerta, The Algebra of Grand Unified Theories](https://arxiv.org/abs/0904.1556)
  provides the representation-theoretic conventions and standard subgroup
  discussion to compare against the concrete Lean constructions.
- [Physlib's Georgi-Glashow source](https://github.com/leanprover-community/physlib/blob/master/Physlib/Particles/BeyondTheStandardModel/GeorgiGlashow/Basic.lean),
  inspected at stage 01, exposes the embedding, kernel, and quotient as
  informal entries. They are potential contribution targets, not imported
  theorems. Recheck the target revision before extraction and explicitly
  reconcile its block order with our color-first convention.
- [Fornal and Grinstein, SU(5) Unification without Proton Decay](https://arxiv.org/abs/1706.08535)
  uses different matter assignments and parameter relations. It motivates
  the explicit scope boundary, not a claimed counterexample to the planned
  `10 + bar5` charge-selection statement.

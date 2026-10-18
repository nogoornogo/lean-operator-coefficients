# Feasibility of the Concrete Scalar Decomposition

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checked stage 01, continuing `proof/yukawa-full-space` from `checkpoint 01`.
The parent topic's base and integration target remain those in its
[record](README.md); this bounded milestone does not complete that topic.

## Scope and stop condition

Inspect two existing routes, without new foundations or literature premises:
(1) explicit irreducible multiplicity blocks using Schur's lemma, and
(2) tensor powers and Young symmetrizers using TauCeti Schur-Weyl duality.
The endpoint is to identify usable interfaces and any missing theorem-level
prerequisites for the actual SU(6) scalar. Stop when either route reaches the
decomposition or requires a separate theorem package. A source search alone
does not prove API absence; the conclusion below is limited to the inspected
pinned dependencies and local implementation.

## Result

The elementary tensor-square split and Schur's lemma elaborate successfully
over the complex numbers. The inspected Schur-Weyl theorem also builds and
has only the accepted standard axioms. Neither route supplies the concrete
scalar decomposition through existing API calls alone. This is a feasibility
boundary, not a counterexample to the mathematical decomposition.

For `F = C^6`, `A = exteriorSquare F`, the required nontrivial steps include

```text
Sym^2(A*) = (105-dimensional simple summand) + (15-dimensional summand)
A* tensor F = (6-dimensional summand) + (84-dimensional simple summand)
```

Their SU(6) simplicity, pairwise inequivalence, and the identification with
the actual symmetric-form scalar must also be verified. The two-flavor term
requires separating symmetric and alternating factors in
`Sym^2(F tensor C^2)` and transporting the direct-sum expansion. These are
more obligations than the numerical multiplicity calculation.

## Route 1 and its boundary

Mathlib's `Representation.IsIrreducible.finrank_intertwiningMap_self` is
applicable to arbitrary complex group representations with the required
finite-dimensionality and irreducibility. The local `ExplicitMultiplicity`
implementation already supplies off-diagonal vanishing and the description
of every intertwiner by scalar matrices on the multiplicity indices.
Thus the commutant step can reuse existing proofs once a decomposition is given.

The inspected TauCeti `ClassicalGroups` modules construct Weyl modules and
identify one-row and one-column shapes with symmetric and exterior powers.
They do not supply the above mixed products as named representation
equivalences with SU(6) irreducibility certificates. In particular,
`ClassicalGroups/WeylDimension.lean` explicitly describes identification of
its numerical formula with actual irreducible dimensions as downstream of
highest-weight theory. A formula evaluating to 105 or 84 cannot be used as
the missing simplicity proof. The available SU(2) symmetric-power
irreducibility results have a different group and do not fill this obligation.

## Route 2 and its boundary

The checked TauCeti theorem
`centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom` identifies
the commutant of the full GL tensor-power action with the permutation-algebra
image. It does not immediately identify the commutant of a selected symmetric
or alternating subspace, nor the restriction from GL to the actual SU(6)
action. Restriction of an irreducible representation to a subgroup does not
in general preserve irreducibility.

Using it here would require proving the projected tensor-power description
of the relevant mixed products, computing the corresponding permutation
algebra blocks, and justifying the group change. This could become a reusable
proof project, but it is not a short application of the checked theorem.
No such project was started during this bounded test.

## Reproducible probe and checks

The following disposable probe was checked with `lake env lean` after
building the two TauCeti modules. It records exactly what the positive check
establishes; it does not claim a model decomposition.

```lean
import TauCeti.RepresentationTheory.Tensor.Square
import TauCeti.RepresentationTheory.Symmetric.TensorAction.GeneralLinear
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M]

example (rho : Representation ℂ G M) :
    (rho.tensorPower 2).Equiv ((rho.symmetricPower 2).prod (rho.exteriorPower 2)) :=
  rho.tensorSquareEquivSymmetricExterior

example (rho : Representation ℂ G M) [FiniteDimensional ℂ M] [rho.IsIrreducible] :
    Module.finrank ℂ (Representation.IntertwiningMap rho rho) = 1 :=
  Representation.IsIrreducible.finrank_intertwiningMap_self rho

#check TauCeti.centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom
#print axioms Representation.tensorSquareEquivSymmetricExterior
#print axioms Representation.IsIrreducible.finrank_intertwiningMap_self
#print axioms TauCeti.centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom
```

Commands and results:

- `lake build TauCeti.RepresentationTheory.Tensor.Square TauCeti.RepresentationTheory.Symmetric.TensorAction.GeneralLinear`: passed, 2394 jobs.
- `lake env lean <temporary-directory>/yukawa-api-probe.lean`: passed after adding the complex-number import explicitly; the initial probe lacked it and failed instance synthesis.
- The three transitive `#print axioms` checks list only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Documentation links and `git diff --check`: passed.

No repository Lean source, aggregate, pin or assumption was changed. A full
project `lake build` was not rerun: this is a documentation result with focused
external-module builds and disposable elaboration tests, not a new proof baseline.
Lean LSP inspection was not used; source reads and the Lean CLI supplied the
checks. The [library search](literature-review.md) records pinned versions.

## Decision supported by the test

An existing-API-only path to kernel dimension 17 has not been established.
The generic Schur step is largely available; the remaining work is a concrete
representation decomposition and its SU(6) certificates. Accepting the
literature decomposition as an explicit input can close a conditional
dimension statement. A full kernel-checked conclusion instead needs a
separately scoped decomposition proof, or the earlier finite commutant route
with its completeness and actual-group connection. These alternatives remain
for the user's decision; neither boundary has been silently changed.

# Continuing without closed numerical certificates

Assessed at stage 01 at `checkpoint 01`, on the existing
`proof/sm-computable-characters` branch. This is a bounded feasibility result,
not a proof of the remaining Q/L support classification. No active Lean source,
numerical example statement, dependency pin or external input was changed.

## Two distinct endpoints

For `Allowed(T)`, the required statement is existence of a nonzero actual
invariant coefficient, or equivalently a nonzero actual constraint kernel.
Exact multiplicity and rank numerals are stronger optional statements.
Replacing the latter by the former changes a theorem's statement, even when
the intended support application is preserved. The user's previous explicit
replacement decision covered Q18; other exact example statements remain intact.

The [Q18 result](q18-support-results.md) already proves actual kernel support
without a character evaluator or Weyl input. The two legacy numerical example
modules that still prevent a full-build success under the recorded memory
guard are outside that proof's import closure. A resource stop while rebuilding
those examples is not a failure of the structural Q18 proof. Their exact
expensive declarations were not isolated; see the
[recorded verification](q18-support-verification.md).

## Route 1: actual support through compact Hom symmetry

For finite-dimensional continuous representations A and B of a compact group,
with an equivariant self-duality of B, the existing mathematics gives

    Allowed(Hom_G(A tensor B, C)) iff Allowed(Hom_G(B, A)).

First curry to `Hom_G(A,B*)`, identify B* with B, then use
[CompactHomSupport.nonzero_iff](../../../Math/RepresentationTheory/Characters/CompactHomSupport.lean)
to reverse Hom. Its proof uses a proved Haar integral identity symbolically;
it does not evaluate an integral or request a Weyl torus-reduction premise.
For algebraic carriers without norm instances, transport both representations
to equivalent finite analytic models before applying the theorem.

This is useful beyond Q18: the whole exterior source need not be self-dual.
The existing [generation support](../../../Physics/StandardModel/Operators/SMGenerationSupport.lean)
already supplies injective `Sym^m` maps for Q6, Q12, Q18 and L2, L4, L6,
uniformly for even m up to the corresponding degree. They are genuine
statistics-constrained source constituents, but are not by themselves
invariant coefficient witnesses.

The generic connection above passed a temporary Lean probe, reproduced below.
For SM applications, the remaining adapter must construct the equivalent
continuous models, transport weak self-duality and the actual source maps,
restore the exact hypercharge condition using
[SMCombinedChargeSupport](../../../Physics/StandardModel/Operators/SMCombinedChargeSupport.lean),
and use the existing compact/local/kernel equivalences. Existing
[combined continuity models](../../../Physics/StandardModel/Operators/SMCombinedCompactContinuity.lean)
provide source and boson models; restricting them to the semisimple inclusion
still needs its continuity and the explicit representation equivalences.
No SM specialization of the probe is claimed here.

This gives a credible next nonzero-support milestone at Q6, m=2, delta=-2
and L4, m=4, delta=4. It does not prove the old exact dimensions 261 or 6.
Completing the degree-uniform iff further requires central parity/charge
necessity, complementary degrees and conjugate-species transports; the
[previous assessment](support-structure-assessment.md) freezes that wider scope.
The existing [weak capacity theorem](../../../Physics/StandardModel/Operators/SMConstantWeakCapacity.lean)
already gives structural vanishing above the balanced exterior-weight bound.

## Route 2: retain exact dimensions through structural isomorphisms

An exact numeral need not come from exhaustive evaluation. For LLHH,
[LLHHKernelRank.kernelCoordinates](../../../Physics/StandardModel/Operators/LLHHKernelRank.lean)
identifies the actual kernel with functions on symmetric flavor pairs.
`kernel_dimension` then uses the generic cardinality formula to get 6;
`rank` follows by rank-nullity. The matrix is not expanded or row-reduced.

That theorem concerns the actual kernel. The legacy example equations instead
evaluate particular integer character algorithms. Proving an actual kernel
dimension does not silently establish the same unconditional evaluator
equation: a bridge to that evaluator is still required, with its hypotheses
preserved. In particular a conditional Weyl extraction theorem cannot replace
an unconditional arithmetic example without changing the statement.

For Q6 or L4, the inspected constituent injections prove lower bounds only.
They supply neither a spanning theorem nor an upper bound identifying every
copy. Retaining exact dimensions would require an additional complete
decomposition or coefficient-basis theorem. This is a larger separate target
than support; no such complete adapter was established in this pass.

## Probe and verification boundary

With the pinned cached `CompactHomSupport` dependency, the following probe
passed `lake env lean` via the existing guarded runner. It used no closed
character/rank computation, `decide`, new axiom or literature premise.
The axiom print was exactly `propext`, `Classical.choice`, `Quot.sound`.
Elapsed time was 6.0 seconds; sampled process-group peak was 4634784 KiB,
under the 6 GiB stopping threshold with a 4 GiB host reserve. This one probe
does not establish a memory bound for the remaining SM adapters.

Save the following Lean block to a temporary file and run:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py \
  --rss-limit-gib 6 --min-available-gib 4 \
  --require-cached Math.RepresentationTheory.Characters.CompactHomSupport \
  /tmp/sm-compact-coefficient-support.lean /tmp/compact-coefficient-support-assessment.log
```

No full `lake build` or project strict-audit suite was rerun for this
documentation/feasibility pass. The previous full-build resource boundary
remains open. The probe is not a newly registered project theorem or audit.
Documentation checks passed: `node tools/docs/check-links.mjs` checked 866
Markdown files, 5359 local links and 109 fragments with zero errors;
`git diff --check` passed.


```lean
import Math.RepresentationTheory.Characters.CompactHomSupport
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.InvariantCoefficientTransport

namespace Math.CompactCoefficientSupport
set_option autoImplicit false
noncomputable section
open Representation ContinuousRepresentationScope
variable {G A B C D : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]

def homEquiv {a : Representation ℂ G A} {b : Representation ℂ G B}
    {c : Representation ℂ G C} {d : Representation ℂ G D}
    (e : Representation.Equiv a c) (t : Representation.Equiv b d) :
    IntertwiningMap a b ≃ₗ[ℂ] IntertwiningMap c d where
  toFun f := t.toIntertwiningMap.comp (f.comp e.symm.toIntertwiningMap)
  invFun f := t.symm.toIntertwiningMap.comp (f.comp e.toIntertwiningMap)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by
    ext x
    change t (f (e.symm x) + g (e.symm x)) = _
    exact map_add t _ _
  map_smul' z f := by
    ext x
    change t (z • f (e.symm x)) = z • t (f (e.symm x))
    exact map_smul t z _

variable {V W : Type*} [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem reverse_models (a : Representation ℂ G A) (b : Representation ℂ G B)
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (ea : Representation.Equiv a rho) (eb : Representation.Equiv b sigma)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    SelectionCriteria.Allowed (IntertwiningMap a b) ↔
      SelectionCriteria.Allowed (IntertwiningMap b a) :=
  (SelectionCriteria.allowed_equiv (homEquiv ea eb)).trans
    ((CompactHomSupport.nonzero_iff rho sigma hr hs).trans
      (SelectionCriteria.allowed_equiv (homEquiv eb ea)).symm)

theorem coefficient_iff (a : Representation ℂ G A) (b : Representation ℂ G B)
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (ea : Representation.Equiv a rho) (eb : Representation.Equiv b sigma)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (selfDual : Representation.Equiv b b.dual) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b)) ↔
      SelectionCriteria.Allowed (IntertwiningMap b a) :=
  (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv a b)).trans
    ((SelectionCriteria.allowed_equiv
      (InvariantTensorCurry.postcompose a b.dual selfDual.symm)).trans
      (reverse_models a b rho sigma ea eb hr hs))

end
end Math.CompactCoefficientSupport

#print axioms Math.CompactCoefficientSupport.coefficient_iff
```

import Math.LinearAlgebra.Selection.MediatorExchange
import Math.RepresentationTheory.Tensors.InvariantPairing
import Math.RepresentationTheory.Tensors.OrderedInvariantPairing
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientCompleteness

open Math

/-! A generated exchange element, not merely existence of an allowed space.
Invariance may be established from equivariant currents or by a model's
explicit contraction calculation. No nonzero generation is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Physics.MediatorQque
noncomputable section
open Representation
open scoped TensorProduct

variable {H Q U E V : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)

def IsInvariant (M : V ≃ₗ[ℂ] V) (g : ℂ)
    (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V) : Prop :=
  ∀ h z, MediatorExchange.coefficient M g J K
    (((q.tprod q).tprod (u.tprod e)) h z) = MediatorExchange.coefficient M g J K z

def internal (M : V ≃ₗ[ℂ] V) (g : ℂ)
    (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)
    (h : IsInvariant q u e M g J K) :
    IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ H ℂ) where
  toLinearMap := MediatorExchange.coefficient M g J K
  isIntertwining' a := by
    apply LinearMap.ext
    intro z
    exact h a z

def equivariantInternal (r : Representation ℂ H V) (M : Representation.Equiv r r) (g : ℂ)
    (J : IntertwiningMap (q.tprod u) r) (K : IntertwiningMap (q.tprod e) r.dual) :
    IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ H ℂ) :=
  -(g ^ 2) • ((InvariantPairing.evaluation r).comp
    ((M.symm.toIntertwiningMap.comp J).tensor K)).comp
      (OrderedInvariantPairing.swapMiddle q q u e).toIntertwiningMap

theorem equivariantInternal_linear (r : Representation ℂ H V)
    (M : Representation.Equiv r r) (g : ℂ)
    (J : IntertwiningMap (q.tprod u) r) (K : IntertwiningMap (q.tprod e) r.dual) :
    (equivariantInternal q u e r M g J K).toLinearMap =
      MediatorExchange.coefficient M.toLinearEquiv g J.toLinearMap K.toLinearMap := rfl

theorem invariant_of_equivariant (r : Representation ℂ H V)
    (M : Representation.Equiv r r) (g : ℂ)
    (J : IntertwiningMap (q.tprod u) r) (K : IntertwiningMap (q.tprod e) r.dual) :
    IsInvariant q u e M.toLinearEquiv g J.toLinearMap K.toLinearMap := by
  intro a z
  exact congrArg (fun f => f z) ((equivariantInternal q u e r M g J K).isIntertwining' a)

def sector (M : V ≃ₗ[ℂ] V) (g : ℂ)
    (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)
    (h : IsInvariant q u e M g J K) : QqueCoefficientSector.sector q u e :=
  ⟨QqueSpinorExterior.exterior q u e (internal q u e M g J K h),
    QqueCoefficientSector.alternation_mem q u e _⟩

theorem ordered_eq_action (M : V ≃ₗ[ℂ] V) (g : ℂ)
    (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)
    (h : IsInvariant q u e M g J K) (x y : Q) (z : U) (w : E)
    (s t v l : WeylSpinor.Space) :
    QqueSpinorExterior.ordered q u e (internal q u e M g J K h)
      (((x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
        ((z ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] l))) =
      MediatorExchange.action M g (J (x ⊗ₜ[ℂ] z)) (K (y ⊗ₜ[ℂ] w))
        (MediatorExchange.leftSolution M g (J (x ⊗ₜ[ℂ] z)))
        (MediatorExchange.rightSolution M g (K (y ⊗ₜ[ℂ] w))) *
          (SMEpsilonTensor.eps2 s t * SMEpsilonTensor.eps2 v l) := by
  rw [QqueSpinorExterior.ordered_apply]
  change MediatorExchange.coefficient M g J K _ * _ = _
  rw [MediatorExchange.coefficient_eq_action]

section Hom
variable {A B D : Type*}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] Module.Dual ℂ B) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D) := inferInstance

variable
  (M : V ≃ₗ[ℂ] V) (g : ℂ)
  (J : (StandardSMGaugeTensor.Quark ⊗[ℂ] A) ⊗[ℂ]
    (SMEpsilonTensor.Color ⊗[ℂ] Module.Dual ℂ B) →ₗ[ℂ] V)
  (K : (StandardSMGaugeTensor.Quark ⊗[ℂ] A) ⊗[ℂ]
    (ℂ ⊗[ℂ] Module.Dual ℂ D) →ₗ[ℂ] Module.Dual ℂ V)
  (h : IsInvariant (QqueSpinorExterior.qField (a := a))
    (QqueSpinorExterior.uField (b := b)) (QqueSpinorExterior.eField (d := d)) M g J K)

def hom : IntertwiningMap (a.symmetricPower 2) (b.tprod d) :=
  (QqueCoefficientCompleteness.equiv a b d).symm (sector _ _ _ M g J K h)

theorem reconstruct : QqueCoefficientCompleteness.equiv a b d (hom a b d M g J K h) =
    sector _ _ _ M g J K h :=
  (QqueCoefficientCompleteness.equiv a b d).apply_symm_apply _

theorem hom_eq_zero_iff : hom a b d M g J K h = 0 ↔ sector _ _ _ M g J K h = 0 := by
  exact (QqueCoefficientCompleteness.equiv a b d).symm.map_eq_zero_iff

theorem hom_ne_zero_iff : hom a b d M g J K h ≠ 0 ↔ sector _ _ _ M g J K h ≠ 0 :=
  not_congr (hom_eq_zero_iff a b d M g J K h)

end Hom
end
end Physics.MediatorQque

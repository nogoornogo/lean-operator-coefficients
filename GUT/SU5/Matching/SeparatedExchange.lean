import GUT.SU5.Matching.InheritedExchange
import Physics.StandardModel.Operators.BaryonOne.Qque.SeparatedMediatorQque

open Physics

open Math

/-! Conditional SU(5)-core families: representation separation derives the
previous support/mass conditions. Auxiliary symmetry and retained block
identifications remain explicit model inputs, not a new GUT realization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.SeparatedExchange
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor MediatorMatching
open scoped TensorProduct

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Color) := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance

variable {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
  (r : Representation ℂ H Channels) (s : Representation ℂ H W)
  (N : Representation.Equiv (r.prod s) (r.prod s))
  (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)

theorem nonzero_of_source_separation
    (a : Representation ℂ H (Quark ⊗[ℂ] Color))
    (J : IntertwiningMap a (r.prod s))
    (K : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ (Channels × W))
    (hr : IsSemisimpleRepresentation r) (hrs : ¬ CommonIrreducible.Shares r s)
    (ha : IsSemisimpleRepresentation a) (has : ¬ CommonIrreducible.Shares a s)
    (hM : ∀ x, (N (x, 0)).1 = mass g v hg hv x)
    (hJ : ∀ x, (J x).1 = leftCurrent x)
    (hK : ∀ y x, K y (x, 0) = rightCurrent y x) :
    ∃ h : MediatorQque.IsInvariant quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J.toLinearMap K,
      (MediatorQque.sector quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J.toLinearMap K h).val = TreeMatching.matchedExterior g v ∧
      MediatorQque.sector quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J.toLinearMap K h ≠ 0 := by
  have hm : ∀ x, N (x, 0) = (mass g v hg hv x, 0) := by
    intro x
    have hx := SeparatedMediator.core_stable r s hr hrs N.toIntertwiningMap x
    change N (x, 0) = ((N (x, 0)).1, 0) at hx
    rw [hM] at hx
    exact hx
  have hj : ∀ x, J x = (leftCurrent x, 0) := by
    intro x
    have hx := SeparatedMediator.source_support r s a ha has J x
    rw [hJ] at hx
    exact hx
  have heq := MediatorInheritance.coefficient_of_source_support
    (mass g v hg hv) N.toLinearEquiv (LinearMap.inl ℂ Channels W) (g : ℂ)
    hm leftCurrent rightCurrent J.toLinearMap K hj hK
  have hi := QqueMediatorInheritance.invariant quark upRight electronRight
    (mass g v hg hv) N.toLinearEquiv (g : ℂ) leftCurrent rightCurrent
    J.toLinearMap K heq (invariant g v hg hv)
  have hs := QqueMediatorInheritance.sector_eq quark upRight electronRight
    (mass g v hg hv) N.toLinearEquiv (g : ℂ) leftCurrent rightCurrent
    J.toLinearMap K heq (invariant g v hg hv) hi
  refine ⟨hi, ?_, ?_⟩
  · rw [hs]
    exact generated_eq g v hg hv
  · rw [hs]
    exact generated_nonzero g v hg hv

theorem nonzero_of_observer_separation
    (a : Representation ℂ H (Quark ⊗[ℂ] ℂ))
    (J : Quark ⊗[ℂ] Color →ₗ[ℂ] Channels × W)
    (K : IntertwiningMap a (r.prod s).dual)
    (hs : IsSemisimpleRepresentation s) (hsr : ¬ CommonIrreducible.Shares s r)
    (ha : IsSemisimpleRepresentation a) (has : ¬ CommonIrreducible.Shares a s.dual)
    (hM : ∀ x, (N (x, 0)).1 = mass g v hg hv x)
    (hJ : ∀ x, (J x).1 = leftCurrent x)
    (hK : ∀ y x, K y (x, 0) = rightCurrent y x) :
    ∃ h : MediatorQque.IsInvariant quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J K.toLinearMap,
      (MediatorQque.sector quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J K.toLinearMap h).val = TreeMatching.matchedExterior g v ∧
      MediatorQque.sector quark upRight electronRight N.toLinearEquiv
        (g : ℂ) J K.toLinearMap h ≠ 0 := by
  apply InheritedExchange.nonzero_of_projection g v hg hv N.toLinearEquiv
    (LinearMap.fst ℂ Channels W) J K.toLinearMap
  · intro x
    have hp := SeparatedMediator.projection_stable r s hs hsr N.toIntertwiningMap x
    change (N x).1 = (N (x.1, 0)).1 at hp
    exact hp.trans (hM x.1)
  · exact hJ
  · intro y x
    exact (SeparatedMediator.dual_support r s a ha has K y x).trans (hK y x.1)

end
end GUT.SU5.SeparatedExchange

import GUT.SU5.Matching.MediatorMatching
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance

open Physics

open Math

/-! Families retaining the SU(5) exchange under structural support conditions.
These are conditional paired-mediator models, not new larger-GUT realizations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.InheritedExchange
noncomputable section
open StandardSMGaugeTensor SMEpsilonTensor MediatorMatching MediatorInheritance
open scoped TensorProduct

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Color) := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem nonzero_of_projection (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (N : W ≃ₗ[ℂ] W) (p : W →ₗ[ℂ] Channels)
    (L : Quark ⊗[ℂ] Color →ₗ[ℂ] W) (R : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ W)
    (hM : ∀ x, p (N x) = mass g v hg hv (p x))
    (hJ : ∀ x, p (L x) = leftCurrent x)
    (hK : ∀ y x, R y x = rightCurrent y (p x)) :
    ∃ h : MediatorQque.IsInvariant quark upRight electronRight N (g : ℂ) L R,
      (MediatorQque.sector quark upRight electronRight N (g : ℂ) L R h).val =
        TreeMatching.matchedExterior g v ∧
      MediatorQque.sector quark upRight electronRight N (g : ℂ) L R h ≠ 0 := by
  have heq := coefficient_of_observer_support (mass g v hg hv) N p (g : ℂ)
    hM leftCurrent rightCurrent L R hJ hK
  have hi := QqueMediatorInheritance.invariant quark upRight electronRight
    (mass g v hg hv) N (g : ℂ) leftCurrent rightCurrent L R heq (invariant g v hg hv)
  have hs := QqueMediatorInheritance.sector_eq quark upRight electronRight
    (mass g v hg hv) N (g : ℂ) leftCurrent rightCurrent L R heq (invariant g v hg hv) hi
  refine ⟨hi, ?_, ?_⟩
  · rw [hs]
    exact generated_eq g v hg hv
  · rw [hs]
    exact generated_nonzero g v hg hv

variable (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
  (N : W ≃ₗ[ℂ] W) (L : Quark ⊗[ℂ] Color →ₗ[ℂ] W)

theorem spectator_invariant : MediatorQque.IsInvariant quark upRight electronRight
    ((mass g v hg hv).prodCongr N) (g : ℂ) (leftCurrent.prod L) (sumDual rightCurrent 0) := by
  apply QqueMediatorInheritance.invariant quark upRight electronRight
    (mass g v hg hv) _ (g : ℂ) leftCurrent rightCurrent
  · exact spectator_observer_zero _ _ _ _ _ _
  · exact invariant g v hg hv

def spectatorSector := MediatorQque.sector quark upRight electronRight
  ((mass g v hg hv).prodCongr N) (g : ℂ) (leftCurrent.prod L) (sumDual rightCurrent 0)
    (spectator_invariant g v hg hv N L)

theorem spectatorSector_eq : spectatorSector g v hg hv N L = generated g v hg hv := by
  exact QqueMediatorInheritance.sector_eq quark upRight electronRight
    (mass g v hg hv) _ (g : ℂ) leftCurrent rightCurrent _ _
    (spectator_observer_zero _ _ _ _ _ _) (invariant g v hg hv) _

theorem spectatorSector_nonzero : spectatorSector g v hg hv N L ≠ 0 := by
  rw [spectatorSector_eq]
  exact generated_nonzero g v hg hv

omit N L in
/-- The same nonzero core can be embedded in a completely cancelling doubled
exchange. This is an algebraic control, not a realized GUT counterexample. -/
theorem retained_core_can_cancel :
    coefficient g v hg hv ≠ 0 ∧
      MediatorExchange.coefficient ((mass g v hg hv).prodCongr (mass g v hg hv))
        (g : ℂ) (leftCurrent.prod leftCurrent) (sumDual rightCurrent (-rightCurrent)) = 0 := by
  constructor
  · intro h
    have hp := DFunLike.congr_fun h
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1)) ⊗ₜ[ℂ]
        (colorBasis 2 ⊗ₜ[ℂ] (1 : ℂ)))
    rw [coefficient_eq] at hp
    change TreeMatching.orderedWilson g v * qque _ = 0 at hp
    rw [qque_tmul] at hp
    norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff] at hp
    exact TreeMatching.orderedWilson_ne_zero hg hv hp
  · exact duplicate_cancellation _ _ _ _

end
end GUT.SU5.InheritedExchange

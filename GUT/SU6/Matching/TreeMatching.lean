import GUT.SU6.Matching.AdjointMass
import GUT.SU5.Matching.MediatorMatching
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance

open Physics

open Math

/-! Full broken-root exchange on the retained SU(6) fifteen's Q/up/e fields.
Extra currents are computed from the exterior action before being proved zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6.TreeMatching
noncomputable section
open StandardSMGaugeTensor SMEpsilonTensor ExteriorCurrents
open scoped TensorProduct

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Color) := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance

abbrev Extra := Fin 5 → ℂ

def extraPairing : Extra →ₗ[ℂ] Module.Dual ℂ Extra :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, x i * y i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

def retainedLeft : Quark ⊗[ℂ] Color →ₗ[ℂ] SU5.MediatorMatching.Channels :=
  LinearMap.pi fun a => LinearMap.pi fun w => TensorProduct.lift (upCurrent (.inl (a,w)))
def extraLeft : Quark ⊗[ℂ] Color →ₗ[ℂ] Extra :=
  LinearMap.pi fun i => TensorProduct.lift (upCurrent (.inr i))
def retainedRight : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ SU5.MediatorMatching.Channels :=
  SU5.MediatorMatching.pairing.comp (LinearMap.pi fun a => LinearMap.pi fun w =>
    TensorProduct.lift (electronCurrent (.inl (a,w))))
def extraRight : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ Extra :=
  extraPairing.comp (LinearMap.pi fun i => TensorProduct.lift (electronCurrent (.inr i)))

theorem retainedLeft_eq : retainedLeft = SU5.MediatorMatching.leftCurrent := by
  simp only [retainedLeft, upCurrent_core, SU5.MediatorMatching.leftCurrent]
theorem retainedRight_eq : retainedRight = SU5.MediatorMatching.rightCurrent := by
  simp only [retainedRight, electronCurrent_core, SU5.MediatorMatching.rightCurrent]
theorem extraLeft_zero : extraLeft = 0 := by
  ext q u i
  simp [extraLeft, upCurrent_extra]
theorem extraRight_zero : extraRight = 0 := by
  ext q e z
  simp [extraRight, extraPairing, electronCurrent_extra]

def leftCurrent := retainedLeft.prod extraLeft
def rightCurrent := MediatorInheritance.sumDual retainedRight extraRight

theorem leftCurrent_eq : leftCurrent = SU5.MediatorMatching.leftCurrent.prod
    (0 : Quark ⊗[ℂ] Color →ₗ[ℂ] Extra) := by
  rw [leftCurrent, retainedLeft_eq, extraLeft_zero]
theorem rightCurrent_eq : rightCurrent = MediatorInheritance.sumDual SU5.MediatorMatching.rightCurrent
    (0 : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ Extra) := by
  rw [rightCurrent, retainedRight_eq, extraRight_zero]

def extraMass (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : Extra ≃ₗ[ℂ] Extra :=
  LinearEquiv.piCongrRight fun i =>
    MediatorExchange.scalarMass (AdjointMass.massSquared g v (.inr i) : ℂ)
      (AdjointMass.massSquared_ne_zero g v hg hv (.inr i))

def mass (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  (SU5.MediatorMatching.mass g v hg hv).prodCongr (extraMass g v hg hv)

def coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : QQueSpace →ₗ[ℂ] ℂ :=
  MediatorExchange.coefficient (mass g v hg hv) (g : ℂ) leftCurrent rightCurrent

theorem coefficient_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    coefficient g v hg hv = SU5.MediatorMatching.coefficient g v hg hv := by
  rw [coefficient, leftCurrent_eq, rightCurrent_eq]
  exact MediatorInheritance.spectator_observer_zero _ _ _ _ _ _

theorem invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorQque.IsInvariant quark upRight electronRight (mass g v hg hv)
      (g : ℂ) leftCurrent rightCurrent :=
  QqueMediatorInheritance.invariant quark upRight electronRight
    (SU5.MediatorMatching.mass g v hg hv) (mass g v hg hv) (g : ℂ)
    SU5.MediatorMatching.leftCurrent SU5.MediatorMatching.rightCurrent leftCurrent rightCurrent
    (coefficient_eq g v hg hv) (SU5.MediatorMatching.invariant g v hg hv)

def generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorQque.sector quark upRight electronRight (mass g v hg hv) (g : ℂ)
    leftCurrent rightCurrent (invariant g v hg hv)

theorem generated_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    generated g v hg hv = SU5.MediatorMatching.generated g v hg hv :=
  QqueMediatorInheritance.sector_eq quark upRight electronRight
    (SU5.MediatorMatching.mass g v hg hv) (mass g v hg hv) (g : ℂ)
    SU5.MediatorMatching.leftCurrent SU5.MediatorMatching.rightCurrent leftCurrent rightCurrent
    (coefficient_eq g v hg hv) (SU5.MediatorMatching.invariant g v hg hv) (invariant g v hg hv)

theorem generated_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : generated g v hg hv ≠ 0 := by
  rw [generated_eq]
  exact SU5.MediatorMatching.generated_nonzero g v hg hv

theorem full_action_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (q r : Quark) (u : Color) (e : ℂ) :
    MediatorExchange.action (mass g v hg hv) (g : ℂ)
      (leftCurrent (q ⊗ₜ[ℂ] u)) (rightCurrent (r ⊗ₜ[ℂ] e))
      (MediatorExchange.leftSolution (mass g v hg hv) (g : ℂ) (leftCurrent (q ⊗ₜ[ℂ] u)))
      (MediatorExchange.rightSolution (mass g v hg hv) (g : ℂ) (rightCurrent (r ⊗ₜ[ℂ] e))) =
      SU5.TreeMatching.orderedWilson g v * qque ((q ⊗ₜ[ℂ] r) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  rw [← MediatorExchange.coefficient_eq_action]
  change coefficient g v hg hv _ = _
  rw [coefficient_eq, SU5.MediatorMatching.coefficient_eq]
  rfl

end
end GUT.SU6.TreeMatching

import GUT.SUN.Matching.ExteriorCurrents
import GUT.SU5.Matching.MediatorMatching
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance

open Physics

open Math

/-! Exact matching on the full massive root sector of variable diagonal
backgrounds. Degenerate spectator weights need no inverse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SUN.TreeMatching

noncomputable section
open DiagonalBackground ExteriorCurrents StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Color) := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance
variable {r : ℕ} (D : Background r)

abbrev Extra := D.ExtraRoot → ℂ
def extraPairing : Extra D →ₗ[ℂ] Module.Dual ℂ (Extra D) :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, x i * y i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

def retainedLeft : Quark ⊗[ℂ] Color →ₗ[ℂ] SU5.MediatorMatching.Channels :=
  LinearMap.pi fun i => LinearMap.pi fun w => TensorProduct.lift (upCurrent D (.inl (i,w)))
def extraLeft : Quark ⊗[ℂ] Color →ₗ[ℂ] Extra D :=
  LinearMap.pi fun c => TensorProduct.lift (upCurrent D (.inr c))
def retainedRight : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ SU5.MediatorMatching.Channels :=
  SU5.MediatorMatching.pairing.comp (LinearMap.pi fun i => LinearMap.pi fun w =>
    TensorProduct.lift (electronCurrent D (.inl (i,w))))
def extraRight : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ (Extra D) :=
  (extraPairing D).comp (LinearMap.pi fun c => TensorProduct.lift (electronCurrent D (.inr c)))

theorem retainedLeft_eq : retainedLeft D = SU5.MediatorMatching.leftCurrent := by
  simp only [retainedLeft, upCurrent_core, SU5.MediatorMatching.leftCurrent]
theorem retainedRight_eq : retainedRight D = SU5.MediatorMatching.rightCurrent := by
  simp only [retainedRight, electronCurrent_core, SU5.MediatorMatching.rightCurrent]
theorem extraLeft_zero : extraLeft D = 0 := by
  ext q u i
  simp [extraLeft, upCurrent_extra]
theorem extraRight_zero : extraRight D = 0 := by
  ext q e z
  simp [extraRight, extraPairing, electronCurrent_extra]

def leftCurrent := (retainedLeft D).prod (extraLeft D)
def rightCurrent := MediatorInheritance.sumDual (retainedRight D) (extraRight D)
theorem leftCurrent_eq : leftCurrent D = SU5.MediatorMatching.leftCurrent.prod
    (0 : Quark ⊗[ℂ] Color →ₗ[ℂ] Extra D) := by
  rw [leftCurrent, retainedLeft_eq, extraLeft_zero]
theorem rightCurrent_eq : rightCurrent D = MediatorInheritance.sumDual SU5.MediatorMatching.rightCurrent
    (0 : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ (Extra D)) := by
  rw [rightCurrent, retainedRight_eq, extraRight_zero]

def extraMass (g : ℝ) (hg : g ≠ 0) : Extra D ≃ₗ[ℂ] Extra D :=
  LinearEquiv.piCongrRight fun c =>
    MediatorExchange.scalarMass (D.massSquared g (.inr c) : ℂ)
      (D.massSquared_ne_zero g hg (.inr c))
def mass (g : ℝ) (hg : g ≠ 0) :=
  (SU5.MediatorMatching.mass g D.effectiveV hg D.effectiveV_ne_zero).prodCongr (extraMass D g hg)

theorem mass_core_apply (g : ℝ) (hg : g ≠ 0)
    (x : SU5.MediatorMatching.Channels × Extra D) (i : Fin 3) (w : Fin 2) :
    (mass D g hg x).1 i w = (D.massSquared g (.inl (i,w)) : ℂ) * x.1 i w := by
  rw [D.core_mass]
  rfl
theorem mass_extra_apply (g : ℝ) (hg : g ≠ 0)
    (x : SU5.MediatorMatching.Channels × Extra D) (c : D.ExtraRoot) :
    (mass D g hg x).2 c = (D.massSquared g (.inr c) : ℂ) * x.2 c := rfl

def coefficient (g : ℝ) (hg : g ≠ 0) : QQueSpace →ₗ[ℂ] ℂ :=
  MediatorExchange.coefficient (mass D g hg) (g : ℂ) (leftCurrent D) (rightCurrent D)
theorem coefficient_eq (g : ℝ) (hg : g ≠ 0) :
    coefficient D g hg = SU5.MediatorMatching.coefficient g D.effectiveV hg D.effectiveV_ne_zero := by
  rw [coefficient, leftCurrent_eq, rightCurrent_eq]
  exact MediatorInheritance.spectator_observer_zero _ _ _ _ _ _

theorem invariant (g : ℝ) (hg : g ≠ 0) :
    MediatorQque.IsInvariant quark upRight electronRight (mass D g hg)
      (g : ℂ) (leftCurrent D) (rightCurrent D) :=
  QqueMediatorInheritance.invariant quark upRight electronRight
    (SU5.MediatorMatching.mass g D.effectiveV hg D.effectiveV_ne_zero) (mass D g hg) (g : ℂ)
    SU5.MediatorMatching.leftCurrent SU5.MediatorMatching.rightCurrent (leftCurrent D) (rightCurrent D)
    (coefficient_eq D g hg) (SU5.MediatorMatching.invariant g D.effectiveV hg D.effectiveV_ne_zero)
def generated (g : ℝ) (hg : g ≠ 0) :=
  MediatorQque.sector quark upRight electronRight (mass D g hg) (g : ℂ)
    (leftCurrent D) (rightCurrent D) (invariant D g hg)
theorem generated_eq (g : ℝ) (hg : g ≠ 0) :
    generated D g hg = SU5.MediatorMatching.generated g D.effectiveV hg D.effectiveV_ne_zero :=
  QqueMediatorInheritance.sector_eq quark upRight electronRight
    (SU5.MediatorMatching.mass g D.effectiveV hg D.effectiveV_ne_zero) (mass D g hg) (g : ℂ)
    SU5.MediatorMatching.leftCurrent SU5.MediatorMatching.rightCurrent (leftCurrent D) (rightCurrent D)
    (coefficient_eq D g hg) (SU5.MediatorMatching.invariant g D.effectiveV hg D.effectiveV_ne_zero)
    (invariant D g hg)
theorem generated_nonzero (g : ℝ) (hg : g ≠ 0) : generated D g hg ≠ 0 := by
  rw [generated_eq]
  exact SU5.MediatorMatching.generated_nonzero g D.effectiveV hg D.effectiveV_ne_zero

theorem wilson_value (g : ℝ) (hg : g ≠ 0) :
    SU5.TreeMatching.orderedWilson g D.effectiveV = -1 / ((D.a : ℂ) - (D.b : ℂ))^2 := by
  rw [SU5.TreeMatching.orderedWilson_value hg D.effectiveV_ne_zero]
  simp only [Background.effectiveV, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]
  congr 1
  ring

theorem full_action_eq (g : ℝ) (hg : g ≠ 0) (q s : Quark) (u : Color) (e : ℂ) :
    MediatorExchange.action (mass D g hg) (g : ℂ)
      (leftCurrent D (q ⊗ₜ[ℂ] u)) (rightCurrent D (s ⊗ₜ[ℂ] e))
      (MediatorExchange.leftSolution (mass D g hg) (g : ℂ) (leftCurrent D (q ⊗ₜ[ℂ] u)))
      (MediatorExchange.rightSolution (mass D g hg) (g : ℂ) (rightCurrent D (s ⊗ₜ[ℂ] e))) =
      (-1 / ((D.a : ℂ) - (D.b : ℂ))^2) * qque ((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  rw [← MediatorExchange.coefficient_eq_action]
  change coefficient D g hg _ = _
  rw [coefficient_eq, SU5.MediatorMatching.coefficient_eq, wilson_value D g hg]
  rfl

end
end GUT.SUN.TreeMatching

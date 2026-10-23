import GUT.SUN.Matching.ConjugatedMatter
import GUT.SUN.Matching.TreeMatching
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorTransport

open Physics

open Math

/-! Recompute rotated currents before changing the massive mediator carrier.
Equality of the generated qque sector is a conclusion, never an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SUN.ConjugatedMatching

noncomputable section
open DiagonalBackground StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Color) := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] ℂ) := inferInstance
variable {r : ℕ} (U : ExteriorMatter.Group r) (D : Background r)

abbrev Carrier := SU5.MediatorMatching.Channels × TreeMatching.Extra D
def rawLeft : Quark ⊗[ℂ] Color →ₗ[ℂ] Carrier D :=
  (LinearMap.pi fun i => LinearMap.pi fun w =>
    TensorProduct.lift (ConjugatedMatter.upCurrent U D (.inl (i,w)))).prod
      (LinearMap.pi fun c => TensorProduct.lift (ConjugatedMatter.upCurrent U D (.inr c)))
def rawRight : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ (Carrier D) :=
  MediatorInheritance.sumDual
    (SU5.MediatorMatching.pairing.comp (LinearMap.pi fun i => LinearMap.pi fun w =>
      TensorProduct.lift (ConjugatedMatter.electronCurrent U D (.inl (i,w)))))
    ((TreeMatching.extraPairing D).comp (LinearMap.pi fun c =>
      TensorProduct.lift (ConjugatedMatter.electronCurrent U D (.inr c))))

theorem rawLeft_eq : rawLeft U D = TreeMatching.leftCurrent D := by
  simp only [rawLeft, ConjugatedMatter.upCurrent_eq, TreeMatching.leftCurrent,
    TreeMatching.retainedLeft, TreeMatching.extraLeft]
theorem rawRight_eq : rawRight U D = TreeMatching.rightCurrent D := by
  simp only [rawRight, ConjugatedMatter.electronCurrent_eq, TreeMatching.rightCurrent,
    TreeMatching.retainedRight, TreeMatching.extraRight]

theorem rawInvariant (g : ℝ) (hg : g ≠ 0) :
    MediatorQque.IsInvariant quark upRight electronRight (TreeMatching.mass D g hg)
      (g : ℂ) (rawLeft U D) (rawRight U D) := by
  rw [rawLeft_eq, rawRight_eq]
  exact TreeMatching.invariant D g hg

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Carrier D ≃ₗ[ℂ] W)
def mass (g : ℝ) (hg : g ≠ 0) := MediatorTransport.mass T (TreeMatching.mass D g hg)
def leftCurrent := MediatorTransport.source T (rawLeft U D)
def rightCurrent := MediatorTransport.observer T (rawRight U D)
def coefficient (g : ℝ) (hg : g ≠ 0) :=
  MediatorExchange.coefficient (mass D T g hg) (g : ℂ) (leftCurrent U D T) (rightCurrent U D T)

theorem coefficient_eq (g : ℝ) (hg : g ≠ 0) :
    coefficient U D T g hg = TreeMatching.coefficient D g hg := by
  rw [coefficient, leftCurrent, rightCurrent, mass, MediatorTransport.coefficient_eq,
    rawLeft_eq, rawRight_eq]
  rfl

def generated (g : ℝ) (hg : g ≠ 0) :=
  QqueMediatorTransport.generated quark upRight electronRight T (TreeMatching.mass D g hg)
    (g : ℂ) (rawLeft U D) (rawRight U D) (rawInvariant U D g hg)

theorem generated_eq (g : ℝ) (hg : g ≠ 0) :
    generated U D T g hg = TreeMatching.generated D g hg := by
  rw [generated, QqueMediatorTransport.generated_eq]
  apply QqueMediatorInheritance.sector_eq quark upRight electronRight
    (TreeMatching.mass D g hg) (TreeMatching.mass D g hg) (g : ℂ)
    (TreeMatching.leftCurrent D) (TreeMatching.rightCurrent D) (rawLeft U D) (rawRight U D)
  rw [rawLeft_eq, rawRight_eq]

theorem generated_nonzero (g : ℝ) (hg : g ≠ 0) : generated U D T g hg ≠ 0 := by
  rw [generated_eq]
  exact TreeMatching.generated_nonzero D g hg

theorem action_eq (g : ℝ) (hg : g ≠ 0) (q s : Quark) (u : Color) (e : ℂ)
    (x : Carrier D) (y : Module.Dual ℂ (Carrier D)) :
    MediatorExchange.action (mass D T g hg) (g : ℂ)
      (leftCurrent U D T (q ⊗ₜ[ℂ] u)) (rightCurrent U D T (s ⊗ₜ[ℂ] e))
      (T x) (y.comp T.symm.toLinearMap) =
      MediatorExchange.action (TreeMatching.mass D g hg) (g : ℂ)
        (TreeMatching.leftCurrent D (q ⊗ₜ[ℂ] u)) (TreeMatching.rightCurrent D (s ⊗ₜ[ℂ] e)) x y := by
  calc
    _ = MediatorExchange.action (TreeMatching.mass D g hg) (g : ℂ)
        (rawLeft U D (q ⊗ₜ[ℂ] u)) (rawRight U D (s ⊗ₜ[ℂ] e)) x y :=
      MediatorTransport.action_eq T (TreeMatching.mass D g hg) (g : ℂ)
        (rawLeft U D (q ⊗ₜ[ℂ] u)) (rawRight U D (s ⊗ₜ[ℂ] e)) x y
    _ = _ := by rw [rawLeft_eq, rawRight_eq]

theorem full_action_eq (g : ℝ) (hg : g ≠ 0) (q s : Quark) (u : Color) (e : ℂ) :
    MediatorExchange.action (mass D T g hg) (g : ℂ)
      (leftCurrent U D T (q ⊗ₜ[ℂ] u)) (rightCurrent U D T (s ⊗ₜ[ℂ] e))
      (MediatorExchange.leftSolution (mass D T g hg) (g : ℂ) (leftCurrent U D T (q ⊗ₜ[ℂ] u)))
      (MediatorExchange.rightSolution (mass D T g hg) (g : ℂ) (rightCurrent U D T (s ⊗ₜ[ℂ] e))) =
      (-1 / ((D.a : ℂ) - (D.b : ℂ))^2) * qque ((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  rw [← MediatorExchange.coefficient_eq_action]
  change coefficient U D T g hg _ = _
  rw [coefficient_eq, TreeMatching.coefficient_eq, SU5.MediatorMatching.coefficient_eq,
    TreeMatching.wilson_value D g hg]
  rfl

end
end GUT.SUN.ConjugatedMatching

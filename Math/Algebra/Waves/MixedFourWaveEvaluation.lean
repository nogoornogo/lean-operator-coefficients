import Math.Algebra.Jets.MixedJetConstantOdd
import Math.Algebra.Waves.ColoredFourWaveEvaluation
import Math.Algebra.Jets.TwoSidedDifferentialNormalForm

/-! Full-source Grassmann/four-wave evaluation. Positive odd jets are removed
in an exterior algebra, while even jets retain the ordinary wave derivative.
The resulting linear probes kill all IBP for conserving momenta. -/
namespace Math.MixedFourWaveEvaluation
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open MixedJetAlgebra
variable {F B : Type*}
  (k : Fin 4 → Fin 4 → ℂ) (v : B → Fin 4 → ℂ)
abbrev Target (F : Type*) := ExteriorAlgebra ℂ (JetLinear.Field F) ⊗[ℂ] FourWaveEvaluation.P

def evaluation : Algebra F B (Fin 4) →ₐ[ℂ] Target F :=
  Algebra.TensorProduct.map MixedJetConstantOdd.project (ColoredFourWaveEvaluation.evaluation k v)

@[simp] theorem evaluation_tmul (x : Odd F (Fin 4)) (p : Even B (Fin 4)) :
    evaluation k v (x ⊗ₜ[ℂ] p) = MixedJetConstantOdd.project x ⊗ₜ[ℂ]
      ColoredFourWaveEvaluation.evaluation k v p := rfl

def derivative (i : Fin 4) : Target F →ₗ[ℂ] Target F :=
  TensorProduct.map LinearMap.id (FourWaveEvaluation.d k i).toLinearMap

theorem evaluation_derivative (i : Fin 4) (p : Algebra F B (Fin 4)) :
    evaluation k v (totalDerivative i p) = derivative k i (evaluation k v p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add,hp,hq]
  | tmul x p =>
    simp [totalDerivative_tmul,MixedJetConstantOdd.project_derivative,
      ColoredFourWaveEvaluation.derivative,derivative]

/-- Kernel stability deals with the entire unbounded two-sided closure. -/
theorem equations_zero (R : Set (Algebra F B (Fin 4)))
    (hR : ∀ r ∈ R, evaluation k v r = 0) {p : Algebra F B (Fin 4)}
    (hp : p ∈ TwoSidedDifferential.relations totalDerivative R) :
    evaluation k v p = 0 := by
  have hle : TwoSidedDifferential.relations totalDerivative R ≤
      (evaluation k v).toLinearMap.ker := by
    apply TwoSidedDifferential.minimal
    · exact hR
    · intro a p hp
      change evaluation k v (a*p) = 0
      rw [map_mul,show evaluation k v p = 0 from hp,mul_zero]
    · intro a p hp
      change evaluation k v (p*a) = 0
      rw [map_mul,show evaluation k v p = 0 from hp,zero_mul]
    · intro i p hp
      change evaluation k v (totalDerivative i p) = 0
      rw [evaluation_derivative,show evaluation k v p = 0 from hp,map_zero]
  exact hle hp

def probe (f : ExteriorAlgebra ℂ (JetLinear.Field F) →ₗ[ℂ] ℂ) :
    Algebra F B (Fin 4) →ₗ[ℂ] ℂ :=
  ((LinearMap.mul' ℂ ℂ).comp (TensorProduct.map f FourWaveEvaluation.coefficient)).comp
    (evaluation k v).toLinearMap

@[simp] theorem probe_tmul (f : ExteriorAlgebra ℂ (JetLinear.Field F) →ₗ[ℂ] ℂ)
    (x : Odd F (Fin 4)) (p : Even B (Fin 4)) :
    probe k v f (x ⊗ₜ[ℂ] p) = f (MixedJetConstantOdd.project x) *
      ColoredFourWaveEvaluation.onJets k v p := rfl

theorem probe_derivative (f : ExteriorAlgebra ℂ (JetLinear.Field F) →ₗ[ℂ] ℂ)
    (hc : ∀ i, ∑ s : Fin 4, k s i = 0) (i : Fin 4)
    (p : Algebra F B (Fin 4)) : probe k v f (totalDerivative i p) = 0 := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | tmul x p =>
    simp [totalDerivative_tmul,MixedJetConstantOdd.project_derivative,
      ColoredFourWaveEvaluation.divergence_zero k v hc]

theorem annihilates (f : ExteriorAlgebra ℂ (JetLinear.Field F) →ₗ[ℂ] ℂ)
    (hc : ∀ i, ∑ s : Fin 4, k s i = 0)
    (R : Set (Algebra F B (Fin 4))) (hR : ∀ r ∈ R, evaluation k v r = 0) :
    TwoSidedDifferential.combined totalDerivative R ≤ (probe k v f).ker := by
  apply sup_le
  · intro p hp
    change ((LinearMap.mul' ℂ ℂ).comp
      (TensorProduct.map f FourWaveEvaluation.coefficient)) (evaluation k v p) = 0
    rw [equations_zero k v R hR hp,map_zero]
  · rintro _ ⟨w,rfl⟩
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add u w hu hw => simpa only [map_add] using (probe k v f).ker.add_mem hu hw
    | single i p =>
      rw [VariationalIBP.divergence_single]
      exact probe_derivative k v f hc i p

end
end Math.MixedFourWaveEvaluation

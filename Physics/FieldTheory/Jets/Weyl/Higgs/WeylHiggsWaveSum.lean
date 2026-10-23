import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveValues
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic

/-! Four null directions reconstruct the inverse-Pauli moment. The sum
already kills all full relations; its group invariance is a separate step. -/
namespace Physics.WeylHiggsWaveSum
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsWaves
def momentum : Fin 4 → Fin 4 → ℂ :=
  ![![1,0,0,1],![1,0,0,-1],![1,1,0,0],![1,0,1,0]]

theorem null (s : Fin 4) :
    (momentum s 0)^2-(momentum s 1)^2-(momentum s 2)^2-(momentum s 3)^2 = 0 := by
  fin_cases s <;> norm_num [momentum]

def weight (a b : Fin 2) : Fin 4 → ℂ :=
  if a = 0 then
    if b = 0 then ![2,0,0,0] else ![-1-Complex.I,-1-Complex.I,2,2*Complex.I]
  else
    if b = 0 then ![-1+Complex.I,-1+Complex.I,2,-2*Complex.I] else ![0,2,0,0]

theorem moment (a b : Fin 2) (i : Fin 4) :
    (∑ s : Fin 4, weight a b s * momentum s i) = 2*WeylDirectionInvariant.kernel a b i := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [weight,momentum,Fin.sum_univ_succ,WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
  all_goals ring

def bySpin (a b : Fin 2) : A →ₗ[ℂ] ℂ :=
  ∑ s : Fin 4, weight a b s • (∑ x : Fin 2, ∑ y : Fin 2, probe (momentum s) a b x y)
def functional : A →ₗ[ℂ] ℂ := ∑ a : Fin 2, ∑ b : Fin 2, bySpin a b

theorem bySpin_annihilates (a b : Fin 2) : input.relations ≤ (bySpin a b).ker := by
  intro p hp
  have hz (s : Fin 4) (x y : Fin 2) : probe (momentum s) a b x y p = 0 :=
    WeylHiggsWaves.annihilates (momentum s) (null s) a b x y hp
  change bySpin a b p = 0
  simp [bySpin,LinearMap.sum_apply,LinearMap.smul_apply,hz]

theorem annihilates : input.relations ≤ functional.ker := by
  intro p hp
  have hz (a b : Fin 2) : bySpin a b p = 0 := bySpin_annihilates a b hp
  simp [functional,hz]

theorem color_sum (p : Fin 4 → ℂ) (a b : Fin 2) :
    (∑ x : Fin 2, ∑ y : Fin 2, probe p a b x y DerivativeLiteratureMixed.candidate) =
      (24*Complex.I)*∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b * p i := by
  have hc (x y : Fin 2) : probe p a b x y DerivativeLiteratureMixed.candidate =
      (2*(if x = y then 4 else 2)*Complex.I)*
        ∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b * p i := by
    rw [WeylHiggsWaveValues.candidate]
    calc
      _ = Complex.I * ((∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b * p i)*
          (2*(if x = y then 4 else 2))) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by ring
  simp only [hc,Fin.sum_univ_two]
  norm_num
  ring

theorem spin_moment (a b : Fin 2) :
    (∑ s : Fin 4, weight a b s *
      ∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b * momentum s i) = 4 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [weight,momentum,Fin.sum_univ_succ,DerivativeLiteratureMixed.sigma,
      LorentzDirections.pauli,Pi.single_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem bySpin_candidate (a b : Fin 2) :
    bySpin a b DerivativeLiteratureMixed.candidate = 96*Complex.I := by
  simp only [bySpin,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,color_sum]
  have hm := spin_moment a b
  calc
    _ = (24*Complex.I)*(∑ s : Fin 4, weight a b s *
        ∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b * momentum s i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [hm]; ring

theorem candidate_value : functional DerivativeLiteratureMixed.candidate = 384*Complex.I := by
  simp only [functional,LinearMap.sum_apply,bySpin_candidate]
  norm_num [Fin.sum_univ_two]
  ring

end
end Physics.WeylHiggsWaveSum

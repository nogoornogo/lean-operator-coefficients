import Math.Algebra.Constructions.ScalarDegreeTwo
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Coeff

/-! Exact four-wave substitution on unbounded ordinary scalar jets.
The square-free coefficient kills every divergence when total momentum is zero.
No group invariance of this coefficient is asserted. -/
namespace Math.FourWaveEvaluation
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
abbrev A := ScalarJetAlgebra.Algebra Unit (Fin 4)
abbrev P := MvPolynomial (Fin 4) ℂ
variable (k : Fin 4 → Fin 4 → ℂ)

def wave (s : Fin 4) (a : Fin 4 →₀ ℕ) : ℂ := ∏ i : Fin 4, k s i ^ a i
def jet (j : Index Unit (Fin 4)) : P := ∑ s : Fin 4, wave k s j.2 • X s
def evaluation : A →ₐ[ℂ] P := aeval (jet k)
def d (i : Fin 4) : Derivation ℂ P P := ∑ s : Fin 4, (k s i • (X s : P)) • pderiv s

@[simp] theorem evaluation_X (j : Index Unit (Fin 4)) : evaluation k (X j) = jet k j := by
  simp [evaluation]

@[simp] theorem d_X (i s : Fin 4) : d k i (X s) = k s i • X s := by
  classical
  simp [d,Derivation.smul_apply,Pi.single_apply]

theorem wave_shift (s i : Fin 4) (a : Fin 4 →₀ ℕ) :
    wave k s (Finsupp.single i 1+a) = k s i * wave k s a := by
  classical
  simp only [wave,Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]
  congr 1
  simp [Finsupp.single_apply]

theorem jet_shift (i : Fin 4) (j : Index Unit (Fin 4)) :
    jet k (shift i j) = d k i (jet k j) := by
  simp only [jet,shift,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [add_comm j.2,wave_shift,Derivation.map_smul,d_X,smul_smul,mul_comm]

theorem derivative (i : Fin 4) (p : A) :
    evaluation k (totalDerivative i p) = d k i (evaluation k p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [totalDerivative_mul,map_add,map_mul,totalDerivative_X,evaluation_X,jet_shift,hp]
    exact (Derivation.leibniz (d k i) (evaluation k p) (jet k j)).symm

def squareFree : Fin 4 →₀ ℕ := ∑ s : Fin 4, Finsupp.single s 1
@[simp] theorem squareFree_apply (s : Fin 4) : squareFree s = 1 := by
  classical
  simp [squareFree,Finsupp.finsetSum_apply,Finsupp.single_apply]
def coefficient : P →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ squareFree

theorem coefficient_fourth (u : Fin 4 → ℂ) :
    coefficient ((∑ i : Fin 4, u i • X i)^4) = 24*∏ i : Fin 4, u i := by
  classical
  change ((∑ i : Fin 4, u i • (X i : P))^4).coeff squareFree = _
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hs : squareFree.support = Finset.univ := by ext i; simp
  norm_num [Finsupp.sum,Finsupp.prod,Finsupp.multinomial_eq,Nat.multinomial,hs,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Nat.factorial]

theorem coefficient_X_pderiv (s : Fin 4) (p : P) : coefficient (X s * pderiv s p) = coefficient p := by
  classical
  change (X s*pderiv s p).coeff squareFree = p.coeff squareFree
  rw [coeff_X_mul']
  simp only [Finsupp.mem_support_iff,squareFree_apply]
  rw [coeff_pderiv,Finsupp.sub_add_single_one_cancel (by simp : squareFree s ≠ 0)]
  have h : ((squareFree-Finsupp.single s 1 : Fin 4 →₀ ℕ)) s = 0 := by simp
  simp [h]

theorem coefficient_derivative (i : Fin 4) (p : P) :
    coefficient (d k i p) = (∑ s : Fin 4, k s i)*coefficient p := by
  have hd : d k i p = ∑ s : Fin 4, (k s i • (X s : P))*pderiv s p := by
    simp [d,Derivation.smul_apply]
  rw [hd]
  rw [map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [smul_mul_assoc,map_smul,coefficient_X_pderiv]
  rfl

def onJets : A →ₗ[ℂ] ℂ := coefficient.comp (evaluation k).toLinearMap

theorem divergence_zero (hk : ∀ i, ∑ s : Fin 4, k s i = 0) (i : Fin 4) (p : A) :
    onJets k (totalDerivative i p) = 0 := by
  change coefficient (evaluation k (totalDerivative i p)) = 0
  rw [derivative,coefficient_derivative,hk,zero_mul]

end
end Math.FourWaveEvaluation

import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInput
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! An ordered raw probe sees the C5 density but also a total derivative.
Its nonzero value is not evidence of an admitted quotient coefficient. -/
namespace Physics.WeylHiggsProbeControl
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic
open scoped TensorProduct
abbrev Odd := MixedJetAlgebra.Odd Label (Fin 4)
abbrev P := MvPolynomial Unit ℂ

def augmentation : Odd →ₐ[ℂ] ℂ := ExteriorAlgebra.lift ℂ
  ⟨(0 : Jet Label (Fin 4) →ₗ[ℂ] ℂ), by intro v; simp⟩
def oddProbe : Odd →ₗ[ℂ] ℂ := augmentation.toLinearMap.comp
  ((CliffordAlgebra.contractLeft (Finsupp.lapply ((true,0),(0 : Fin 4 →₀ ℕ)))).comp
    (CliffordAlgebra.contractLeft (Finsupp.lapply ((false,0),(0 : Fin 4 →₀ ℕ)))))

theorem odd_pair (j k : ScalarJetAlgebra.Index Label (Fin 4)) :
    oddProbe (ExteriorAlgebra.ι ℂ (Finsupp.single j 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single k 1)) =
      (if j = ((false,0),0) then 1 else 0) * (if k = ((true,0),0) then 1 else 0) -
      (if j = ((true,0),0) then 1 else 0) * (if k = ((false,0),0) then 1 else 0) := by
  by_cases hj : j = ((false,0),0) <;> by_cases hk : k = ((false,0),0) <;>
    simp [oddProbe, LinearMap.comp_apply, CliffordAlgebra.contractLeft_ι_mul,
    CliffordAlgebra.contractLeft_ι, augmentation,
    Finsupp.single_apply, eq_comm, hj, hk]

def bosonValue (j : ScalarJetAlgebra.Index Label (Fin 4)) : P :=
  if j = ((false,0),Finsupp.single 0 1) then MvPolynomial.X () else
    if j = ((false,0),0) ∨ j = ((true,0),0) then 1 else 0
def bosonEval : DerivativeLiteratureHiggs.A →ₐ[ℂ] P := MvPolynomial.aeval bosonValue
def bosonProbe : DerivativeLiteratureHiggs.A →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ (Finsupp.single () 1)).comp bosonEval.toLinearMap
def probe : A →ₗ[ℂ] ℂ := (LinearMap.mul' ℂ ℂ).comp (TensorProduct.map oddProbe bosonProbe)

theorem probe_tmul (x : Odd) (p : DerivativeLiteratureHiggs.A) :
    probe (x ⊗ₜ[ℂ] p) = oddProbe x * bosonProbe p := rfl

def primitive : A := psi false 0 * psi true 0 *
  (DerivativeLiteratureMixed.h false 0)^2 * (DerivativeLiteratureMixed.h true 0)^2

theorem candidate_value : probe DerivativeLiteratureMixed.candidate = Complex.I := by
  have hz : (0 : Fin 4 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have he := congrArg (fun v : Fin 4 →₀ ℕ => v 0) h
    simp at he
  simp [DerivativeLiteratureMixed.candidate, DerivativeLiteratureMixed.current,
    DerivativeLiteratureMixed.sigma, LorentzDirections.pauli,
    DerivativeLiteratureMixed.higgsCurrent, DerivativeLiteratureMixed.rho,
    DerivativeLiteratureMixed.psi, DerivativeLiteratureMixed.h, MixedJetAlgebra.odd,
    MixedJetAlgebra.even,
    Algebra.TensorProduct.tmul_mul_tmul, smul_mul_assoc,
    probe_tmul, odd_pair, Fin.sum_univ_succ, bosonProbe, bosonEval, bosonValue,
    ScalarJetAlgebra.shift, LinearMap.comp_apply, MvPolynomial.coeff_X,
    MixedJetAlgebra.oddDerivative, add_mul, mul_add, sub_mul, mul_sub, hz]
  have h30 : Finsupp.single (3 : Fin 4) (1 : ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have he := congrArg (fun v : Fin 4 →₀ ℕ => v 0) h
    norm_num [Finsupp.single_apply] at he
  simp [h30]

theorem divergence_value : probe (D 0 primitive) = 2 := by
  have hz : (0 : Fin 4 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have he := congrArg (fun v : Fin 4 →₀ ℕ => v 0) h
    simp at he
  simp [primitive, psi,
    DerivativeLiteratureMixed.h, MixedJetAlgebra.odd, MixedJetAlgebra.even,
    pow_two, Algebra.TensorProduct.tmul_mul_tmul, probe_tmul, odd_pair,
    bosonProbe, bosonEval, bosonValue, ScalarJetAlgebra.shift, LinearMap.comp_apply,
    MixedJetAlgebra.oddDerivative, JetLinear.shift_single, hz,
    ExteriorAlgebra.derivationOfLinear_mul, ExteriorAlgebra.derivationOfLinear_ι]
  norm_num [MvPolynomial.coeff_one, Finsupp.single_eq_zero]

theorem probe_not_admitted : ¬∀ p ∈ WeylHiggsInput.input.relations, probe p = 0 := by
  intro h
  have hm : D 0 primitive ∈ WeylHiggsInput.input.relations :=
    Submodule.mem_sup_right ⟨Finsupp.single 0 primitive, VariationalIBP.divergence_single D 0 primitive⟩
  have hz := h _ hm
  rw [divergence_value] at hz
  norm_num at hz

theorem raw_candidate_nonzero : DerivativeLiteratureMixed.candidate ≠ 0 := by
  intro hz
  have he := candidate_value
  rw [hz, map_zero] at he
  exact Complex.I_ne_zero he.symm

end
end Physics.WeylHiggsProbeControl

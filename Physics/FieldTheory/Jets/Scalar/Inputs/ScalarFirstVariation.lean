import Math.Algebra.Variational.JetFirstVariation
import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM
import Physics.FieldTheory.Jets.Gauge.FormalYangMills

/-! Normalized polynomial scalar Lagrangian: actual first variation, the
retained EOM seed, explicit boundary current and first-order substitution. -/
namespace Physics.ScalarFirstVariation
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM

def delta (eta : OffShell) := JetFirstVariation.variation (fun _ : Unit => eta)
def lagrangian (lambda : ℂ) : OffShell :=
  (1 / 2 : ℂ) • LorentzJetIBP.kinetic - (lambda / 4) • field ^ 4
def current (eta : OffShell) (i : Fin 4) : OffShell := FormalYangMills.sign i • (eta * D i field)

@[simp] theorem delta_field (eta : OffShell) : delta eta field = eta := by
  exact JetFirstVariation.variation_field _ _

theorem delta_first (eta : OffShell) (i : Fin 4) :
    delta eta (X ((), Finsupp.single i 1)) = D i eta := by
  have h := JetFirstVariation.variation_derivative (fun _ : Unit => eta) i field
  change delta eta (D i field) = D i (delta eta field) at h
  rw [delta_field] at h
  simpa only [field, MasslessScalarEOM.field, ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift, zero_add] using h

theorem first_variation (lambda : ℂ) (eta : OffShell) :
    delta eta (lagrangian lambda) = -eta * seed lambda + ∑ i, D i (current eta i) := by
  let q := -eta * seed lambda + ∑ i, D i (current eta i)
  let raw := LorentzJetIBP.kinetic + LorentzJetIBP.kinetic - C lambda * field ^ 4
  have hnorm : raw = (4 : ℂ) • lagrangian lambda := by
    dsimp [raw, lagrangian]
    rw [C_mul']
    module
  have h0 : delta eta (X ((), 0)) = eta := delta_field eta
  have hr : delta eta raw = (4 : ℂ) • q := by
    dsimp [raw, q]
    rw [LorentzJetIBP.kinetic_formula]
    simp [current, FormalYangMills.sign, Fin.sum_univ_succ,
      ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift, ← Finsupp.single_add,
      seed, MasslessScalarEOM.waveField_formula, field, MasslessScalarEOM.field,
      pow_succ, Derivation.leibniz, delta_first, h0, smul_eq_mul, Algebra.smul_def,
      MvPolynomial.algebraMap_eq]
    norm_num only [map_ofNat]
    ring
  have hs : delta eta ((4 : ℂ) • lagrangian lambda) = (4 : ℂ) • delta eta (lagrangian lambda) :=
    (delta eta).toLinearMap.map_smul _ _
  rw [hnorm, hs] at hr
  have h := congrArg (fun p : OffShell => (1 / 4 : ℂ) • p) hr
  simpa only [smul_smul, show (1 / 4 : ℂ) * 4 = 1 by norm_num, one_smul] using h

theorem first_variation_mod_ibp (lambda : ℂ) (eta : OffShell) :
    (DifferentialEquation.ibp D).mkQ (delta eta (lagrangian lambda)) =
      (DifferentialEquation.ibp D).mkQ (-eta * seed lambda) := by
  rw [first_variation, map_add]
  have h : (DifferentialEquation.ibp D).mkQ (∑ i, D i (current eta i)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.sum_mem _ (fun i _ => DifferentialEquation.derivative_mem_ibp D i _)
  rw [h, add_zero]

theorem first_variation_onShell (lambda : ℂ) (eta : OffShell) :
    integrated lambda (delta eta (lagrangian lambda)) = 0 := by
  rw [first_variation, map_add, map_sum]
  have he : integrated lambda (-eta * seed lambda) = 0 :=
    DifferentialEquation.integrated_equation _ _ ((ideal lambda).mul_mem_left _
      (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _)))
  simp only [he, DifferentialEquation.integrated_derivative, Finset.sum_const_zero, add_zero]

theorem substitution_first (lambda : ℂ) (eta : OffShell) :
    (JetFirstVariation.substitution (fun _ : Unit => eta) (lagrangian lambda)).coeff 1 =
      -eta * seed lambda + ∑ i, D i (current eta i) := by
  rw [JetFirstVariation.substitution_first]
  exact first_variation lambda eta

def eulerEquation (lambda : ℂ) : OffShell := -seed lambda

theorem euler_ideal_eq (lambda : ℂ) : DifferentialEquation.ideal D {eulerEquation lambda} = ideal lambda := by
  apply le_antisymm
  · apply DifferentialEquation.minimal
    · intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      exact (ideal lambda).neg_mem (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _))
    · intro i p hp
      exact DifferentialEquation.stable _ _ i hp
  · apply DifferentialEquation.minimal
    · intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      have he : eulerEquation lambda ∈ DifferentialEquation.ideal D {eulerEquation lambda} :=
        DifferentialEquation.seed_mem _ _ (Set.mem_singleton _)
      change seed lambda ∈ DifferentialEquation.ideal D {eulerEquation lambda}
      have hn := (DifferentialEquation.ideal D {eulerEquation lambda}).neg_mem he
      change -(-seed lambda) ∈ DifferentialEquation.ideal D {eulerEquation lambda} at hn
      rw [neg_neg] at hn
      exact hn
    · intro i p hp
      exact DifferentialEquation.stable _ _ i hp

end
end Physics.ScalarFirstVariation

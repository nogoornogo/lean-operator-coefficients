import Physics.FieldTheory.Jets.Gauge.MaxwellLinearEquation

/-! Coordinate equations and the wave consequence of Maxwell plus Bianchi. -/
namespace Physics.AbelianFieldStrength
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections LorentzDirections
open scoped TensorProduct BigOperators

def component (a b : Fin 4) : Jets := zeroPair (basis a) (basis b)

theorem component_symbol (a b : Fin 4) : component a b = ofSymbols (a, b) 1 := by
  rw [component, zeroPair, pair_basis, atOrder_single]
  exact (ofSymbols_monomial (a, b) 0 1).symm

theorem antisymmetry_basis (a b : Fin 4) : antisymmetry (basis a ⊗ₜ[ℂ] basis b) = component a b + component b a :=
  antisymmetry_tmul _ _

theorem maxwell_basis (b : Fin 4) : maxwell (basis b) = ∑ a : Fin 4, JetLinear.shift a (component a b) :=
  maxwell_apply _

theorem bianchi_basis (a b c : Fin 4) : bianchi (basis a ⊗ₜ[ℂ] (basis b ⊗ₜ[ℂ] basis c)) =
    sign a • JetLinear.shift a (component b c) + sign c • JetLinear.shift c (component a b) +
      sign b • JetLinear.shift b (component c a) := by
  simp [bianchi_tmul, metric_basis, directional_apply, Finsupp.single_apply, component]

def fieldClass (a b : Fin 4) : Generator := relations.mkQ (component a b)
abbrev D := LinearJetEquation.shift seed

theorem antisymmetry_zero (a b : Fin 4) : fieldClass a b + fieldClass b a = 0 := by
  have h : relations.mkQ (antisymmetry (basis a ⊗ₜ[ℂ] basis b)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (antisymmetry_mem (basis a) (basis b))
  rw [antisymmetry_basis, map_add] at h
  exact h

theorem antisymmetry_descendants (a b : Fin 4) (p : Symbols (Fin 4)) :
    ofSymbols (a, b) p + ofSymbols (b, a) p ∈ relations := by
  have h := LinearJetEquation.multiple_stable seed p (antisymmetry_mem (basis a) (basis b))
  change LinearJetEquation.multiple p (antisymmetry (basis a ⊗ₜ[ℂ] basis b)) ∈ relations at h
  rw [antisymmetry_basis, map_add, component_symbol, component_symbol,
    LinearJetEquation.multiple_ofSymbols, LinearJetEquation.multiple_ofSymbols, mul_one] at h
  exact h

theorem diagonal_descendants (a : Fin 4) (p : Symbols (Fin 4)) : ofSymbols (a, a) p ∈ relations := by
  have h := relations.smul_mem (1/2 : ℂ) (antisymmetry_descendants a a p)
  have he : (1/2 : ℂ) • (ofSymbols (a, a) p + ofSymbols (a, a) p) = ofSymbols (a, a) p := by
    rw [smul_add, ← add_smul]
    norm_num
  rwa [he] at h

theorem maxwell_zero (b : Fin 4) : ∑ a : Fin 4, D a (fieldClass a b) = 0 := by
  have h : relations.mkQ (maxwell (basis b)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (maxwell_mem (basis b))
  rw [maxwell_basis, map_sum] at h
  exact h

theorem bianchi_zero (a b c : Fin 4) : sign a • D a (fieldClass b c) +
    sign c • D c (fieldClass a b) + sign b • D b (fieldClass c a) = 0 := by
  have h : relations.mkQ (bianchi (basis a ⊗ₜ[ℂ] (basis b ⊗ₜ[ℂ] basis c))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (bianchi_mem (basis a) (basis b) (basis c))
  rw [bianchi_basis, map_add, map_smul] at h
  exact h

private theorem D_commute (a b : Fin 4) (v : Generator) : D a (D b v) = D b (D a v) :=
  LinearMap.congr_fun (LinearJetEquation.shift_commute seed a b) v

private theorem swapped_maxwell_zero (b : Fin 4) : ∑ a : Fin 4, D a (fieldClass b a) = 0 := by
  have he : ∀ a, fieldClass b a = -fieldClass a b := by
    intro a
    exact eq_neg_of_add_eq_zero_left (antisymmetry_zero b a)
  simp only [he, map_neg, Finset.sum_neg_distrib, maxwell_zero, neg_zero]

theorem wave_zero (a b : Fin 4) : ∑ i : Fin 4, sign i • D i (D i (fieldClass a b)) = 0 := by
  have h := Finset.sum_eq_zero (s := Finset.univ) (fun i _ => by simpa only [map_zero] using congrArg (D i) (bianchi_zero i a b))
  simp only [map_add, map_smul] at h
  simp only [Finset.sum_add_distrib] at h
  have hm1 : (∑ i : Fin 4, sign b • D i (D b (fieldClass i a))) = 0 := by
    simp_rw [D_commute _ b]
    rw [← Finset.smul_sum, ← map_sum, maxwell_zero, map_zero, smul_zero]
  have hm2 : (∑ i : Fin 4, sign a • D i (D a (fieldClass b i))) = 0 := by
    simp_rw [D_commute _ a]
    rw [← Finset.smul_sum, ← map_sum, swapped_maxwell_zero, map_zero, smul_zero]
  rw [hm1, hm2, add_zero, add_zero] at h
  exact h

theorem wave_relation (a b : Fin 4) : ofSymbols (a, b) wave ∈ relations := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have h := wave_zero a b
  norm_num [Fin.sum_univ_succ, sign] at h
  change relations.mkQ (ofSymbols (a, b) wave) = 0
  have he : relations.mkQ (ofSymbols (a, b) wave) =
      D 0 (D 0 (fieldClass a b)) - D 1 (D 1 (fieldClass a b)) -
        D 2 (D 2 (fieldClass a b)) - D 3 (D 3 (fieldClass a b)) := by
    simp only [fieldClass, component_symbol, D, LinearJetEquation.shift_mk, shift_ofSymbols,
      one_mul, ← map_sub, wave, pow_two]
  rw [he]
  convert h using 1
  abel

theorem wave_descendants (a b : Fin 4) (p : Symbols (Fin 4)) : ofSymbols (a, b) (p * wave) ∈ relations := by
  have h := LinearJetEquation.multiple_stable seed p (wave_relation a b)
  change LinearJetEquation.multiple p (ofSymbols (a, b) wave) ∈ relations at h
  rwa [LinearJetEquation.multiple_ofSymbols] at h

end
end Physics.AbelianFieldStrength

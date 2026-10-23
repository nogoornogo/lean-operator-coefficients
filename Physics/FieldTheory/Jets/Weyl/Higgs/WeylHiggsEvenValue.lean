import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalIBP

/-! Exact separation of the Lorentz trace and the two internal Higgs
coordinates in the candidate evaluation. -/
namespace Physics.WeylHiggsEvenValue
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsLorentzUpper WeylHiggsInternalLift
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def scalarMono (b : Fin 4 → Label) (i : Fin 4) : DerivativeLiteratureHiggs.A :=
  DerivativeLiteratureHiggs.D i (DerivativeLiteratureHiggs.h (b 0).1 (b 0).2)*
    DerivativeLiteratureHiggs.h (b 1).1 (b 1).2*DerivativeLiteratureHiggs.h (b 2).1 (b 2).2*
      DerivativeLiteratureHiggs.h (b 3).1 (b 3).2

theorem even_value (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    f (psi false a*psi true e*scalarEmbed (scalarMono b i)) =
      WeylDirectionInvariant.kernel a e i * scalarFunctional f (scalarMono b 0) := by
  calc
    _ = C f false true b 2 a e i := by rw [component_word,even_word_scalar]; rfl
    _ = C f false true b 2 0 0 0 * WeylDirectionInvariant.kernel a e i := by
      simpa only [Bool.false_eq_true,ite_false,ite_true] using component_formula f h false true b 2 a e i
    _ = _ := by rw [component_word,even_word_scalar,scalarFunctional_apply,mul_comm]; rfl

def plus (c e : Fin 2) : Fin 4 → Label := ![(false,c),(true,c),(true,e),(false,e)]
def minus (c e : Fin 2) : Fin 4 → Label := ![(true,c),(false,c),(true,e),(false,e)]

theorem current_radius (i : Fin 4) :
    WeylHiggsCurrent.scalarCurrent i*DerivativeLiteratureHiggs.rho =
      ∑ c : Fin 2, ∑ e : Fin 2, (scalarMono (plus c e) i-scalarMono (minus c e) i) := by
  simp [WeylHiggsCurrent.scalarCurrent,DerivativeLiteratureHiggs.rho,scalarMono,plus,minus,Fin.sum_univ_two]
  ring

def S (f : A →ₗ[ℂ] ℂ) : ℂ := ∑ c : Fin 2, ∑ e : Fin 2,
  (scalarFunctional f (scalarMono (plus c e) 0)-scalarFunctional f (scalarMono (minus c e) 0))

theorem current_value (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (a e : Fin 2) (i : Fin 4) :
    f (psi false a*psi true e*scalarEmbed
      (WeylHiggsCurrent.scalarCurrent i*DerivativeLiteratureHiggs.rho)) =
        WeylDirectionInvariant.kernel a e i*S f := by
  rw [current_radius]
  simp only [map_sum,map_sub,Finset.mul_sum,mul_sub,even_value f h]
  simp only [S,Finset.mul_sum,mul_sub]

theorem candidate_sum : DerivativeLiteratureMixed.candidate = Complex.I •
    ∑ i : Fin 4, ∑ a : Fin 2, ∑ e : Fin 2, DerivativeLiteratureMixed.sigma i a e •
      (psi false a*psi true e*scalarEmbed
        (WeylHiggsCurrent.scalarCurrent i*DerivativeLiteratureHiggs.rho)) := by
  unfold DerivativeLiteratureMixed.candidate
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← WeylHiggsCurrent.higgs_current_dictionary,← WeylHiggsCurrent.rho_dictionary,
    mul_assoc,← map_mul]
  simp only [DerivativeLiteratureMixed.current,Finset.sum_mul,smul_mul_assoc]
  rfl

theorem spin_trace (a e : Fin 2) :
    (∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a e * WeylDirectionInvariant.kernel a e i) = 2 := by
  fin_cases a <;> fin_cases e <;>
    norm_num [Fin.sum_univ_four,DerivativeLiteratureMixed.sigma,LorentzDirections.pauli,
      WeylDirectionInvariant.kernel,LorentzDirections.fromPauli,Pi.single_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem kernel_trace :
    (∑ i : Fin 4, ∑ a : Fin 2, ∑ e : Fin 2,
      DerivativeLiteratureMixed.sigma i a e * WeylDirectionInvariant.kernel a e i) = 8 := by
  calc
    _ = ∑ a : Fin 2, ∑ e : Fin 2, ∑ i : Fin 4,
        DerivativeLiteratureMixed.sigma i a e * WeylDirectionInvariant.kernel a e i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by simp only [spin_trace]; norm_num [Fin.sum_univ_two]

theorem candidate_value_raw (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p) :
    f DerivativeLiteratureMixed.candidate = (8*Complex.I)*S f := by
  rw [candidate_sum,map_smul]
  simp only [map_sum,map_smul,smul_eq_mul,current_value f h,← mul_assoc,← Finset.sum_mul]
  rw [kernel_trace]
  ring

end
end Physics.WeylHiggsEvenValue

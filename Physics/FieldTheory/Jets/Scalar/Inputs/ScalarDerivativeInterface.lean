import Math.RepresentationTheory.Jets.DerivativeInterface
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter

/-! Purpose-specific model factory and full-quotient selection through common operations. -/
namespace Physics.ScalarDerivativeInterface
set_option autoImplicit false
noncomputable section
open Math Representation PolynomialScalarEOM

/-- Coupling is the only model input; actual Lorentz covariance is already proved. -/
def scalar (lambda : ℂ) : DerivativeInterface.Input LorentzDirections.Group OffShell :=
  DerivativeInterface.equations D (equations lambda) ScalarInputAdapter.lorentzAction
    (ScalarInputAdapter.lorentz_stable lambda)

def compatibleInput (lambda : ℂ) : (scalar lambda).Coefficient ≃ₗ[ℂ]
    ScalarInputAdapter.LorentzInput lambda := LinearEquiv.refl ℂ _

@[simp] theorem compatible_map (lambda : ℂ) (f : (scalar lambda).Coefficient) :
    (scalar lambda).coefficientEquiv f = ScalarInputAdapter.lorentzEquiv lambda f := rfl

/-- Same dot-operations as the mixed graded factory. -/
theorem scalar_extraction (lambda : ℂ) (f : (scalar lambda).Coefficient) (p : OffShell) :
    (scalar lambda).coefficientEquiv f ((scalar lambda).projection p) = f.val p :=
  (scalar lambda).extraction f p

def interactionSource : Submodule ℂ OffShell :=
  Submodule.span ℂ ({LorentzJetIBP.waveField, field ^ 3} : Set OffShell)

theorem wave_mem : LorentzJetIBP.waveField ∈ interactionSource :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem cubic_mem : field ^ 3 ∈ interactionSource :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem interaction_stable (lambda : ℂ) : ∀ g, interactionSource ≤
    interactionSource.comap ((scalar lambda).action g) := by
  intro g
  apply Submodule.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with hp | hp
  · subst p
    change offAction g LorentzJetIBP.waveField ∈ interactionSource
    rw [show offAction g LorentzJetIBP.waveField = LorentzJetIBP.waveField from
      LorentzJetIBP.waveField_invariant g]
    exact wave_mem
  · rw [Set.mem_singleton_iff] at hp
    subst p
    change offAction g (field ^ 3) ∈ interactionSource
    rw [map_pow, field_invariant]
    exact cubic_mem

def selected (lambda : ℂ) := (scalar lambda).select interactionSource (interaction_stable lambda)

def wave : interactionSource := ⟨LorentzJetIBP.waveField, wave_mem⟩
def cubic : interactionSource := ⟨field ^ 3, cubic_mem⟩

theorem seed_mem_source (lambda : ℂ) : seed lambda ∈ interactionSource := by
  change LorentzJetIBP.waveField + MvPolynomial.C lambda * field ^ 3 ∈ interactionSource
  rw [← MvPolynomial.smul_eq_C_mul]
  exact interactionSource.add_mem wave_mem (interactionSource.smul_mem lambda cubic_mem)

def selectedSeed (lambda : ℂ) : interactionSource := ⟨seed lambda, seed_mem_source lambda⟩

theorem selected_seed_relation (lambda : ℂ) : selectedSeed lambda ∈ (selected lambda).relations :=
  Submodule.mem_sup_left (DifferentialEquation.seed_mem D (equations lambda) (Set.mem_singleton _))

/-- The selected source contains both derivative and nonderivative terms of the actual EOM. -/
theorem selected_interaction (lambda : ℂ) (f : (selected lambda).Coefficient) :
    f.val wave + lambda * f.val cubic = 0 := by
  have hs := f.property (selected_seed_relation lambda)
  have hv : selectedSeed lambda = wave + lambda • cubic := by
    apply Subtype.ext
    change seed lambda = LorentzJetIBP.waveField + lambda • field ^ 3
    rw [seed, MvPolynomial.smul_eq_C_mul]
  change f.val (selectedSeed lambda) = 0 at hs
  rw [hv, map_add, map_smul] at hs
  exact hs

/-- Selection is the actual full-quotient image, without an independent-grade assumption. -/
def selectedImageEquiv (lambda : ℂ) : (selected lambda).Source ≃ₗ[ℂ]
    (scalar lambda).selectedImage interactionSource :=
  (scalar lambda).selectionEquiv interactionSource (interaction_stable lambda)

theorem restriction_agrees (lambda : ℂ) (f : (scalar lambda).Coefficient) :
    ((scalar lambda).restrict interactionSource (interaction_stable lambda) f).val wave =
      f.val LorentzJetIBP.waveField := rfl

end
end Physics.ScalarDerivativeInterface

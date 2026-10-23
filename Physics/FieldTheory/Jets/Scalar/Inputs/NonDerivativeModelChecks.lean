import Math.RepresentationTheory.Jets.NonDerivativeInputChecks
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput

/-! Nonderivative targets through actual represented EOM inputs.
Restriction retains all full-source relations, including cross-degree EOM. -/
namespace Physics.NonDerivativeModelChecks
set_option autoImplicit false
noncomputable section
open Math

namespace Scalar
open PolynomialScalarEOM

def freeCoefficient (n : ℕ) (c : ℂ) : (ScalarDerivativeInterface.scalar 0).Coefficient :=
  c • ScalarConstantCoefficients.functional n

theorem free_value (n : ℕ) (c : ℂ) : (freeCoefficient n c).val (field^n) = c := by
  change c * (ScalarConstantCoefficients.functional n).val (field^n) = c
  rw [ScalarConstantCoefficients.detects,mul_one]

theorem free_extraction (n : ℕ) (c : ℂ) :
    (ScalarDerivativeInterface.scalar 0).coefficientEquiv (freeCoefficient n c)
      ((ScalarDerivativeInterface.scalar 0).projection (field^n)) = c := free_value n c

theorem free_image_dimension (n : ℕ) :
    Module.finrank ℂ (ScalarZeroDerivativeCertificate.Image n) = 1 :=
  ScalarZeroDerivativeCertificate.dimension n

theorem interacting_values (lambda c : ℂ) :
    (∃ f : (ScalarDerivativeInterface.scalar lambda).Coefficient, f.val (field^3) = c) ↔
      lambda*c = 0 := ScalarConstantCoefficients.cubic_value_iff lambda c

/-- A legitimate old cubic value need not extend after a nonzero interaction EOM. -/
theorem interacting_one_rejected :
    ¬∃ f : (ScalarDerivativeInterface.scalar 1).Coefficient, f.val (field^3) = 1 := by
  rw [interacting_values]
  norm_num
end Scalar

namespace Higgs
open Math.DerivativeLiteratureHiggs

theorem rho_invariant (g : HiggsStandardInput.Group) :
    HiggsStandardInput.transport g rho = rho := by
  rw [HiggsStandardInput.factorize,HiggsLagrangianInput.rho_invariant,
    HiggsInternalSymmetry.radius_invariant]

theorem power_invariant (g : HiggsStandardInput.Group) (n : ℕ) :
    HiggsStandardInput.action g (rho^n) = rho^n := by
  change HiggsStandardInput.transport g (rho^n) = rho^n
  rw [map_pow,rho_invariant]

def potentialSource : Submodule ℂ A := Submodule.span ℂ ({rho^2,rho^3} : Set A)
theorem square_mem : rho^2 ∈ potentialSource := Submodule.subset_span (Set.mem_insert _ _)
theorem cube_mem : rho^3 ∈ potentialSource :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem potential_stable (a b : ℂ) : ∀ g, potentialSource ≤
    potentialSource.comap ((HiggsStandardInput.input a b).action g) := by
  intro g
  apply Submodule.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with hp | hp
  · subst p
    change HiggsStandardInput.action g (rho^2) ∈ potentialSource
    rw [power_invariant]
    exact square_mem
  · rw [Set.mem_singleton_iff] at hp
    subst p
    change HiggsStandardInput.action g (rho^3) ∈ potentialSource
    rw [power_invariant]
    exact cube_mem

def input (a b : ℂ) := (HiggsStandardInput.input a b).select potentialSource (potential_stable a b)
def square : potentialSource := ⟨rho^2,square_mem⟩
def cube : potentialSource := ⟨rho^3,cube_mem⟩
def restrict (a b : ℂ) := (HiggsStandardInput.input a b).restrict potentialSource (potential_stable a b)

theorem extraction (a b : ℂ) (f : (HiggsStandardInput.input a b).Coefficient) :
    (input a b).coefficientEquiv (restrict a b f) ((input a b).projection square) =
      f.val (rho^2) ∧
    (input a b).coefficientEquiv (restrict a b f) ((input a b).projection cube) =
      f.val (rho^3) := ⟨rfl,rfl⟩

def imageEquiv (a b : ℂ) : (input a b).Source ≃ₗ[ℂ]
    (HiggsStandardInput.input a b).selectedImage potentialSource :=
  (HiggsStandardInput.input a b).selectionEquiv potentialSource (potential_stable a b)

theorem image_agreement (a b : ℂ) (p : potentialSource) :
    (imageEquiv a b ((input a b).projection p)).val =
      (HiggsStandardInput.input a b).projection p.val := rfl

theorem reconstruction (a b : ℂ) (f : (input a b).Coefficient) :
    (input a b).coefficientEquiv.symm ((input a b).coefficientEquiv f) = f :=
  (input a b).coefficientEquiv.symm_apply_apply f

theorem generated_direct_values (a b : ℂ) (f : (HiggsStandardInput.input a b).Coefficient) :
    (HiggsStandardInput.coefficientEquiv a b f).val (rho^2) = f.val (rho^2) ∧
    (HiggsStandardInput.coefficientEquiv a b f).val (rho^3) = f.val (rho^3) := ⟨rfl,rfl⟩
end Higgs

end
end Physics.NonDerivativeModelChecks

import Math.RepresentationTheory.Coefficients.MixedOperatorInput

/-! Purpose-specific derivative inputs with shared quotient/coefficient operations.
Selection retains all full-source relations; no global graded decomposition is assumed. -/
namespace Math.DerivativeInterface
set_option autoImplicit false
noncomputable section
open Representation

/-- Optional common operation surface. Existing public coefficient inputs stay unchanged. -/
structure Input (H U : Type*) [Group H] [AddCommGroup U] [Module ℂ U] where
  action : Representation ℂ H U
  relations : Submodule ℂ U
  stable : ∀ h, relations ≤ relations.comap (action h)

namespace Input
variable {H U : Type*} [Group H] [AddCommGroup U] [Module ℂ U] (P : Input H U)

abbrev Source := U ⧸ P.relations
abbrev residual : Representation ℂ H P.Source := P.action.quotient P.relations P.stable
abbrev Coefficient := JetInputAdapter.Input P.action (trivial ℂ H ℂ) P.relations

def projection : U →ₗ[ℂ] P.Source := P.relations.mkQ

def coefficientEquiv : P.Coefficient ≃ₗ[ℂ] IntertwiningMap P.residual (trivial ℂ H ℂ) :=
  JetInputAdapter.equiv _ _ _ P.stable

@[simp] theorem extraction (f : P.Coefficient) (u : U) :
    P.coefficientEquiv f (P.projection u) = f.val u := rfl

@[simp] theorem reconstruction (f : IntertwiningMap P.residual (trivial ℂ H ℂ)) (u : U) :
    (P.coefficientEquiv.symm f).val u = f (P.projection u) := rfl

theorem nonzero_iff : (∃ f : P.Coefficient, f ≠ 0) ↔
    ∃ f : IntertwiningMap P.residual (trivial ℂ H ℂ), f ≠ 0 :=
  JetInputAdapter.nonzero_iff _ _ _ _

theorem forbidden_iff : (∀ f : P.Coefficient, f = 0) ↔
    ∀ f : IntertwiningMap P.residual (trivial ℂ H ℂ), f = 0 := by
  constructor
  · intro h f
    rw [← P.coefficientEquiv.apply_symm_apply f, h (P.coefficientEquiv.symm f), map_zero]
  · intro h f
    apply P.coefficientEquiv.injective
    rw [h (P.coefficientEquiv f), map_zero]

variable (V : Submodule ℂ U) (hV : ∀ h, V ≤ V.comap (P.action h))

def select : Input H V where
  action := P.action.subrepresentation V hV
  relations := P.relations.comap V.subtype
  stable h _ hp := P.stable h hp

/-- Selected inputs keep their actual image in the full quotient. -/
def selectedProjection : V →ₗ[ℂ] P.Source := P.projection.comp V.subtype

abbrev selectedImage : Submodule ℂ P.Source := (P.selectedProjection V).range

theorem selected_kernel : (P.selectedProjection V).ker = (P.select V hV).relations := by
  rw [selectedProjection, LinearMap.ker_comp, projection, Submodule.ker_mkQ]
  rfl

def selectionEquiv : (P.select V hV).Source ≃ₗ[ℂ] P.selectedImage V :=
  (Submodule.quotEquivOfEq _ _ (P.selected_kernel V hV).symm).trans
    (P.selectedProjection V).quotKerEquivRange

@[simp] theorem selectionEquiv_mk (p : V) :
    (P.selectionEquiv V hV ((P.select V hV).projection p)).val = P.projection p.val := rfl

/-- Restrict global coefficients. Extension of arbitrary selected coefficients is not assumed. -/
def restrict : P.Coefficient →ₗ[ℂ] (P.select V hV).Coefficient where
  toFun f := ⟨{
    toLinearMap := f.val.toLinearMap.comp V.subtype
    isIntertwining' h := by
      apply LinearMap.ext
      intro p
      exact IntertwiningMap.isIntertwining _ _ f.val h p.val }, fun _ hp => f.property hp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_evaluation (f : P.Coefficient) (p : V) :
    (P.restrict V hV f).val p = f.val p.val := rfl

@[simp] theorem selected_extraction (f : P.Coefficient) (p : V) :
    (P.select V hV).coefficientEquiv (P.restrict V hV f)
      ((P.select V hV).projection p) = P.coefficientEquiv f (P.projection p.val) := rfl
end Input

section Graded
variable {F B I H : Type*} [Group H] [Fintype I]
  (rhoF : Representation ℂ H (JetLinear.Field F))
  (rhoB : Representation ℂ H (JetLinear.Field B))
  (sigma : Representation ℂ H (JetDirections.Direction I))

@[reducible] local instance (n m d : ℕ) : AddCommGroup (MixedOperatorInput.Source F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (MixedOperatorInput.Source F B I n m d) := inferInstance

def graded (n m d : ℕ) : Input H (MixedOperatorInput.Source F B I n m d) where
  action := MixedOperatorInput.action rhoF rhoB sigma n m d
  relations := MixedOperatorInput.relations n m d
  stable := MixedOperatorInput.stable rhoF rhoB sigma n m d

/-- Same coefficient type; packaging creates no new caller proof obligation. -/
def gradedInputEquiv (n m d : ℕ) : (graded rhoF rhoB sigma n m d).Coefficient ≃ₗ[ℂ]
    MixedOperatorInput.Coefficient rhoF rhoB sigma n m d := LinearEquiv.refl ℂ _

@[simp] theorem graded_map (n m d : ℕ) (f : (graded rhoF rhoB sigma n m d).Coefficient) :
    (graded rhoF rhoB sigma n m d).coefficientEquiv f =
      MixedOperatorInput.coefficientEquiv rhoF rhoB sigma n m d f := rfl
/-- Existing nonderivative coefficients enter the graded factory without new proofs. -/
def fromNonDerivative (n m : ℕ) := MixedOperatorInput.nonDerivativeEquiv rhoF rhoB sigma n m

@[simp] theorem fromNonDerivative_evaluation (n m : ℕ)
    (f : InvariantCoefficientTransport.Invariants (MixedJetSource.originalAction rhoF rhoB n m))
    (p : MixedJetSource.Original F B n m) :
    (graded rhoF rhoB sigma n m 0).coefficientEquiv (fromNonDerivative rhoF rhoB sigma n m f)
      ((graded rhoF rhoB sigma n m 0).projection (MixedJetSource.zeroEquiv n m p)) = f p :=
  MixedOperatorInput.nonDerivative_extraction rhoF rhoB sigma n m f p

end Graded

section Equations
variable {A I H : Type*} [CommRing A] [Algebra ℂ A] [Group H]
  (D : I → Derivation ℂ A A) (R : Set A) (rho : Representation ℂ H A)
  (stable : ∀ h, DifferentialEquation.combined D R ≤
    (DifferentialEquation.combined D R).comap (rho h))

def equations : Input H A where
  action := rho
  relations := DifferentialEquation.combined D R
  stable := stable

def equationInputEquiv : (equations D R rho stable).Coefficient ≃ₗ[ℂ]
    JetInputAdapter.EquationInput D R rho := LinearEquiv.refl ℂ _

@[simp] theorem equations_map (f : (equations D R rho stable).Coefficient) :
    (equations D R rho stable).coefficientEquiv f = JetInputAdapter.equationEquiv D R rho stable f := rfl
end Equations

end
end Math.DerivativeInterface

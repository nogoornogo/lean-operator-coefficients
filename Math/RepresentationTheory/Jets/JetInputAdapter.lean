import Math.RepresentationTheory.Coefficients.RelationInputExtension
import Math.RepresentationTheory.Jets.DirectionalJetIBP
import Math.RepresentationTheory.Jets.MixedJetZero
import Math.RepresentationTheory.Jets.NonlinearJetIBP

/-! Derivative inputs in the published relation/Hom vocabulary. No old API changes. -/
namespace Math.JetInputAdapter
set_option autoImplicit false
noncomputable section
open Representation

section Common
variable {H U W : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (rho : Representation ℂ H U) (tau : Representation ℂ H W)

def values : IntertwiningMap rho tau →ₗ[ℂ] (U →ₗ[ℂ] W) where
  toFun f := f.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev Input (T : Submodule ℂ U) := RelationInputExtension.Input (values rho tau) T

/-- The new adapter's input is definitionally the existing published input. -/
def legacyInputEquiv (T : Submodule ℂ U) : Input rho tau T ≃ₗ[ℂ]
    RelationQuotient.vanishing rho tau T := LinearEquiv.refl ℂ _

def equiv (T : Submodule ℂ U) (stable : ∀ h, T ≤ T.comap (rho h)) :
    Input rho tau T ≃ₗ[ℂ] IntertwiningMap (rho.quotient T stable) tau :=
  (legacyInputEquiv rho tau T).trans (RelationQuotient.equiv rho tau T stable)

@[simp] theorem extraction (T : Submodule ℂ U) (stable : ∀ h, T ≤ T.comap (rho h))
    (f : Input rho tau T) (u : U) : equiv rho tau T stable f (T.mkQ u) = f.val u := rfl

@[simp] theorem reconstruction (T : Submodule ℂ U) (stable : ∀ h, T ≤ T.comap (rho h))
    (f : IntertwiningMap (rho.quotient T stable) tau) (u : U) :
    ((equiv rho tau T stable).symm f).val u = f (T.mkQ u) := rfl

theorem nonzero_iff (T : Submodule ℂ U) (stable : ∀ h, T ≤ T.comap (rho h)) :
    (∃ f : Input rho tau T, f ≠ 0) ↔
      ∃ f : IntertwiningMap (rho.quotient T stable) tau, f ≠ 0 :=
  ConstrainedCompleteness.exists_nonzero_iff (equiv rho tau T stable)
end Common

section Mixed
variable {F B I H : Type*} [Group H]
  (rhoF : Representation ℂ H (JetLinear.Field F))
  (rhoB : Representation ℂ H (JetLinear.Field B))

@[reducible] local instance (n m d : ℕ) : AddCommGroup (MixedJetAlgebra.grade F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (MixedJetAlgebra.grade F B I n m d) := inferInstance

/-- No EOM and no derivatives: inverse compatibility with the existing mixed source. -/
def zeroEquiv (n m : ℕ) :
    InvariantCoefficientTransport.Invariants (MixedJetSource.originalAction rhoF rhoB n m) ≃ₗ[ℂ]
    Input (MixedJetAlgebra.gradeAction (I := I) rhoF rhoB n m 0) (trivial ℂ H ℂ) ⊥ :=
  (InvariantCoefficientTransport.alongEquiv (MixedJetSource.zeroRepresentationEquiv rhoF rhoB n m)).trans
    (RelationInputExtension.emptyEquiv (values _ _)).symm

@[simp] theorem zero_evaluation (n m : ℕ)
    (f : InvariantCoefficientTransport.Invariants (MixedJetSource.originalAction rhoF rhoB n m))
    (u : MixedJetSource.Original F B n m) :
    (zeroEquiv (I := I) rhoF rhoB n m f).val (MixedJetSource.zeroEquiv n m u) = f u := by
  change f ((MixedJetSource.zeroRepresentationEquiv rhoF rhoB n m).toLinearEquiv.symm
    ((MixedJetSource.zeroRepresentationEquiv rhoF rhoB n m).toLinearEquiv u)) = f u
  rw [LinearEquiv.symm_apply_apply]

variable [Fintype I] (sigma : Representation ℂ H (JetDirections.Direction I))

abbrev mixedRelations (n m d : ℕ) := CovariantJetIBP.relations (V := fun d => MixedJetAlgebra.grade F B I n m d)
  (DirectionalJetIBP.mixedDerivatives (F := F) (B := B) (I := I) n m) d

def mixedEquiv (n m d : ℕ) := equiv
  (DirectionalJetIBP.mixedAction sigma rhoF rhoB n m (d + 1)) (trivial ℂ H ℂ)
  (mixedRelations (F := F) (B := B) (I := I) n m d)
  (CovariantJetIBP.stable _ sigma (DirectionalJetIBP.mixedAction sigma rhoF rhoB n m)
    (fun h i d => DirectionalJetIBP.mixed_covariance sigma rhoF rhoB n m h i d) d)

/-- The old positive-grade coefficient input is accepted without conversion. -/
def mixedLegacyInput (n m d : ℕ) :
    CovariantJetIBP.Coefficient (DirectionalJetIBP.mixedDerivatives (I := I) n m)
      (DirectionalJetIBP.mixedAction sigma rhoF rhoB n m) d ≃ₗ[ℂ]
    Input (DirectionalJetIBP.mixedAction sigma rhoF rhoB n m (d + 1)) (trivial ℂ H ℂ)
      (mixedRelations (F := F) (B := B) (I := I) n m d) := LinearEquiv.refl ℂ _

@[simp] theorem mixed_legacy_map (n m d : ℕ) (f : _) :
    mixedEquiv rhoF rhoB sigma n m d f =
      DirectionalJetIBP.mixedCoefficientEquiv sigma rhoF rhoB n m d f := rfl
end Mixed

section Equations
variable {A I H : Type*} [CommRing A] [Algebra ℂ A] [Group H]
  (D : I → Derivation ℂ A A) (R : Set A)
  (rho : Representation ℂ H A)
  (stable : ∀ h, DifferentialEquation.combined D R ≤
    (DifferentialEquation.combined D R).comap (rho h))

abbrev EquationInput := Input rho (trivial ℂ H ℂ) (DifferentialEquation.combined D R)

theorem equation_admissible_iff (f : IntertwiningMap rho (trivial ℂ H ℂ)) :
    f ∈ EquationInput D R rho ↔
      (∀ p ∈ DifferentialEquation.ideal D R, f p = 0) ∧ ∀ i p, f (D i p) = 0 := by
  change DifferentialEquation.relations D R ⊔ DifferentialEquation.ibp D ≤ f.toLinearMap.ker ↔ _
  rw [sup_le_iff]
  constructor
  · rintro ⟨he, hd⟩
    exact ⟨he, fun i p => hd (DifferentialEquation.derivative_mem_ibp D i p)⟩
  · rintro ⟨he, hd⟩
    refine ⟨he, ?_⟩
    rintro _ ⟨c, rfl⟩
    change f (DifferentialEquation.divergence D c) = 0
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c e hc he => simp only [map_add, hc, he, add_zero]
    | single i p => simpa only [DifferentialEquation.divergence_single] using hd i p

def equationEquiv := equiv rho (trivial ℂ H ℂ) (DifferentialEquation.combined D R) stable

@[simp] theorem equation_extraction (f : EquationInput D R rho) (p : A) :
    equationEquiv D R rho stable f (DifferentialEquation.integrated D R p) = f.val p := rfl
end Equations

end
end Math.JetInputAdapter

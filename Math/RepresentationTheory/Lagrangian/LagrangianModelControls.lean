import Math.RepresentationTheory.Lagrangian.LagrangianModel
import Math.RepresentationTheory.Lagrangian.InteractingLagrangianControls

/-! Artificial checks exercise the new packages without supplying a basis,
relation-span premise or global extension of selected coefficients. -/
namespace Math.LagrangianModelControls
set_option autoImplicit false
noncomputable section
open LocalPolynomial
@[reducible] local instance {F B I : Type*} : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance {F B I : Type*} : Module ℂ (A F B I) := inferInstance
@[reducible] local instance {F B I : Type*} : Ring (A F B I) := inferInstance

def cubic (g : ℂ) := LagrangianModel.Mixed.trivial (LagrangianControls.yukawa g)

theorem cubic_input (g : ℂ) : (cubic g).input = LagrangianControls.mixedModel g := rfl

theorem cubic_signs (g : ℂ) (q : (cubic g).Coordinates) :
    g*(cubic g).evaluate q ((LagrangianControls.psi false).eval * (LagrangianControls.psi true).eval) = 0 ∧
    g*(cubic g).evaluate q (LagrangianControls.h.eval * (LagrangianControls.psi true).eval) = 0 ∧
    -g*(cubic g).evaluate q (LagrangianControls.h.eval * (LagrangianControls.psi false).eval) = 0 :=
  InteractingLagrangianControls.yukawa_constraints g ((cubic g).equivalence.symm q)

theorem arbitrary_targets (g : ℂ) {T : Type*}
    (v : T → A Bool Unit Unit) (a : T → ℂ) :
    (∃ f : (cubic g).input.Coefficient, ∀ t, f.val (v t) = a t) ↔
      ∃ q : (cubic g).Coordinates, ∀ t, (cubic g).evaluate q (v t) = a t :=
  (cubic g).target_values_iff v a

theorem selected_roundtrip (g : ℂ) (V : Submodule ℂ (A Bool Unit Unit))
    (hV : ∀ h, V ≤ V.comap ((cubic g).action h))
    (f : ((cubic g).selected V hV).Coefficient) :
    ((cubic g).selectedEquivalence V hV).symm
      ((cubic g).selectedEquivalence V hV f) = f :=
  ((cubic g).selectedEquivalence V hV).symm_apply_apply f

theorem selected_targets (g : ℂ) (V : Submodule ℂ (A Bool Unit Unit))
    (hV : ∀ h, V ≤ V.comap ((cubic g).action h)) {T : Type*} (v : T → V) (a : T → ℂ) :
    (∃ f : ((cubic g).selected V hV).Coefficient, ∀ t, f.val (v t) = a t) ↔
      ∃ q : ((cubic g).selectedPresentation V hV).rows,
        ∀ t, ((cubic g).selectedPresentation V hV).assemble q.val (v t) = a t :=
  ((cubic g).selectedPresentation V hV).target_values_iff v a

theorem selected_full_preimage (g : ℂ) (V : Submodule ℂ (A Bool Unit Unit))
    (hV : ∀ h, V ≤ V.comap ((cubic g).action h)) :
    ((cubic g).selected V hV).relations = (cubic g).input.relations.comap V.subtype := rfl

theorem cancellation_euler {F B I : Type*} (p : Expr F B I) :
    (LagrangianModel.Mixed.trivial (p-p)).density.euler = 0 := by
  change (p-p).euler = 0
  rw [Expr.euler_sub,sub_self]

theorem cancellation_relations {F B I : Type*} (p : Expr F B I) :
    (LagrangianModel.Mixed.trivial (p-p)).input.relations = (VariationalIBP.divergence
      (D (F := F) (B := B) (I := I))).range := by
  have hz : (p-p).equations = ⊥ := by
    apply le_antisymm
    · apply TwoSidedDifferential.minimal
      · rintro _ ⟨s,rfl⟩
        change (p-p).euler s ∈ (⊥ : Submodule ℂ (A F B I))
        rw [Expr.euler_sub,sub_self,Finsupp.zero_apply]
        exact Submodule.zero_mem _
      · intro a u hu
        rw [Submodule.mem_bot] at hu ⊢
        rw [hu,mul_zero]
      · intro a u hu
        rw [Submodule.mem_bot] at hu ⊢
        rw [hu,zero_mul]
      · intro i u hu
        rw [Submodule.mem_bot] at hu ⊢
        rw [hu,map_zero]
    · exact bot_le
  change (p-p).equations ⊔ _ = _
  rw [hz,bot_sup_eq]

theorem no_equation_union (n : ℕ) :
    (PolynomialPotentialClassification.input 0 n).relations ≠
      (PolynomialPotentialClassification.input 1 n).relations ⊔
      (PolynomialPotentialClassification.input (-1) n).relations :=
  InteractingLagrangianControls.cancelled_equations_not_union n

end
end Math.LagrangianModelControls

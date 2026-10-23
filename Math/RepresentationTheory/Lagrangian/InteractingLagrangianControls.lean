import Math.RepresentationTheory.Lagrangian.InteractingLagrangianCoordinates
import Math.RepresentationTheory.Lagrangian.PolynomialPotentialClassification
import Math.Algebra.Variational.LagrangianControls

/-! Artificial interacting controls: full mixed coordinates, both odd signs,
exact nonlinear coupling branches and a counterexample to equation union. -/
namespace Math.InteractingLagrangianControls
set_option autoImplicit false
noncomputable section
open LocalPolynomial LagrangianControls

def yukawaEquivalence (g : ℂ) : (mixedModel g).Coefficient ≃ₗ[ℂ]
    (yukawa g).Coordinates (Representation.trivial ℂ Unit _) (fun _ => le_refl _) :=
  (yukawa g).allOrderEquivalence _ _

theorem yukawa_constraints (g : ℂ) (f : (mixedModel g).Coefficient) :
    g*f.val ((psi false).eval * (psi true).eval) = 0 ∧
    g*f.val (h.eval * (psi true).eval) = 0 ∧
    -g*f.val (h.eval * (psi false).eval) = 0 := by
  have he (s : Field Bool Unit) : f.val ((yukawa g).euler s) = 0 :=
    f.property (TwoSidedDifferential.combined_seed _ _ ⟨s,rfl⟩)
  refine ⟨?_,?_,?_⟩
  · simpa only [yukawa_even_euler,map_smul,smul_eq_mul] using he (.inr ())
  · simpa only [yukawa_first_odd_euler,map_smul,smul_eq_mul] using he (.inl false)
  · simpa only [yukawa_second_odd_euler,map_smul,smul_eq_mul] using he (.inl true)

theorem yukawa_zero_euler : (yukawa 0).euler = 0 := by
  rw [yukawa,Expr.euler_smul,zero_smul]

theorem yukawa_zero_relations : (yukawa 0).relations =
    (VariationalIBP.divergence (D (F := Bool) (B := Unit) (I := Unit))).range := by
  have hz : (yukawa 0).equations = ⊥ := by
    apply le_antisymm
    · apply TwoSidedDifferential.minimal
      · rintro u ⟨s,rfl⟩
        simp [yukawa_zero_euler]
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
  change (yukawa 0).equations ⊔ _ = _
  simp only [hz,bot_sup_eq]

open PolynomialPotentialClassification in
theorem cancelled_potential (n : ℕ) : potential 1 n + potential (-1) n = 0 := by
  simp [PolynomialPotentialClassification.potential,neg_div,neg_smul]

open PolynomialPotentialClassification in
theorem cancelled_equations_not_union (n : ℕ) :
    (input 0 n).relations ≠ (input 1 n).relations ⊔ (input (-1) n).relations := by
  intro he
  obtain ⟨f,hf⟩ := (target_value_iff 0 n n 1).mpr (Or.inl rfl)
  have hm : (Polynomial.X^n : A) ∈ (input 1 n).relations := by
    change (Polynomial.X^n : A) ∈ TwoSidedDifferential.combined
      PolynomialPotentialClassification.D (Set.range (seed 1 n))
    have h := TwoSidedDifferential.combined_seed PolynomialPotentialClassification.D
      (Set.range (seed 1 n)) ⟨(),rfl⟩
    simpa only [seed,one_smul] using h
  have hz : f.val (Polynomial.X^n) = 0 := f.property (by rw [he]; exact Submodule.mem_sup_left hm)
  rw [hf] at hz
  exact one_ne_zero hz

end
end Math.InteractingLagrangianControls

import Math.Algebra.Jets.JetCombined
import Math.RepresentationTheory.Jets.JetGradeAction
import Math.RepresentationTheory.Jets.CovariantJetIBP

/-! Actual direction-mixing actions and covariant IBP on scalar and mixed jets. -/
namespace Math.DirectionalJetIBP
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra JetDirections

variable {S F B I H : Type*} [Fintype I] [Group H]
  (σ : Representation ℂ H (Direction I))

section Scalar
variable (ρ : Representation ℂ H (JetLinear.Field S))

abbrev scalarAction (n d : ℕ) :=
  JetFunctor.scalarGradeAction (combined ρ σ) (combined_order ρ σ) n d

omit [Fintype I] in
@[simp] theorem scalarAction_apply (n d : ℕ) (h : H) (p : grade (S := S) (I := I) n d) :
    (scalarAction σ ρ n d h p).val = JetFunctor.polynomialAction (combined ρ σ) h p.val := rfl

theorem scalar_covariance (n : ℕ) (h : H) (i : I) (d : ℕ)
    (p : grade (S := S) (I := I) n d) :
    scalarAction σ ρ n (d + 1) h (derivative i n d p) =
      ∑ j, (σ h (Finsupp.single i 1)) j • derivative j n d (scalarAction σ ρ n d h p) := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, scalarAction_apply,
    ScalarJetAlgebra.derivative_apply] using
    JetFunctor.polynomial_covariant (combined ρ σ) h i
      (fun j => (σ h (Finsupp.single i 1)) j) (combined_covariant ρ σ h i) p.val

def scalarCoefficientEquiv (n d : ℕ) :=
  CovariantJetIBP.coefficientEquiv (fun i d => derivative (S := S) i n d)
    σ (scalarAction σ ρ n) (fun h i d => scalar_covariance σ ρ n h i d) d

theorem scalar_relations_stable (n d : ℕ) : ∀ h,
    GradedJetIBP.relations (fun i d => derivative (S := S) i n d) d ≤
      (GradedJetIBP.relations (fun i d => derivative (S := S) i n d) d).comap
        (scalarAction σ ρ n (d + 1) h) := by
  simpa only [← CovariantJetIBP.relations_eq] using
    CovariantJetIBP.stable (fun i d => derivative (S := S) i n d)
      σ (scalarAction σ ρ n) (fun h i d => scalar_covariance σ ρ n h i d) d
end Scalar

section Mixed
variable (ρF : Representation ℂ H (JetLinear.Field F))
  (ρB : Representation ℂ H (JetLinear.Field B))

abbrev mixedAction (n m d : ℕ) :=
  JetFunctor.mixedGradeAction (combined ρF σ) (combined ρB σ)
    (combined_order ρF σ) (combined_order ρB σ) n m d

omit [Fintype I] in
@[simp] theorem mixedAction_apply (n m d : ℕ) (h : H)
    (p : MixedJetAlgebra.grade F B I n m d) :
    (mixedAction σ ρF ρB n m d h p).val =
      JetFunctor.mixedAction (combined ρF σ) (combined ρB σ) h p.val := rfl

omit [Fintype I] in
@[simp] theorem mixedDerivative_apply (n m d : ℕ) (i : I)
    (p : MixedJetAlgebra.grade F B I n m d) :
    (MixedJetAlgebra.derivative i n m d p).val = MixedJetAlgebra.totalDerivative i p.val := rfl

theorem mixed_covariance (n m : ℕ) (h : H) (i : I) (d : ℕ)
    (p : MixedJetAlgebra.grade F B I n m d) :
    mixedAction σ ρF ρB n m (d + 1) h (MixedJetAlgebra.derivative i n m d p) =
      ∑ j, (σ h (Finsupp.single i 1)) j •
        MixedJetAlgebra.derivative j n m d (mixedAction σ ρF ρB n m d h p) := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, mixedAction_apply,
    mixedDerivative_apply] using
    JetFunctor.mixed_covariant (combined ρF σ) (combined ρB σ) h i
      (fun j => (σ h (Finsupp.single i 1)) j)
      (combined_covariant ρF σ h i) (combined_covariant ρB σ h i) p.val

def mixedDerivatives (n m : ℕ) (i : I) (d : ℕ) :=
  MixedJetAlgebra.derivative (F := F) (B := B) i n m d

def mixedCoefficientEquiv (n m d : ℕ) :=
  CovariantJetIBP.coefficientEquiv (V := fun d => MixedJetAlgebra.grade F B I n m d)
    (mixedDerivatives (F := F) (B := B) (I := I) n m)
    σ (mixedAction σ ρF ρB n m) (fun h i d => mixed_covariance σ ρF ρB n m h i d) d

def mixedSourceEquiv (n m d : ℕ) :=
  JetFunctor.gradeRepresentationEquiv (combined ρF σ) (combined ρB σ)
    (combined_order ρF σ) (combined_order ρB σ) n m d

end Mixed
end
end Math.DirectionalJetIBP

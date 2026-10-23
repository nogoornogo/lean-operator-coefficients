import Math.Algebra.Jets.JetLinear
import Math.RepresentationTheory.Jets.GradedJetIBP

/-! Actual scalar IBP descent for arbitrary internal linear field actions. -/
namespace Math.ScalarLinearIBP
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra JetLinear Representation

variable {S I H : Type*} [Group H] (ρ : Representation ℂ H (JetLinear.Field S))

def derivatives (n : ℕ) (i : I) (d : ℕ) := derivative (S := S) i n d

theorem covariance (n : ℕ) (h : H) (i : I) (d : ℕ) (p : grade (S := S) (I := I) n d) :
    gradeAction ρ n (d + 1) h (derivatives n i d p) =
      derivatives n i d (gradeAction ρ n d h p) :=
  (derivative_gradeMap (ρ h) i n d p).symm

abbrev relations (n d : ℕ) := GradedJetIBP.relations (derivatives (S := S) (I := I) n) d

theorem relations_stable (n d : ℕ) : ∀ h,
    relations (S := S) (I := I) n d ≤
      (relations n d).comap (gradeAction ρ n (d + 1) h) :=
  GradedJetIBP.stable (derivatives n) (gradeAction ρ n) (covariance ρ n) d

abbrev Coefficient (n d : ℕ) :=
  GradedJetIBP.Coefficient (derivatives (I := I) n) (gradeAction ρ n) d

def coefficientEquiv (n d : ℕ) :=
  GradedJetIBP.coefficientEquiv (derivatives (I := I) n) (gradeAction ρ n) (covariance ρ n) d

section Local
variable {G : Type*} [Group G] (a : Representation ℂ G (JetLinear.Field S))
  (comm : ∀ g h v, a g (ρ h v) = ρ h (a g v))

include comm in
theorem actions_commute (n d : ℕ) (g : G) (h : H) (p : grade (S := S) (I := I) n d) :
    gradeAction a n d g (gradeAction ρ n d h p) =
      gradeAction ρ n d h (gradeAction a n d g p) := by
  apply Subtype.ext
  have he : (a g).comp (ρ h) = (ρ h).comp (a g) := LinearMap.ext (comm g h)
  change polynomialMap (a g) (polynomialMap (ρ h) p.val) =
    polynomialMap (ρ h) (polynomialMap (a g) p.val)
  rw [← AlgHom.comp_apply, ← polynomialMap_comp, he, polynomialMap_comp]
  rfl

def localEquiv (n d : ℕ) := GradedJetIBP.localEquiv
  (derivatives (I := I) n) (gradeAction ρ n) (covariance ρ n)
  (gradeAction a n) (actions_commute ρ a comm n) d

abbrev LocalCoefficient (n d : ℕ) := GradedJetIBP.LocalCoefficient
  (derivatives (I := I) n) (gradeAction ρ n) (gradeAction a n) d

abbrev residual (n d : ℕ) := GradedJetIBP.residual
  (derivatives (I := I) n) (gradeAction ρ n) (covariance ρ n)
  (gradeAction a n) (actions_commute ρ a comm n) d

theorem local_nonzero_iff (n d : ℕ) :
    (∃ f : LocalCoefficient (I := I) ρ a n d, f ≠ 0) ↔
      ∃ f : IntertwiningMap (residual (I := I) ρ a comm n d) (trivial ℂ H ℂ), f ≠ 0 :=
  GradedJetIBP.local_nonzero_iff
  (derivatives (I := I) n) (gradeAction ρ n) (covariance ρ n)
  (gradeAction a n) (actions_commute ρ a comm n) d
end Local

end
end Math.ScalarLinearIBP

import Math.RepresentationTheory.Jets.MixedJetAction
import Math.RepresentationTheory.Jets.GradedJetIBP

/-! Actual mixed divergence ranges and inverse local/residual coefficient descent.
No ideal closure or exchange of invariants with quotients is used. -/
namespace Math.MixedJetIBP
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra Representation

variable {F B I H : Type*} [Group H]
  (ρF : Representation ℂ H (JetLinear.Field F)) (ρB : Representation ℂ H (JetLinear.Field B))

@[reducible] local instance (n m d : ℕ) : AddCommGroup (grade F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (grade F B I n m d) := inferInstance

def derivatives (n m : ℕ) (i : I) (d : ℕ) :
    grade F B I n m d →ₗ[ℂ] grade F B I n m (d + 1) := derivative i n m d

theorem covariance (n m : ℕ) (h : H) (i : I) (d : ℕ) (p : grade F B I n m d) :
    gradeAction ρF ρB n m (d + 1) h (derivatives n m i d p) =
      derivatives n m i d (gradeAction ρF ρB n m d h p) :=
  derivative_covariant ρF ρB n m d h i p

abbrev divergence (n m d : ℕ) := GradedJetIBP.divergence (V := fun d => grade F B I n m d) (derivatives (F := F) (B := B) (I := I) n m) d
abbrev relations (n m d : ℕ) := GradedJetIBP.relations (V := fun d => grade F B I n m d) (derivatives (F := F) (B := B) (I := I) n m) d

theorem annihilates_iff {W : Type*} [AddCommGroup W] [Module ℂ W] (n m d : ℕ)
    (f : grade F B I n m (d + 1) →ₗ[ℂ] W) :
    relations n m d ≤ f.ker ↔ ∀ i p, f (derivative i n m d p) = 0 :=
  GradedJetIBP.annihilates_iff (V := fun d => grade F B I n m d) (derivatives n m) d f

theorem relations_stable (n m d : ℕ) : ∀ h,
    relations (F := F) (B := B) (I := I) n m d ≤
      (relations n m d).comap (gradeAction ρF ρB n m (d + 1) h) :=
  GradedJetIBP.stable (V := fun d => grade F B I n m d) (derivatives n m) (gradeAction ρF ρB n m) (covariance ρF ρB n m) d

abbrev Coefficient (n m d : ℕ) :=
  GradedJetIBP.Coefficient (V := fun d => grade F B I n m d) (derivatives (I := I) n m) (gradeAction ρF ρB n m) d

def coefficientEquiv (n m d : ℕ) := GradedJetIBP.coefficientEquiv
  (derivatives (I := I) n m) (gradeAction ρF ρB n m) (covariance ρF ρB n m) d

def multiply {n m d p q e : ℕ} (x : grade F B I n m d) (y : grade F B I p q e) :
    grade F B I (n + p) (m + q) (d + e) := ⟨x.val * y.val, mul_mem x.property y.property⟩

def productLeft {n m d p q e : ℕ} (i : I)
    (x : grade F B I n m d) (y : grade F B I p q e) :
    grade F B I (n + p) (m + q) (d + e + 1) :=
  ⟨x.val * totalDerivative i y.val, by
    simpa only [Nat.add_assoc] using mul_mem x.property (totalDerivative_mem i y.property)⟩

def productRight {n m d p q e : ℕ} (i : I)
    (x : grade F B I n m d) (y : grade F B I p q e) :
    grade F B I (n + p) (m + q) (d + e + 1) :=
  ⟨totalDerivative i x.val * y.val, by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      mul_mem (totalDerivative_mem i x.property) y.property⟩

theorem derivative_multiply {n m d p q e : ℕ} (i : I)
    (x : grade F B I n m d) (y : grade F B I p q e) :
    derivative i (n + p) (m + q) (d + e) (multiply x y) = productLeft i x y + productRight i x y := by
  apply Subtype.ext
  exact (totalDerivative_mul i x.val y.val).trans (add_comm _ _)

theorem integration_by_parts {n m d p q e : ℕ} (i : I)
    (x : grade F B I n m d) (y : grade F B I p q e)
    (f : Coefficient (I := I) ρF ρB (n + p) (m + q) (d + e)) :
    f.val (productLeft i x y) = -f.val (productRight i x y) := by
  have hz := f.property (GradedJetIBP.derivative_mem (V := fun d => grade F B I (n + p) (m + q) d) (derivatives (n + p) (m + q))
    (d + e) i (multiply x y))
  change f.val (derivative i (n + p) (m + q) (d + e) (multiply x y)) = 0 at hz
  rw [derivative_multiply, map_add] at hz
  exact eq_neg_of_add_eq_zero_left hz

section Local
variable {G : Type*} [Group G]
  (aF : Representation ℂ G (JetLinear.Field F)) (aB : Representation ℂ G (JetLinear.Field B))
  (commF : ∀ g h v, aF g (ρF h v) = ρF h (aF g v))
  (commB : ∀ g h v, aB g (ρB h v) = ρB h (aB g v))

abbrev LocalCoefficient (n m d : ℕ) := GradedJetIBP.LocalCoefficient
  (derivatives (I := I) n m) (gradeAction ρF ρB n m) (gradeAction aF aB n m) d

abbrev residual (n m d : ℕ) := GradedJetIBP.residual
  (derivatives (I := I) n m) (gradeAction ρF ρB n m) (covariance ρF ρB n m)
  (gradeAction aF aB n m) (grade_actions_commute aF aB ρF ρB commF commB n m) d

def localEquiv (n m d : ℕ) := GradedJetIBP.localEquiv
  (derivatives (I := I) n m) (gradeAction ρF ρB n m) (covariance ρF ρB n m)
  (gradeAction aF aB n m) (grade_actions_commute aF aB ρF ρB commF commB n m) d

theorem local_nonzero_iff (n m d : ℕ) :
    (∃ f : LocalCoefficient (I := I) ρF ρB aF aB n m d, f ≠ 0) ↔
      ∃ f : IntertwiningMap (residual (I := I) ρF ρB aF aB commF commB n m d) (trivial ℂ H ℂ), f ≠ 0 :=
  GradedJetIBP.local_nonzero_iff
    (derivatives (I := I) n m) (gradeAction ρF ρB n m) (covariance ρF ρB n m)
    (gradeAction aF aB n m) (grade_actions_commute aF aB ρF ρB commF commB n m) d
end Local

end
end Math.MixedJetIBP

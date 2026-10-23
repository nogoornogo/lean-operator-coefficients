import Math.Algebra.Jets.JetEquation
import Math.RepresentationTheory.Jets.DirectionalJetIBP

/-! Actual on-shell derivatives, finite homogeneous images and EOM/IBP descent.
Homogeneous images are used without asserting a global direct-sum decomposition. -/
namespace Math.JetEquation
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections

variable {S I H : Type*} [Group H] (q : Symbols I)
  (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
  (hq : ∀ h, symbolMap (σ h) q = q)

@[simp] theorem generatorAction_mk (h : H) (v : Jet S I) :
    generatorAction q ρ σ hq h ((relations S q).mkQ v) =
      (relations S q).mkQ (combined ρ σ h v) := rfl

def action : Representation ℂ H (Algebra S q) :=
  PhyslibSymmetric.Representation.symmetricAlgebra (generatorAction q ρ σ hq)

theorem projection_action (h : H) (p : ScalarJetAlgebra.Algebra S I) :
    projection q (JetFunctor.polynomialAction (combined ρ σ) h p) = action q ρ σ hq h (projection q p) := by
  have he : (projection (S := S) q).comp (JetFunctor.polynomialMap (combined ρ σ h)) =
      (PhyslibSymmetric.Representation.symmetricAlgebraAlgHom (generatorAction q ρ σ hq) h).comp
        (projection q) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, JetFunctor.polynomialMap_X, projection_linearForm, projection_X,
      PhyslibSymmetric.Representation.symmetricAlgebraAlgHom, SymmetricAlgebra.lift_ι_apply,
      LinearMap.comp_apply, generatorAction_mk]
  exact DFunLike.congr_fun he p

include hq in
theorem ideal_action_stable (h : H) {p : ScalarJetAlgebra.Algebra S I} (hp : p ∈ ideal S q) :
    JetFunctor.polynomialAction (combined ρ σ) h p ∈ ideal S q := by
  rw [← projection_ker] at hp ⊢
  change projection q p = 0 at hp
  change projection q (JetFunctor.polynomialAction (combined ρ σ) h p) = 0
  rw [projection_action q ρ σ hq, hp, map_zero]

theorem ideal_derivative_stable (i : I) {p : ScalarJetAlgebra.Algebra S I} (hp : p ∈ ideal S q) :
    ScalarJetAlgebra.totalDerivative i p ∈ ideal S q := by
  rw [← projection_ker] at hp ⊢
  change projection q p = 0 at hp
  change projection q (ScalarJetAlgebra.totalDerivative i p) = 0
  rw [projection_derivative, hp, map_zero]

theorem covariance [Fintype I] (h : H) (i : I) (p : Algebra S q) :
    action q ρ σ hq h (derivative q i p) =
      ∑ j, (σ h (Finsupp.single i 1)) j • derivative q j (action q ρ σ hq h p) :=
  PhyslibSymmetric.SymmetricAlgebra.symmetricAlgebra_derivationOfLinear
    (generatorAction q ρ σ hq) h (shift q) i _ (generator_covariant q ρ σ hq h i) p

def grade (S : Type*) (q : Symbols I) (n d : ℕ) : Submodule ℂ (Algebra S q) :=
  (ScalarJetAlgebra.grade (S := S) (I := I) n d).map (projection q).toLinearMap

def gradeProjection (n d : ℕ) : ScalarJetAlgebra.grade (S := S) (I := I) n d →ₗ[ℂ] grade S q n d where
  toFun p := ⟨projection q p.val, ⟨p.val, p.property, rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem gradeProjection_apply (n d : ℕ) (p : ScalarJetAlgebra.grade (S := S) (I := I) n d) :
    (gradeProjection q n d p).val = projection q p.val := rfl

theorem gradeProjection_surjective (n d : ℕ) : Function.Surjective (gradeProjection (S := S) q n d) := by
  intro p
  obtain ⟨x, hx, he⟩ := p.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

instance grade_finite [Finite S] [Finite I] (n d : ℕ) : FiniteDimensional ℂ (grade S q n d) :=
  Module.Finite.of_surjective (gradeProjection q n d) (gradeProjection_surjective q n d)

theorem derivative_mem (i : I) (n d : ℕ) {p : Algebra S q} (hp : p ∈ grade S q n d) :
    derivative q i p ∈ grade S q n (d + 1) := by
  obtain ⟨p, hp, rfl⟩ := hp
  change derivative q i (projection q p) ∈ grade S q n (d + 1)
  rw [← projection_derivative]
  exact ⟨_, ScalarJetAlgebra.totalDerivative_mem i hp, rfl⟩

def gradeDerivative (n : ℕ) (i : I) (d : ℕ) : grade S q n d →ₗ[ℂ] grade S q n (d + 1) where
  toFun p := ⟨derivative q i p.val, derivative_mem q i n d p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem gradeDerivative_apply (n d : ℕ) (i : I) (p : grade S q n d) :
    (gradeDerivative q n i d p).val = derivative q i p.val := rfl

theorem gradeProjection_derivative (n d : ℕ) (i : I)
    (p : ScalarJetAlgebra.grade (S := S) (I := I) n d) :
    gradeProjection q n (d + 1) (ScalarJetAlgebra.derivative i n d p) =
      gradeDerivative q n i d (gradeProjection q n d p) :=
  Subtype.ext (projection_derivative q i p.val)

include hq in
theorem action_mem (h : H) (n d : ℕ) {p : Algebra S q} (hp : p ∈ grade S q n d) :
    action q ρ σ hq h p ∈ grade S q n d := by
  obtain ⟨p, hp, rfl⟩ := hp
  change action q ρ σ hq h (projection q p) ∈ grade S q n d
  rw [← projection_action]
  exact ⟨_, JetFunctor.polynomialMap_homogeneous (combined ρ σ h) (combined_order ρ σ h) hp, rfl⟩

def gradeAction (n d : ℕ) : Representation ℂ H (grade S q n d) :=
  (action q ρ σ hq).subrepresentation (grade S q n d) (fun h _ hp => action_mem q ρ σ hq h n d hp)

@[simp] theorem gradeAction_apply (n d : ℕ) (h : H) (p : grade S q n d) :
    (gradeAction q ρ σ hq n d h p).val = action q ρ σ hq h p.val := rfl

theorem grade_covariance [Fintype I] (n : ℕ) (h : H) (i : I) (d : ℕ) (p : grade S q n d) :
    gradeAction q ρ σ hq n (d + 1) h (gradeDerivative q n i d p) =
      ∑ j, (σ h (Finsupp.single i 1)) j • gradeDerivative q n j d (gradeAction q ρ σ hq n d h p) := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, gradeAction_apply, gradeDerivative_apply] using
    covariance q ρ σ hq h i p.val

def coefficientEquiv [Fintype I] (n d : ℕ) :=
  CovariantJetIBP.coefficientEquiv (V := fun d => grade S q n d) (gradeDerivative q n)
    σ (gradeAction q ρ σ hq n) (fun h i d => grade_covariance q ρ σ hq n h i d) d

end
end Math.JetEquation

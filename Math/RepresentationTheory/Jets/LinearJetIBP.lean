import Math.RepresentationTheory.Jets.LinearJetAction
import Math.RepresentationTheory.Jets.JetEquationComparison

/-! Finite image grades, actual EOM/IBP quotient comparison and equivariant
coefficient descent for component-mixing odd/even linear equations. -/
namespace Math.LinearJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections Representation

variable {F B I EF EB : Type*} [AddCommGroup EF] [Module ℂ EF]
  [AddCommGroup EB] [Module ℂ EB]
  (eF : EF →ₗ[ℂ] Jet F I) (eB : EB →ₗ[ℂ] Jet B I)

def grade (n m d : ℕ) : Submodule ℂ (Algebra eF eB) :=
  (MixedJetAlgebra.grade F B I n m d).map (projection eF eB).toLinearMap

def gradeProjection (n m d : ℕ) : MixedJetAlgebra.grade F B I n m d →ₗ[ℂ] grade eF eB n m d where
  toFun x := ⟨projection eF eB x.val, ⟨x.val, x.property, rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem gradeProjection_surjective (n m d : ℕ) : Function.Surjective (gradeProjection eF eB n m d) := by
  intro x
  obtain ⟨x, hx, he⟩ := x.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

instance grade_finite [Finite F] [Finite B] [Finite I] (n m d : ℕ) :
    FiniteDimensional ℂ (grade eF eB n m d) :=
  Module.Finite.of_surjective (gradeProjection eF eB n m d) (gradeProjection_surjective eF eB n m d)

theorem derivative_mem (i : I) (n m d : ℕ) {x : Algebra eF eB} (hx : x ∈ grade eF eB n m d) :
    derivative eF eB i x ∈ grade eF eB n m (d + 1) := by
  obtain ⟨x, hx, rfl⟩ := hx
  change derivative eF eB i (projection eF eB x) ∈ grade eF eB n m (d + 1)
  rw [← projection_derivative]
  exact ⟨_, MixedJetAlgebra.totalDerivative_mem i hx, rfl⟩

def gradeDerivative (n m : ℕ) (i : I) (d : ℕ) : grade eF eB n m d →ₗ[ℂ] grade eF eB n m (d + 1) where
  toFun x := ⟨derivative eF eB i x.val, derivative_mem eF eB i n m d x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem gradeDerivative_apply (n m d : ℕ) (i : I) (x : grade eF eB n m d) :
    (gradeDerivative eF eB n m i d x).val = derivative eF eB i x.val := rfl

theorem gradeProjection_derivative (n m d : ℕ) (i : I) (x : MixedJetAlgebra.grade F B I n m d) :
    gradeProjection eF eB n m (d + 1) (MixedJetAlgebra.derivative i n m d x) =
      gradeDerivative eF eB n m i d (gradeProjection eF eB n m d x) :=
  Subtype.ext (projection_derivative eF eB i x.val)

@[reducible] local instance (n m d : ℕ) : AddCommGroup (grade eF eB n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (grade eF eB n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : AddCommGroup (MixedJetAlgebra.grade F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (MixedJetAlgebra.grade F B I n m d) := inferInstance

abbrev offRelations (n m d : ℕ) := GradedJetIBP.relations
  (V := fun d => MixedJetAlgebra.grade F B I n m d)
  (DirectionalJetIBP.mixedDerivatives (F := F) (B := B) (I := I) n m) d

abbrev ibpRelations (n m d : ℕ) := GradedJetIBP.relations
  (V := fun d => grade eF eB n m d) (gradeDerivative eF eB n m) d

theorem ibpRelations_map (n m d : ℕ) : ibpRelations eF eB n m d =
    (offRelations (F := F) (B := B) (I := I) n m d).map (gradeProjection eF eB n m (d + 1)) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i x =>
      obtain ⟨x, rfl⟩ := gradeProjection_surjective eF eB n m d x
      rw [GradedJetIBP.divergence_single, ← gradeProjection_derivative]
      exact ⟨_, GradedJetIBP.derivative_mem (DirectionalJetIBP.mixedDerivatives n m) d i x, rfl⟩
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i x =>
      rw [GradedJetIBP.divergence_single]
      change gradeProjection eF eB n m (d + 1) (MixedJetAlgebra.derivative i n m d x) ∈ _
      rw [gradeProjection_derivative]
      exact GradedJetIBP.derivative_mem (gradeDerivative eF eB n m) d i _

def combinedRelations (n m d : ℕ) : Submodule ℂ (MixedJetAlgebra.grade F B I n m (d + 1)) :=
  (gradeProjection eF eB n m (d + 1)).ker ⊔ offRelations n m d

theorem combinedRelations_comap (n m d : ℕ) : combinedRelations eF eB n m d =
    (ibpRelations eF eB n m d).comap (gradeProjection eF eB n m (d + 1)) := by
  rw [ibpRelations_map, Submodule.comap_map_eq]
  exact sup_comm _ _

def combinedProjection (n m d : ℕ) : MixedJetAlgebra.grade F B I n m (d + 1) →ₗ[ℂ]
    (grade eF eB n m (d + 1) ⧸ ibpRelations eF eB n m d) :=
  (ibpRelations eF eB n m d).mkQ.comp (gradeProjection eF eB n m (d + 1))

theorem combinedProjection_ker (n m d : ℕ) :
    (combinedProjection eF eB n m d).ker = combinedRelations eF eB n m d := by
  rw [combinedProjection, LinearMap.ker_comp, Submodule.ker_mkQ, combinedRelations_comap]

theorem combinedProjection_surjective (n m d : ℕ) : Function.Surjective (combinedProjection eF eB n m d) :=
  (ibpRelations eF eB n m d).mkQ_surjective.comp (gradeProjection_surjective eF eB n m (d + 1))

def combinedQuotientEquiv (n m d : ℕ) :
    (MixedJetAlgebra.grade F B I n m (d + 1) ⧸ combinedRelations eF eB n m d) ≃ₗ[ℂ]
      (grade eF eB n m (d + 1) ⧸ ibpRelations eF eB n m d) :=
  (Submodule.quotEquivOfEq _ _ (combinedProjection_ker eF eB n m d).symm).trans
    ((combinedProjection eF eB n m d).quotKerEquivOfSurjective (combinedProjection_surjective eF eB n m d))

@[simp] theorem combinedQuotientEquiv_mk (n m d : ℕ) (x : MixedJetAlgebra.grade F B I n m (d + 1)) :
    combinedQuotientEquiv eF eB n m d ((combinedRelations eF eB n m d).mkQ x) =
      (ibpRelations eF eB n m d).mkQ (gradeProjection eF eB n m (d + 1) x) := rfl

def combinedCoefficientEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] (n m d : ℕ) :
    ((MixedJetAlgebra.grade F B I n m (d + 1) ⧸ combinedRelations eF eB n m d) →ₗ[ℂ] W) ≃ₗ[ℂ]
      ((grade eF eB n m (d + 1) ⧸ ibpRelations eF eB n m d) →ₗ[ℂ] W) :=
  LinearEquiv.arrowCongr (combinedQuotientEquiv eF eB n m d) (LinearEquiv.refl ℂ W)

section Action
variable {H : Type*} [Group H] [Fintype I]
  (τF : Representation ℂ H EF) (τB : Representation ℂ H EB)
  (ρF : Representation ℂ H (JetLinear.Field F)) (ρB : Representation ℂ H (JetLinear.Field B))
  (σ : Representation ℂ H (Direction I))
  (cF : ∀ h x, combined ρF σ h (eF x) = eF (τF h x))
  (cB : ∀ h x, combined ρB σ h (eB x) = eB (τB h x))

omit [Fintype I] in
include cF cB in
theorem action_mem (g : H) (n m d : ℕ) {x : Algebra eF eB} (hx : x ∈ grade eF eB n m d) :
    action eF eB τF τB ρF ρB σ cF cB g x ∈ grade eF eB n m d := by
  obtain ⟨x, hx, rfl⟩ := hx
  change action eF eB τF τB ρF ρB σ cF cB g (projection eF eB x) ∈ grade eF eB n m d
  rw [← projection_action]
  exact ⟨_, (DirectionalJetIBP.mixedAction σ ρF ρB n m d g ⟨x, hx⟩).property, rfl⟩

def gradeAction (n m d : ℕ) : Representation ℂ H (grade eF eB n m d) :=
  (action eF eB τF τB ρF ρB σ cF cB).subrepresentation (grade eF eB n m d)
    (fun g _ hx => action_mem eF eB τF τB ρF ρB σ cF cB g n m d hx)

omit [Fintype I] in
@[simp] theorem gradeAction_apply (n m d : ℕ) (g : H) (x : grade eF eB n m d) :
    (gradeAction eF eB τF τB ρF ρB σ cF cB n m d g x).val =
      action eF eB τF τB ρF ρB σ cF cB g x.val := rfl

omit [Fintype I] in
theorem gradeProjection_action (n m d : ℕ) (g : H) (x : MixedJetAlgebra.grade F B I n m d) :
    gradeProjection eF eB n m d (DirectionalJetIBP.mixedAction σ ρF ρB n m d g x) =
      gradeAction eF eB τF τB ρF ρB σ cF cB n m d g (gradeProjection eF eB n m d x) :=
  Subtype.ext (projection_action eF eB τF τB ρF ρB σ cF cB g x.val)

theorem grade_covariance (n m : ℕ) (g : H) (i : I) (d : ℕ) (x : grade eF eB n m d) :
    gradeAction eF eB τF τB ρF ρB σ cF cB n m (d + 1) g (gradeDerivative eF eB n m i d x) =
      ∑ j, (σ g (Finsupp.single i 1)) j • gradeDerivative eF eB n m j d
        (gradeAction eF eB τF τB ρF ρB σ cF cB n m d g x) := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, gradeAction_apply, gradeDerivative_apply] using
    covariance eF eB τF τB ρF ρB σ cF cB g i x.val

theorem ibp_stable (n m d : ℕ) : ∀ g, ibpRelations eF eB n m d ≤
    (ibpRelations eF eB n m d).comap (gradeAction eF eB τF τB ρF ρB σ cF cB n m (d + 1) g) := by
  intro g x hx
  obtain ⟨c, rfl⟩ := hx
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
  | single i x =>
    rw [GradedJetIBP.divergence_single]
    change gradeAction eF eB τF τB ρF ρB σ cF cB n m (d + 1) g
      (gradeDerivative eF eB n m i d x) ∈ ibpRelations eF eB n m d
    rw [grade_covariance]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (GradedJetIBP.derivative_mem (gradeDerivative eF eB n m) d j _))

def quotientAction (n m d : ℕ) :=
  (gradeAction eF eB τF τB ρF ρB σ cF cB n m (d + 1)).quotient
    (ibpRelations eF eB n m d) (ibp_stable eF eB τF τB ρF ρB σ cF cB n m d)

theorem combinedProjection_action (n m d : ℕ) (g : H) (x : MixedJetAlgebra.grade F B I n m (d + 1)) :
    combinedProjection eF eB n m d (DirectionalJetIBP.mixedAction σ ρF ρB n m (d + 1) g x) =
      quotientAction eF eB τF τB ρF ρB σ cF cB n m d g (combinedProjection eF eB n m d x) := by
  change (ibpRelations eF eB n m d).mkQ
    (gradeProjection eF eB n m (d + 1) (DirectionalJetIBP.mixedAction σ ρF ρB n m (d + 1) g x)) = _
  rw [gradeProjection_action]
  rfl

include cF cB in
theorem combined_stable (n m d : ℕ) : ∀ g, combinedRelations eF eB n m d ≤
    (combinedRelations eF eB n m d).comap (DirectionalJetIBP.mixedAction σ ρF ρB n m (d + 1) g) := by
  intro g x hx
  rw [← combinedProjection_ker] at hx
  change combinedProjection eF eB n m d x = 0 at hx
  change DirectionalJetIBP.mixedAction σ ρF ρB n m (d + 1) g x ∈ combinedRelations eF eB n m d
  rw [← combinedProjection_ker]
  change combinedProjection eF eB n m d _ = 0
  rw [combinedProjection_action eF eB τF τB ρF ρB σ cF cB, hx, map_zero]

def combinedAction (n m d : ℕ) :=
  (DirectionalJetIBP.mixedAction σ ρF ρB n m (d + 1)).quotient
    (combinedRelations eF eB n m d) (combined_stable eF eB τF τB ρF ρB σ cF cB n m d)

def combinedRepresentationEquiv (n m d : ℕ) : Representation.Equiv
    (combinedAction eF eB τF τB ρF ρB σ cF cB n m d) (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) :=
  Representation.Equiv.mk (combinedQuotientEquiv eF eB n m d) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (combinedRelations eF eB n m d).mkQ_surjective x
    exact combinedProjection_action eF eB τF τB ρF ρB σ cF cB n m d g x)

def coefficientEquiv (n m d : ℕ) := CovariantJetIBP.coefficientEquiv
  (gradeDerivative eF eB n m) σ (gradeAction eF eB τF τB ρF ρB σ cF cB n m)
  (fun g i d => grade_covariance eF eB τF τB ρF ρB σ cF cB n m g i d) d

end Action
end
end Math.LinearJetAlgebra

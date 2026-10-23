import Math.RepresentationTheory.Jets.JetEquationIBP

/-! The on-shell divergence quotient equals the off-shell source modulo
the sum of EOM and actual IBP relations, with inverse coefficient transport. -/
namespace Math.JetEquation
set_option autoImplicit false
noncomputable section
open JetDirections

variable {S I : Type*} (q : Symbols I)

def offDerivatives (n : ℕ) (i : I) (d : ℕ) := ScalarJetAlgebra.derivative (S := S) i n d

abbrev offRelations (n d : ℕ) := GradedJetIBP.relations (offDerivatives (S := S) (I := I) n) d
abbrev shellRelations (n d : ℕ) := GradedJetIBP.relations (gradeDerivative (S := S) q n) d

theorem shellRelations_map (n d : ℕ) : shellRelations (S := S) q n d =
    (offRelations (S := S) (I := I) n d).map (gradeProjection q n (d + 1)) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i p =>
      obtain ⟨p, rfl⟩ := gradeProjection_surjective q n d p
      rw [GradedJetIBP.divergence_single, ← gradeProjection_derivative]
      exact ⟨_, GradedJetIBP.derivative_mem (offDerivatives n) d i p, rfl⟩
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
    | single i p =>
      rw [GradedJetIBP.divergence_single]
      change gradeProjection q n (d + 1) (ScalarJetAlgebra.derivative i n d p) ∈ _
      rw [gradeProjection_derivative]
      exact GradedJetIBP.derivative_mem (gradeDerivative q n) d i (gradeProjection q n d p)

def combinedRelations (n d : ℕ) : Submodule ℂ (ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1)) :=
  (gradeProjection q n (d + 1)).ker ⊔ offRelations n d

theorem combinedRelations_comap (n d : ℕ) : combinedRelations (S := S) q n d =
    (shellRelations q n d).comap (gradeProjection q n (d + 1)) := by
  rw [shellRelations_map, Submodule.comap_map_eq]
  exact sup_comm _ _

theorem eom_kernel_iff (n d : ℕ) (p : ScalarJetAlgebra.grade (S := S) (I := I) n d) :
    p ∈ (gradeProjection q n d).ker ↔ p.val ∈ ideal S q := by
  change gradeProjection q n d p = 0 ↔ _
  rw [show gradeProjection q n d p = 0 ↔ projection q p.val = 0 from
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩]
  exact (show projection q p.val = 0 ↔ p.val ∈ RingHom.ker (projection q).toRingHom from Iff.rfl).trans
    (by rw [projection_ker])

def combinedProjection (n d : ℕ) : ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1) →ₗ[ℂ]
    (grade S q n (d + 1) ⧸ shellRelations q n d) :=
  (shellRelations q n d).mkQ.comp (gradeProjection q n (d + 1))

theorem combinedProjection_ker (n d : ℕ) :
    (combinedProjection (S := S) q n d).ker = combinedRelations q n d := by
  rw [combinedProjection, LinearMap.ker_comp, Submodule.ker_mkQ, combinedRelations_comap]

theorem combinedProjection_surjective (n d : ℕ) :
    Function.Surjective (combinedProjection (S := S) q n d) :=
  (shellRelations q n d).mkQ_surjective.comp (gradeProjection_surjective q n (d + 1))

def combinedQuotientEquiv (n d : ℕ) :
    (ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1) ⧸ combinedRelations q n d) ≃ₗ[ℂ]
      (grade S q n (d + 1) ⧸ shellRelations q n d) :=
  (Submodule.quotEquivOfEq _ _ (combinedProjection_ker q n d).symm).trans
    ((combinedProjection q n d).quotKerEquivOfSurjective (combinedProjection_surjective q n d))

@[simp] theorem combinedQuotientEquiv_mk (n d : ℕ)
    (p : ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1)) :
    combinedQuotientEquiv q n d ((combinedRelations q n d).mkQ p) =
      (shellRelations q n d).mkQ (gradeProjection q n (d + 1) p) := rfl

def combinedCoefficientEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] (n d : ℕ) :
    ((ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1) ⧸ combinedRelations q n d) →ₗ[ℂ] W) ≃ₗ[ℂ]
      ((grade S q n (d + 1) ⧸ shellRelations q n d) →ₗ[ℂ] W) :=
  LinearEquiv.arrowCongr (combinedQuotientEquiv q n d) (LinearEquiv.refl ℂ W)

section Equivariant
variable [Fintype I] {H : Type*} [Group H]
  (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
  (hq : ∀ h, symbolMap (σ h) q = q)

omit [Fintype I] in
theorem gradeProjection_equivariant (n d : ℕ) (h : H)
    (p : ScalarJetAlgebra.grade (S := S) (I := I) n d) :
    gradeProjection q n d (DirectionalJetIBP.scalarAction σ ρ n d h p) =
      gradeAction q ρ σ hq n d h (gradeProjection q n d p) := by
  apply Subtype.ext
  simpa only [gradeProjection_apply, gradeAction_apply, DirectionalJetIBP.scalarAction_apply] using
    projection_action q ρ σ hq h p.val

theorem shell_stable (n d : ℕ) : ∀ h,
    shellRelations (S := S) q n d ≤ (shellRelations q n d).comap (gradeAction q ρ σ hq n (d + 1) h) := by
  simpa only [CovariantJetIBP.relations_eq] using
    CovariantJetIBP.stable (gradeDerivative (S := S) q n) σ (gradeAction q ρ σ hq n)
      (fun h i d => grade_covariance q ρ σ hq n h i d) d

def shellQuotientAction (n d : ℕ) :=
  (gradeAction q ρ σ hq n (d + 1)).quotient (shellRelations q n d) (shell_stable q ρ σ hq n d)

theorem combinedProjection_equivariant (n d : ℕ) (h : H)
    (p : ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1)) :
    combinedProjection q n d (DirectionalJetIBP.scalarAction σ ρ n (d + 1) h p) =
      shellQuotientAction q ρ σ hq n d h (combinedProjection q n d p) := by
  change (shellRelations q n d).mkQ
      (gradeProjection q n (d + 1) (DirectionalJetIBP.scalarAction σ ρ n (d + 1) h p)) =
    (shellRelations q n d).mkQ (gradeAction q ρ σ hq n (d + 1) h (gradeProjection q n (d + 1) p))
  rw [gradeProjection_equivariant q ρ σ hq]

include hq in
theorem combined_stable_action (n d : ℕ) : ∀ h,
    combinedRelations (S := S) q n d ≤
      (combinedRelations q n d).comap (DirectionalJetIBP.scalarAction σ ρ n (d + 1) h) := by
  intro h p hp
  rw [← combinedProjection_ker] at hp
  change combinedProjection q n d p = 0 at hp
  change DirectionalJetIBP.scalarAction σ ρ n (d + 1) h p ∈ combinedRelations q n d
  rw [← combinedProjection_ker]
  change combinedProjection q n d (DirectionalJetIBP.scalarAction σ ρ n (d + 1) h p) = 0
  rw [combinedProjection_equivariant q ρ σ hq, hp, map_zero]

def combinedAction (n d : ℕ) :=
  (DirectionalJetIBP.scalarAction σ ρ n (d + 1)).quotient (combinedRelations q n d)
    (combined_stable_action q ρ σ hq n d)

def combinedRepresentationEquiv (n d : ℕ) :
    Representation.Equiv (combinedAction q ρ σ hq n d) (shellQuotientAction q ρ σ hq n d) :=
  Representation.Equiv.mk (combinedQuotientEquiv q n d) (by
    intro h
    apply LinearMap.ext
    intro p
    obtain ⟨p, rfl⟩ := (combinedRelations (S := S) q n d).mkQ_surjective p
    change combinedQuotientEquiv q n d ((combinedRelations q n d).mkQ
        (DirectionalJetIBP.scalarAction σ ρ n (d + 1) h p)) =
      shellQuotientAction q ρ σ hq n d h
        (combinedQuotientEquiv q n d ((combinedRelations q n d).mkQ p))
    simp only [combinedQuotientEquiv_mk]
    exact combinedProjection_equivariant q ρ σ hq n d h p)

end Equivariant

end
end Math.JetEquation

import Math.RepresentationTheory.Characters.ResidualWeightCharacter

/-!
# Abelian recovery through actual joint eigenspaces

Nested torus/residual eigenspaces are linearly equivalent to full joint
eigenspaces. This compares characters coefficientwise, not just dimensions
of the complete representations.
-/

set_option autoImplicit false

namespace Math.ResidualAbelianRecovery

noncomputable section

open ResidualWeightSpace UnitaryCharacterProfile

variable {T H V W : Type*} [CommGroup T] [CommGroup H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def jointCharacter (chi : T →* Circle) (psi : H →* Circle) : (T × H) →* Circle :=
  chi.comp (MonoidHom.fst T H) * psi.comp (MonoidHom.snd T H)

def jointSpaceEquiv (rho : Representation ℂ (T × H) V)
    (chi : T →* Circle) (psi : H →* Circle) :
    UnitaryCharacterProfile.space (representation rho chi) psi ≃ₗ[ℂ]
      UnitaryCharacterProfile.space rho (jointCharacter chi psi) where
  toFun x := ⟨x.val.val, by
    intro g
    rw [product_on_weight rho chi g.1 g.2 x.val]
    have he := congrArg Subtype.val (x.property g.2)
    change residual rho g.2 x.val.val = (psi g.2 : ℂ) • x.val.val at he
    rw [he, smul_smul]
    rfl⟩
  invFun x := ⟨⟨x.val, by
    intro t
    simpa [jointCharacter, torus] using x.property (t, 1)⟩, by
    intro h
    apply Subtype.ext
    simpa [jointCharacter, ResidualWeightSpace.residual] using x.property (1, h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sector_unitary (rho : Representation ℂ (T × H) V)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho) (chi : T →* Circle) :
    UnitaryMultiplicity.IsUnitaryRepresentation (representation rho chi) := by
  intro h x y
  exact hu (1, h) x.val y.val

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

def circleCoefficients (rho : Representation ℂ H W)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho) : (H →* Circle) →₀ ℂ :=
  (profile rho hu).mapRange (fun n : ℕ => (n : ℂ)) (by simp)

theorem eval_circleCoefficients (rho : Representation ℂ H W)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho) (h : H) :
    ResidualWeightCharacter.eval (circleCoefficients rho hu) h = rho.character h := by
  unfold ResidualWeightCharacter.eval circleCoefficients
  rw [Finsupp.sum_mapRange_index]
  · exact UnitaryCharacterSpectrum.profile_eval rho hu h
  · simp

theorem joint_profile (rho : Representation ℂ (T × H) V)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (chi : T →* Circle) (psi : H →* Circle) :
    profile (representation rho chi) (sector_unitary rho hu chi) psi =
      profile rho hu (jointCharacter chi psi) := by
  simp only [profile_apply]
  exact (jointSpaceEquiv rho chi psi).finrank_eq

theorem index_eq_iff_joint_multiplicities (rho : Representation ℂ (T × H) V)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (target : Representation ℂ H W)
    (ht : UnitaryMultiplicity.IsUnitaryRepresentation target) (chi : T →* Circle) :
    (∀ h, ResidualWeightCharacter.index rho chi h = target.character h) ↔
      ∀ psi : H →* Circle,
        (profile rho hu (jointCharacter chi psi) : ℤ) -
          (profile rho hu (jointCharacter chi⁻¹ psi⁻¹) : ℤ) =
            (profile target ht psi : ℤ) := by
  let p := circleCoefficients (representation rho chi) (sector_unitary rho hu chi) -
    ResidualWeightCharacter.dual
      (circleCoefficients (representation rho chi⁻¹) (sector_unitary rho hu chi⁻¹))
  let q := circleCoefficients target ht
  have he (h : H) : ResidualWeightCharacter.eval p h =
      ResidualWeightCharacter.index rho chi h := by
    simp only [p, ResidualWeightCharacter.eval_sub, ResidualWeightCharacter.eval_dual,
      eval_circleCoefficients, ResidualWeightCharacter.index, Representation.char_dual]
  have hq (h : H) : ResidualWeightCharacter.eval q h = target.character h :=
    eval_circleCoefficients target ht h
  have hc (psi : H →* Circle) : p psi =
      (profile rho hu (jointCharacter chi psi) : ℂ) -
        (profile rho hu (jointCharacter chi⁻¹ psi⁻¹) : ℂ) := by
    simp only [p, Finsupp.sub_apply, ResidualWeightCharacter.dual_apply,
      circleCoefficients, Finsupp.mapRange_apply]
    rw [joint_profile rho hu chi psi, joint_profile rho hu chi⁻¹ psi⁻¹]
  constructor
  · intro h psi
    have hpq := ResidualWeightCharacter.eval_injective p q (fun x => by rw [he, hq, h])
    have hcoeff := congrArg (fun r : (H →* Circle) →₀ ℂ => r psi) hpq
    rw [hc] at hcoeff
    change (_ : ℂ) - _ = (profile target ht psi : ℂ) at hcoeff
    exact_mod_cast hcoeff
  · intro h x
    have hpq : p = q := by
      ext psi
      rw [hc]
      change (_ : ℂ) - _ = (profile target ht psi : ℂ)
      exact_mod_cast h psi
    rw [← he, hpq, hq]

end
end Math.ResidualAbelianRecovery

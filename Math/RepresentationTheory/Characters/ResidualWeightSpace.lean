import Math.RepresentationTheory.Characters.UnitaryCharacterSpectrum

/-!
# Residual representations on actual torus-weight spaces

Only T is assumed Abelian. H retains its full representation on each weight
space. Unitarity of the torus supplies a finite internal decomposition.
-/

set_option autoImplicit false

namespace Math.ResidualWeightSpace

noncomputable section

open scoped BigOperators

variable {T H E : Type*} [CommGroup T] [Group H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (rho : Representation ℂ (T × H) E)

def torus : Representation ℂ T E := rho.comp (MonoidHom.inl T H)
def residual : Representation ℂ H E := rho.comp (MonoidHom.inr T H)

abbrev space (chi : T →* Circle) : Submodule ℂ E :=
  UnitaryCharacterProfile.space (torus rho) chi

theorem actions_commute (t : T) (h : H) (v : E) :
    torus rho t (residual rho h v) = residual rho h (torus rho t v) := by
  change (rho (t, 1) * rho (1, h)) v = (rho (1, h) * rho (t, 1)) v
  rw [← map_mul, ← map_mul]
  simp

def sector (chi : T →* Circle) : Subrepresentation (residual rho) where
  toSubmodule := space rho chi
  apply_mem_toSubmodule h {v} hv t := by
    rw [actions_commute, hv t, map_smul]

abbrev representation (chi : T →* Circle) : Representation ℂ H (space rho chi) :=
  (sector rho chi).toRepresentation

@[simp] theorem representation_apply (chi : T →* Circle) (h : H) (v : space rho chi) :
    (representation rho chi h v).val = residual rho h v.val := rfl

theorem product_on_weight (chi : T →* Circle) (t : T) (h : H) (v : space rho chi) :
    rho (t, h) v.val = (chi t : ℂ) • residual rho h v.val := by
  have he : rho (t, h) v.val = torus rho t (residual rho h v.val) := by
    change rho (t, h) v.val = (rho (t, 1) * rho (1, h)) v.val
    rw [← map_mul]
    simp
  rw [he]
  exact (sector rho chi).apply_mem_toSubmodule h v.property t

theorem product_preserves_weight (chi : T →* Circle) (t : T) (h : H) :
    Set.MapsTo (rho (t, h)) (space rho chi) (space rho chi) := by
  intro v hv
  rw [product_on_weight rho chi t h ⟨v, hv⟩]
  exact (space rho chi).smul_mem _ ((sector rho chi).apply_mem_toSubmodule h hv)

theorem product_restrict (chi : T →* Circle) (t : T) (h : H) :
    (rho (t, h)).restrict (product_preserves_weight rho chi t h) =
      (chi t : ℂ) • representation rho chi h := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact product_on_weight rho chi t h v

variable [FiniteDimensional ℂ E]
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (torus rho))

/-- A residual character, not its dimension, is the coefficient at each weight. -/
theorem character_expansion (t : T) (h : H) :
    letI := UnitaryCharacterProfile.activeFintype (torus rho) hu
    rho.character (t, h) =
      ∑ chi : UnitaryCharacterProfile.Active (torus rho),
        (chi.val t : ℂ) * (representation rho chi.val).character h := by
  classical
  let := UnitaryCharacterProfile.activeFintype (torus rho) hu
  have hi : DirectSum.IsInternal
      (fun chi : UnitaryCharacterProfile.Active (torus rho) => space rho chi.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr (UnitaryCharacterProfile.internal (torus rho) hu)
  unfold Representation.character
  rw [LinearMap.trace_eq_sum_trace_restrict hi
    (fun chi => product_preserves_weight rho chi.val t h)]
  simp_rw [product_restrict, map_smul, smul_eq_mul]

end
end Math.ResidualWeightSpace

import TauCeti.RepresentationTheory.Compact.Intertwiner.Dimension
import TauCeti.RepresentationTheory.Continuous.Intertwining
import Math.RepresentationTheory.Unitary.ContinuousAction

/-!
# Compact character counting for algebraic intertwiners

The group is not assumed finite. Group-variable continuity is a separate
hypothesis: `ContRepresentation` alone only makes each operator continuous.
-/

namespace Math.CompactHomDimension

noncomputable section

open MeasureTheory Representation ContinuousRepresentationScope

variable {H V W : Type*} [Group H] [TopologicalSpace H]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/-- Finite-dimensional operators are continuous, independently of continuity
in the group variable. -/
def asContinuous (rho : Representation ℂ H V) : ContRepresentation ℂ H V where
  toMonoidHom :=
    { toFun := fun h => (rho h).toContinuousLinearMap
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp }

omit [TopologicalSpace H] in
@[simp] theorem asContinuous_toRepresentation (rho : Representation ℂ H V) :
    (asContinuous rho).toRepresentation = rho := by
  ext h v
  rfl

theorem continuous_asContinuous (rho : Representation ℂ H V)
    (hc : IsJointlyContinuous rho) : Continuous (asContinuous rho) := by
  apply continuous_clm_apply.mpr
  intro v
  exact hc.orbit v

variable [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- TauCeti's continuous Hom counting, expressed using the existing algebraic
character and intertwiner API. No unitary action is needed for this formula. -/
theorem integral_character_mul_eq_finrank
    (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    (∫ h, rho.character h⁻¹ * sigma.character h ∂TauCeti.haarProb H) =
      (Module.finrank ℂ (IntertwiningMap rho sigma) : ℂ) := by
  have hc := ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap
    (asContinuous rho) (asContinuous sigma)
    (continuous_asContinuous rho hr) (continuous_asContinuous sigma hs)
  rw [ContRepresentation.intertwiningMapEquiv.finrank_eq] at hc
  rw [asContinuous_toRepresentation rho, asContinuous_toRepresentation sigma] at hc
  simpa only [TauCeti.ContRepresentation.coe_character, asContinuous_toRepresentation] using hc

theorem integrable_character_mul
    (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    Integrable (fun h => rho.character h⁻¹ * sigma.character h) (TauCeti.haarProb H) := by
  have cr : Continuous rho.character :=
    (TauCeti.ContRepresentation.character (asContinuous rho)
      (continuous_asContinuous rho hr)).continuous
  have cs : Continuous sigma.character :=
    (TauCeti.ContRepresentation.character (asContinuous sigma)
      (continuous_asContinuous sigma hs)).continuous
  exact ((cr.comp continuous_inv).mul cs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable {R U : Type*}
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]

/-- The exact dimension identity consumed by the finite-group positive-quotient
argument, now for compact continuous representations. -/
theorem hom_finrank_add
    (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (tau : Representation ℂ H R) (upsilon : Representation ℂ H U)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (ht : IsJointlyContinuous tau) (hu : IsJointlyContinuous upsilon)
    (hc : ∀ h, rho.character h = sigma.character h + tau.character h) :
    Module.finrank ℂ (IntertwiningMap rho upsilon) =
      Module.finrank ℂ (IntertwiningMap sigma upsilon) +
        Module.finrank ℂ (IntertwiningMap tau upsilon) := by
  have he : (Module.finrank ℂ (IntertwiningMap rho upsilon) : ℂ) =
      (Module.finrank ℂ (IntertwiningMap sigma upsilon) : ℂ) +
        (Module.finrank ℂ (IntertwiningMap tau upsilon) : ℂ) := by
    rw [← integral_character_mul_eq_finrank rho upsilon hr hu,
      ← integral_character_mul_eq_finrank sigma upsilon hs hu,
      ← integral_character_mul_eq_finrank tau upsilon ht hu]
    simp_rw [hc, add_mul]
    exact integral_add (integrable_character_mul sigma upsilon hs hu)
      (integrable_character_mul tau upsilon ht hu)
  exact_mod_cast he

end
end Math.CompactHomDimension

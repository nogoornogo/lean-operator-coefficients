import Physics.StandardModel.Spectrum.NonabelianLightSource
import Math.RepresentationTheory.OrderedInvariantPairing

open Math

/-!
# Ordered nonzero residual coefficients on actual light SM fields

The qque order is Q,Q,u*,e*; the duql order is d*,u*,Q,L. Stars denote
contragredients of the left-chiral sectors. These are internal coefficient
theorems, not claims about Grassmann/Lorentz nonvanishing or interactions.
-/

set_option autoImplicit false

namespace GUT.NonabelianLightOperators

noncomputable section

open Representation NonabelianSMTarget NonabelianLightSource
open SU5.MaximalTorus StandardSMCharacterTarget
open StructuralConjugation InvariantWeylMass ResidualWeightSpace

variable {H G E : Type*} [Group H] [Fintype H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Fin 5 → Type*} [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  [∀ s, FiniteDimensional ℂ (F s)]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))
  (P : ∀ s, Representation ℂ H (F s))
  (ht : Matches B.radical.toRepresentation P) (c : ThreeConjugations j)

abbrev qqueRepresentation (q₁ q₂ u e : Fin 15) :=
  ((lightSector j rho B q₁).tprod (lightSector j rho B q₂)).tprod
    ((lightSector j rho B u).dual.tprod (lightSector j rho B e).dual)

abbrev duqlRepresentation (d u q l : Fin 15) :=
  ((lightSector j rho B d).dual.tprod (lightSector j rho B u).dual).tprod
    ((lightSector j rho B q).tprod (lightSector j rho B l))

include hu ht c in
-- Kernel checking involves nested actual radical/weight-space subtypes.
set_option maxHeartbeats 4000000 in
theorem exists_qque_coefficient [Nontrivial (F 0)]
    (q₁ q₂ u e : Fin 15) (hq₁ : species q₁ = 0) (hq₂ : species q₂ = 0)
    (hu' : species u = 1) (he : species e = 4) :
    ∃ f : IntertwiningMap (qqueRepresentation j rho B q₁ q₂ u e)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_ten_quotient (F := F) j rho B hu P ht c
  let : Nontrivial S.toSubmodule := hn
  obtain ⟨sq₁⟩ := hs q₁ (Or.inl hq₁)
  obtain ⟨sq₂⟩ := hs q₂ (Or.inl hq₂)
  obtain ⟨su⟩ := hs u (Or.inr (Or.inl hu'))
  obtain ⟨se⟩ := hs e (Or.inr (Or.inr he))
  exact OrderedInvariantPairing.exists_ordered_coefficient sq₁ su sq₂ se

include hu ht c in
set_option maxHeartbeats 12000000 in
theorem exists_duql_coefficient [Nontrivial (F 0)] [Nontrivial (F 2)]
    (d u q l : Fin 15) (hd : species d = 2) (hu' : species u = 1)
    (hq : species q = 0) (hl : species l = 3) :
    ∃ f : IntertwiningMap (duqlRepresentation j rho B d u q l)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_ten_quotient (F := F) j rho B hu P ht c
  obtain ⟨T, _, hm, ht'⟩ := common_barFive_quotient (F := F) j rho B hu P ht c
  let : Nontrivial S.toSubmodule := hn
  let : Nontrivial T.toSubmodule := hm
  obtain ⟨sq⟩ := hs q (Or.inl hq)
  obtain ⟨su⟩ := hs u (Or.inr (Or.inl hu'))
  obtain ⟨sd⟩ := ht' d (Or.inl hd)
  obtain ⟨sl⟩ := ht' l (Or.inr hl)
  exact OrderedInvariantPairing.exists_dual_first_coefficient sq su sl sd

theorem qque_slots_neutral :
    smReducedWeight 0 + smReducedWeight 3 - smReducedWeight 8 - smReducedWeight 14 = 0 := by
  decide

theorem duql_slots_neutral :
    -smReducedWeight 9 - smReducedWeight 8 + smReducedWeight 2 + smReducedWeight 13 = 0 := by
  decide

include hu ht c in
/-- Both ordered internal coefficient spaces are nonzero at explicitly
torus-neutral SM slots. The claim is about residual H invariance only. -/
theorem both_coefficients_exist [Nontrivial (F 0)] [Nontrivial (F 2)] :
    (∃ f : IntertwiningMap (qqueRepresentation j rho B 0 3 8 14)
      (Representation.trivial ℂ H ℂ), f ≠ 0) ∧
    (∃ f : IntertwiningMap (duqlRepresentation j rho B 9 8 2 13)
      (Representation.trivial ℂ H ℂ), f ≠ 0) := by
  constructor
  · exact exists_qque_coefficient j rho B hu P ht c 0 3 8 14 rfl rfl rfl rfl
  · exact exists_duql_coefficient j rho B hu P ht c 9 8 2 13 rfl rfl rfl rfl

/-- Complete exclusion at the level of the two residual internal coefficient
spaces. This is not a predicate on generated interactions or amplitudes. -/
def ForbidsBothInternalCoefficients : Prop :=
  (∀ f : IntertwiningMap (qqueRepresentation j rho B 0 3 8 14)
    (Representation.trivial ℂ H ℂ), f = 0) ∧
  (∀ f : IntertwiningMap (duqlRepresentation j rho B 9 8 2 13)
    (Representation.trivial ℂ H ℂ), f = 0)

include hu ht c in
theorem not_forbidsBothInternalCoefficients [Nontrivial (F 0)] :
    ¬ ForbidsBothInternalCoefficients j rho B := by
  intro h
  obtain ⟨f, hf⟩ := exists_qque_coefficient j rho B hu P ht c 0 3 8 14 rfl rfl rfl rfl
  exact hf (h.1 f)

end
end GUT.NonabelianLightOperators

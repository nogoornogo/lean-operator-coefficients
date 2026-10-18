import Physics.StandardModel.Spectrum.NonabelianSMTarget
import Physics.FieldTheory.Mass.ResidualLightQuotient

open Math

/-!
# Common constituents on actual light SM sectors

Ambient conjugation forces compatible positive target characters. Finite-group
semisimplicity then supplies matched split quotients of the mass radical.
-/

set_option autoImplicit false

namespace GUT.NonabelianLightSource

noncomputable section

open Representation NonabelianSMTarget ResidualWeightSpace
open SU5.MaximalTorus SU5.TorusCharacter StandardSMCharacterTarget
open StructuralConjugation InvariantWeylMass SplitRepresentationProjection

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

abbrev lightSector (i : Fin 15) :=
  representation B.radical.toRepresentation (weightCharacter (smReducedWeight i))

include hu ht c in
theorem common_ten_quotient [Nontrivial (F 0)] :
    ∃ S : Subrepresentation (P 0), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15,
        (species i = 0 ∨ species i = 1 ∨ species i = 4) →
          Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  obtain ⟨h01, h04, _⟩ := characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    ResidualLightQuotient.exists_common_quotient B.radical.toRepresentation (P 0)
  refine ⟨S, hi, hn, fun i h => hs _ ?_⟩
  intro x
  rw [ht i x]
  rcases h with h | h | h
  · rw [h]
  · rw [h, h01]
  · rw [h, h04]

include hu ht c in
theorem common_barFive_quotient [Nontrivial (F 2)] :
    ∃ S : Subrepresentation (P 2), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15,
        (species i = 2 ∨ species i = 3) →
          Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  obtain ⟨_, _, h23⟩ := characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    ResidualLightQuotient.exists_common_quotient B.radical.toRepresentation (P 2)
  refine ⟨S, hi, hn, fun i h => hs _ ?_⟩
  intro x
  rw [ht i x]
  rcases h with h | h
  · rw [h]
  · rw [h, h23]

end
end GUT.NonabelianLightSource

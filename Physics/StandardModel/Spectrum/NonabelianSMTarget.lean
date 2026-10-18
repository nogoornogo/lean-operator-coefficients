import Physics.FieldTheory.Mass.ResidualMassIndex
import Physics.StandardModel.Spectrum.ConjugationSource

open Math

/-!
# Local SM targets valued in actual residual representations

Fifteen oriented weights share five positive representation targets, one per
SM multiplet type. Equalities between different species are conclusions of
actual ambient conjugation, not target assumptions. Abelian recovery remains
a separate obligation.
-/

set_option autoImplicit false

namespace GUT.NonabelianSMTarget

noncomputable section

open SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge StandardSMCharacterTarget InvariantWeylMass
open ResidualWeightSpace ResidualWeightCharacter

/-- Species order: Q, up, down, lepton, electron. -/
def species : Fin 15 → Fin 5 :=
  ![0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4]

def torusPermutation (p : Equiv.Perm (Fin 5)) : Torus ≃* Torus where
  toFun := permute p
  invFun := permute p.symm
  left_inv t := by apply Subtype.ext; funext i; simp [permute, Function.comp_def]
  right_inv t := by apply Subtype.ext; funext i; simp [permute, Function.comp_def]
  map_mul' _ _ := rfl

theorem weightCharacter_comp (p : Equiv.Perm (Fin 5)) (w : ReducedWeight) :
    (weightCharacter w).comp (torusPermutation p).toMonoidHom =
      weightCharacter (permuteReducedWeight p w) := by
  apply MonoidHom.ext
  intro t
  exact (weightCharacter_permute p w t).symm

variable {H V : Type*} [Group H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {F : Fin 5 → Type*} [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]

/-- P consists of actual representations, not signed data. Finite dimensionality
is required by constituent extraction, not by this character identity.
No condition is imposed away from the fifteen monitored torus weights. -/
def Matches (light : Representation ℂ (Torus × H) V)
    (P : ∀ s, Representation ℂ H (F s)) : Prop :=
  ∀ (i : Fin 15) (h : H), index light (weightCharacter (smReducedWeight i)) h =
    (P (species i)).character h

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))

include hu in
theorem index_permute (p : Equiv.Perm (Fin 5)) (c : Realizes j p)
    (w : ReducedWeight) (h : H) :
    index B.radical.toRepresentation (weightCharacter (permuteReducedWeight p w)) h =
      index B.radical.toRepresentation (weightCharacter w) h := by
  have he := ResidualMassIndex.weight_index_invariant j rho B hu
    (torusPermutation p) c.element c.conjugate (weightCharacter w) h
  rwa [weightCharacter_comp] at he

include hu in
theorem target_character_eq (P : ∀ s, Representation ℂ H (F s))
    (ht : Matches B.radical.toRepresentation P)
    (i k : Fin 15) (p : Equiv.Perm (Fin 5)) (c : Realizes j p)
    (hw : permuteReducedWeight p (smReducedWeight i) = smReducedWeight k) :
    (P (species i)).character = (P (species k)).character := by
  funext h
  have he := index_permute j rho B hu p c (smReducedWeight i) h
  rw [hw] at he
  exact (ht i h).symm.trans (he.symm.trans (ht k h))

include hu in
theorem characters_compatible (P : ∀ s, Representation ℂ H (F s))
    (ht : Matches B.radical.toRepresentation P) (c : ThreeConjugations j) :
    (P 0).character = (P 1).character ∧
      (P 0).character = (P 4).character ∧ (P 2).character = (P 3).character := by
  refine ⟨?_, ?_, ?_⟩
  · apply target_character_eq j rho B hu P ht 0 8 _ c.quarkUp
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl]
    exact permuteReducedWeight_swap31_tenQ
  · apply target_character_eq j rho B hu P ht 0 14 _ c.quarkElectron
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl]
    exact permuteReducedWeight_swap04_tenQ
  · apply target_character_eq j rho B hu P ht 9 13 _ c.downLepton
    rw [(smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl,
      (smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl]
    exact permuteReducedWeight_swap03_barFiveDown

end
end GUT.NonabelianSMTarget

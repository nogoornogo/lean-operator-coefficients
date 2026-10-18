import GUT.SU5.Branching.TorusCharacter
import Math.RepresentationTheory.Characters.CharacterRestriction

open Math

/-!
# Weyl invariance from actual arbitrary SU(5) representations

A representation of SU(5) times H is a strict commuting residual action.
Conjugation by an actual SU(5) element, acting trivially on H, forces
invariance of every faithfully evaluated target. Only the target needs a
finite weight model; no source Laurent-polynomial certificate is assumed.
-/

set_option autoImplicit false

namespace GUT.SU5.TorusCharacterSource
open Math.SU5.MaximalTorus

noncomputable section

open StandardModelEmbedding MaximalTorus TorusCharacter StandardAbelianCharge
open FiniteAbelianChargeSectors

variable {H E : Type*} [CommGroup H] [AddCommGroup E] [Module ℂ E]

def inclusion : CombinedGroup H →* (TargetGroup × H) :=
  MaximalTorus.hom.prodMap (MonoidHom.id H)

def restrict (rho : Representation ℂ (TargetGroup × H) E) :
    Representation ℂ (CombinedGroup H) E := rho.comp inclusion

theorem inclusion_conjugate (p : Equiv.Perm (Fin 5)) (g : CombinedGroup H) :
    inclusion (permute p g.1, g.2) =
      (MonomialElements.signedPermutation p, 1) * inclusion g *
        (MonomialElements.signedPermutation p, 1)⁻¹ := by
  apply Prod.ext
  · exact hom_conjugate p g.1
  · simp [inclusion]

theorem character_invariant (rho : Representation ℂ (TargetGroup × H) E)
    (p : Equiv.Perm (Fin 5)) (g : CombinedGroup H) :
    (restrict rho).character (permute p g.1, g.2) = (restrict rho).character g :=
  CharacterRestriction.character_restriction_invariant rho inclusion
    (fun g => (permute p g.1, g.2)) (MonomialElements.signedPermutation p, 1)
    (inclusion_conjugate p) g

variable [FiniteDimensional ℂ E]

theorem dual_character_invariant (rho : Representation ℂ (TargetGroup × H) E)
    (p : Equiv.Perm (Fin 5)) (g : CombinedGroup H) :
    (restrict rho).dual.character (permute p g.1, g.2) = (restrict rho).dual.character g := by
  simp only [Representation.char_dual]
  exact character_invariant rho p g⁻¹

theorem target_invariant (rho : Representation ℂ (TargetGroup × H) E)
    (q : ResolvedCharacter (ChargeLabel H))
    (ht : ∀ g, (restrict rho).character g - (restrict rho).dual.character g = eval q g) :
    ResolvedWeylInvariant q := by
  intro p
  apply eval_injective
  intro g
  rw [eval_permute, ← ht, character_invariant, dual_character_invariant, ht]

end

end GUT.SU5.TorusCharacterSource

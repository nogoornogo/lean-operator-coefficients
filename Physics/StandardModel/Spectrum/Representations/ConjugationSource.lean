import Physics.StandardModel.Spectrum.Representations.TorusCharacter
import Physics.StandardModel.Spectrum.Charges.ProfileChiralIndex
import Math.RepresentationTheory.Characters.CharacterRestriction

open Math

/-! Three actual ambient conjugations suffice for the SM charge-profile
equalities. No SU(5) representation, full Weyl invariance, or profile equality
is an input. The determinant-one torus is a fixed weight-coordinate model. -/

set_option autoImplicit false

namespace Physics.StructuralConjugation

noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles

variable {G : Type*} [Group G]

/-- One ambient element works on the entire torus, not a pointwise choice. -/
structure Realizes (j : Torus →* G) (p : Equiv.Perm (Fin 5)) where
  element : G
  conjugate : ∀ t, j (permute p t) = element * j t * element⁻¹

/-- The two actual coordinate moves needed for the qque argument. -/
structure TwoConjugations (j : Torus →* G) where
  quarkUp : Realizes j (Equiv.swap (3 : Fin 5) 1)
  quarkElectron : Realizes j (Equiv.swap (0 : Fin 5) 4)

/-- Only the three coordinate moves used by the SM coefficient argument.
No multiplication relations between their representatives are required. -/
structure ThreeConjugations (j : Torus →* G) where
  quarkUp : Realizes j (Equiv.swap (3 : Fin 5) 1)
  quarkElectron : Realizes j (Equiv.swap (0 : Fin 5) 4)
  downLepton : Realizes j (Equiv.swap (0 : Fin 5) 3)

def ThreeConjugations.toTwo {j : Torus →* G} (c : ThreeConjugations j) :
    TwoConjugations j := ⟨c.quarkUp, c.quarkElectron⟩

/-- The Q/up swap also moves a different down weight to a lepton weight. -/
theorem swap31_down_lepton :
    permuteReducedWeight (Equiv.swap (3 : Fin 5) 1) (smReducedWeight 10) =
      smReducedWeight 13 := by
  decide

variable {H E : Type*} [CommGroup H] [AddCommGroup E] [Module ℂ E]

def inclusion (j : Torus →* G) : CombinedGroup H →* (G × H) :=
  j.prodMap (MonoidHom.id H)

def restrict (j : Torus →* G) (rho : Representation ℂ (G × H) E) :
    Representation ℂ (CombinedGroup H) E := rho.comp (inclusion j)

theorem inclusion_conjugate {j : Torus →* G} {p : Equiv.Perm (Fin 5)}
    (c : Realizes j p) (g : CombinedGroup H) :
    inclusion j (permute p g.1, g.2) =
      (c.element, 1) * inclusion j g * (c.element, 1)⁻¹ := by
  apply Prod.ext
  · exact c.conjugate g.1
  · simp [inclusion]

theorem character_invariant {j : Torus →* G} {p : Equiv.Perm (Fin 5)}
    (c : Realizes j p) (rho : Representation ℂ (G × H) E) (g : CombinedGroup H) :
    (restrict j rho).character (permute p g.1, g.2) = (restrict j rho).character g :=
  CharacterRestriction.character_restriction_invariant rho (inclusion j)
    (fun g => (permute p g.1, g.2)) (c.element, 1) (inclusion_conjugate c) g

variable [FiniteDimensional ℂ E]

theorem dual_character_invariant {j : Torus →* G} {p : Equiv.Perm (Fin 5)}
    (c : Realizes j p) (rho : Representation ℂ (G × H) E) (g : CombinedGroup H) :
    (restrict j rho).dual.character (permute p g.1, g.2) =
      (restrict j rho).dual.character g := by
  simp only [Representation.char_dual]
  exact character_invariant c rho g⁻¹

theorem target_invariant {j : Torus →* G} {p : Equiv.Perm (Fin 5)}
    (c : Realizes j p) (rho : Representation ℂ (G × H) E)
    (q : ResolvedCharacter (ChargeLabel H))
    (ht : ∀ g, (restrict j rho).character g - (restrict j rho).dual.character g =
      TorusCharacter.eval q g) :
    permuteResolved p q = q := by
  apply TorusCharacter.eval_injective
  intro g
  rw [TorusCharacter.eval_permute, ← ht, character_invariant c,
    dual_character_invariant c, ht]

/-- Coefficient equality needs only the one permutation being evaluated. -/
theorem coefficient_eq_of_invariant {A : Type*} (q : ResolvedCharacter A)
    (p : Equiv.Perm (Fin 5)) (hi : permuteResolved p q = q) (key : ResolvedKey A) :
    q (permuteKey p key) = q key := by
  have he := congrArg (fun f : ResolvedCharacter A => f (permuteKey p key)) hi
  simpa only [permuteResolved, Finsupp.mapDomain_apply_of_injective (permuteKey_injective p)] using he.symm

theorem profiles_equal_of_three_invariances {A : Type*} (q : ResolvedCharacter A)
    (hQU : permuteResolved (Equiv.swap (3 : Fin 5) 1) q = q)
    (hQE : permuteResolved (Equiv.swap (0 : Fin 5) 4) q = q)
    (hDL : permuteResolved (Equiv.swap (0 : Fin 5) 3) q = q) :
    quarkProfile q = upProfile q ∧ quarkProfile q = electronProfile q ∧
      downProfile q = leptonProfile q := by
  refine ⟨?_, ?_, ?_⟩
  · ext a
    exact (show q (reducedTenUp, a) = q (reducedTenQ, a) by
      simpa only [permuteKey, permuteReducedWeight_swap31_tenQ] using
        coefficient_eq_of_invariant q _ hQU (reducedTenQ, a)).symm
  · ext a
    exact (show q (reducedTenElectron, a) = q (reducedTenQ, a) by
      simpa only [permuteKey, permuteReducedWeight_swap04_tenQ] using
        coefficient_eq_of_invariant q _ hQE (reducedTenQ, a)).symm
  · ext a
    exact (show q (reducedBarFiveLepton, a) = q (reducedBarFiveDown, a) by
      simpa only [permuteKey, permuteReducedWeight_swap03_barFiveDown] using
        coefficient_eq_of_invariant q _ hDL (reducedBarFiveDown, a)).symm

theorem orbitCompatible_of_three_invariances {A : Type*} [AddCommGroup A]
    (P : Profiles A) (s : A →₀ ℤ)
    (hQU : permuteResolved (Equiv.swap (3 : Fin 5) 1)
      (chiralDifference (targetWithSinglets P s)) = chiralDifference (targetWithSinglets P s))
    (hQE : permuteResolved (Equiv.swap (0 : Fin 5) 4)
      (chiralDifference (targetWithSinglets P s)) = chiralDifference (targetWithSinglets P s))
    (hDL : permuteResolved (Equiv.swap (0 : Fin 5) 3)
      (chiralDifference (targetWithSinglets P s)) = chiralDifference (targetWithSinglets P s)) :
    OrbitCompatible P := by
  obtain ⟨hQ, he, hd⟩ := profiles_equal_of_three_invariances _ hQU hQE hDL
  have h0 := chiralDifference_target_profile P s 0
  have h8 := chiralDifference_target_profile P s 8
  have h9 := chiralDifference_target_profile P s 9
  have h13 := chiralDifference_target_profile P s 13
  have h14 := chiralDifference_target_profile P s 14
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at h0
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at h8
  rw [(smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] at h9
  rw [(smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] at h13
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at h14
  change chargeProfile _ reducedTenQ = chargeProfile _ reducedTenUp at hQ
  change chargeProfile _ reducedTenQ = chargeProfile _ reducedTenElectron at he
  change chargeProfile _ reducedBarFiveDown = chargeProfile _ reducedBarFiveLepton at hd
  rw [h0, h8] at hQ
  rw [h0, h14] at he
  rw [h9, h13] at hd
  exact ⟨integral_injective hQ, integral_injective he, integral_injective hd⟩

/-- Derive compatibility from an actual source dual trace; SC-2 supplies this
trace identity from an invariant mass and its light dual target. -/
theorem profiles_compatible {j : Torus →* G} (c : ThreeConjugations j)
    (rho : Representation ℂ (G × H) E) (P : Profiles (ChargeLabel H))
    (s : ChargeLabel H →₀ ℤ)
    (ht : ∀ g, (restrict j rho).character g - (restrict j rho).dual.character g =
      TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g) :
    OrbitCompatible P :=
  orbitCompatible_of_three_invariances P s
    (target_invariant c.quarkUp rho _ ht)
    (target_invariant c.quarkElectron rho _ ht)
    (target_invariant c.downLepton rho _ ht)

end
end Physics.StructuralConjugation

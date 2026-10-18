import Physics.StandardModel.Spectrum.RestrictedConjugationMassSource
import Math.RepresentationTheory.Characters.CoefficientTransport

open Math

/-! Actual radical dual-index invariance derived from ambient conjugation,
without requiring a global Laurent target or radical conjugation invariance. -/

set_option autoImplicit false

namespace GUT.ConjugationDualIndex

noncomputable section
open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open InvariantWeylMass StructuralConjugationMass

variable {H : Type*} [CommGroup H]

def coordinateEquiv (p : Equiv.Perm (Fin 5)) : CombinedGroup H ≃* CombinedGroup H where
  toFun g := (permute p g.1, g.2)
  invFun g := (permute p.symm g.1, g.2)
  left_inv g := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [permute, Function.comp_def]
    · rfl
  right_inv g := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [permute, Function.comp_def]
    · rfl
  map_mul' _ _ := rfl

theorem keyCharacter_permute (p : Equiv.Perm (Fin 5)) (key : ResolvedKey (ChargeLabel H)) :
    keyCharacter (permuteKey p key) = (keyCharacter key).comp (coordinateEquiv p).toMonoidHom := by
  ext g
  change (weightCharacter (permuteReducedWeight p key.1) g.1 : ℂ) * (key.2.toMul g.2 : ℂ) =
    (weightCharacter key.1 (permute p g.1) : ℂ) * (key.2.toMul g.2 : ℂ)
  rw [weightCharacter_permute]

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))

def dualIndex : ResolvedCharacter (ChargeLabel H) :=
  chiralDifference (RestrictedUnitary.spectrum j rho B hu)

theorem dualIndex_apply (key : ResolvedKey (ChargeLabel H)) :
    dualIndex j rho B hu key =
      (AbelianMassSpectrum.radicalSpectrum B hu -
        AbelianActualSpectrum.dual (AbelianMassSpectrum.radicalSpectrum B hu)) (keyCharacter key) := by
  simp only [dualIndex, chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    RestrictedUnitary.spectrum, Finsupp.comapDomain_apply, AbelianActualSpectrum.dual_apply,
    keyCharacter_neg]

theorem fullDual_eval (g : CombinedGroup H) :
    AbelianActualSpectrum.eval (AbelianMassSpectrum.radicalSpectrum B hu -
      AbelianActualSpectrum.dual (AbelianMassSpectrum.radicalSpectrum B hu)) g =
      (restrict j rho).character g - (restrict j rho).dual.character g := by
  rw [AbelianActualSpectrum.eval_sub, AbelianActualSpectrum.eval_dual,
    AbelianMassSpectrum.radicalSpectrum_eval, AbelianMassSpectrum.radicalSpectrum_eval,
    ← Representation.char_dual]
  exact B.radical_dual_character_eq g

theorem coeff_permute (p : Equiv.Perm (Fin 5)) (c : Realizes j p)
    (key : ResolvedKey (ChargeLabel H)) :
    dualIndex j rho B hu (permuteKey p key) = dualIndex j rho B hu key := by
  rw [dualIndex_apply, dualIndex_apply, keyCharacter_permute]
  apply AbelianActualSpectrum.coeff_comp_eq_of_eval_invariant
  intro g
  rw [fullDual_eval, fullDual_eval]
  change (restrict j rho).character (permute p g.1, g.2) -
    (restrict j rho).dual.character (permute p g.1, g.2) = _
  rw [character_invariant c, dual_character_invariant c]

end
end GUT.ConjugationDualIndex

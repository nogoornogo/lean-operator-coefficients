import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.FieldTheory.Mass.SelfDualMassIndex
import Math.RepresentationTheory.Characters.AbelianCharacterPolynomial

open Math

/-!
# Self-dual sources cannot realize a positive SM dual index

Residual charges are forgotten by summing coefficients, not by selecting
the neutral sector. A separated SM gauge weight retains the positive
generation total. Only the target needs a faithful weight evaluator.
-/

set_option autoImplicit false

namespace GUT.SelfDualChirality

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles InvariantWeylMass

def gaugeDualDifference (p : ReducedWeight →₀ ℤ) : ReducedWeight →₀ ℤ :=
  p - Finsupp.mapDomain Neg.neg p

theorem gaugeDualDifference_apply (p : ReducedWeight →₀ ℤ) (w : ReducedWeight) :
    gaugeDualDifference p w = p w - p (-w) := by
  have h := Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (Neg.neg : ReducedWeight → ReducedWeight)) p (-w)
  simpa [gaugeDualDifference] using congrArg (fun n : ℤ => p w - n) h

theorem forgetCharges_chiralDifference {A : Type*} [AddCommGroup A]
    (p : ResolvedCharacter A) :
    forgetCharges (chiralDifference p) = gaugeDualDifference (forgetCharges p) := by
  unfold forgetCharges chiralDifference dualCharacter gaugeDualDifference
  rw [Finsupp.mapDomain_sub, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

theorem unchargedTarget_apply_smWeight (N : ℕ) (i : Fin 15) :
    unchargedTarget N (smReducedWeight i) = (N : ℤ) := by
  classical
  have hi : Function.Injective smReducedWeight := by decide
  simp [unchargedTarget, Finset.sum_apply, Finsupp.single_apply, hi.eq_iff]

theorem unchargedTarget_apply_neg_smWeight (N : ℕ) (i : Fin 15) :
    unchargedTarget N (-smReducedWeight i) = 0 := by
  classical
  simp [unchargedTarget, Finset.sum_apply, smReducedWeight_ne_neg]

theorem forgotten_target_coefficient {A : Type*} [AddCommGroup A]
    (P : Profiles A) (N : ℕ) (hN : HasCommonTotal P N) (s : A →₀ ℤ) (i : Fin 15) :
    forgetCharges (chiralDifference (targetWithSinglets P s)) (smReducedWeight i) =
      (N : ℤ) := by
  rw [forgetCharges_chiralDifference, forgetCharges_targetWithSinglets hN,
    gaugeDualDifference_apply]
  simp [unchargedTarget_apply_smWeight, unchargedTarget_apply_neg_smWeight,
    smReducedWeight_nonzero, neg_ne_zero.mpr (smReducedWeight_nonzero i)]

theorem forgotten_target_ne_zero {A : Type*} [AddCommGroup A]
    (F : Family A) (s : A →₀ ℤ) :
    forgetCharges (chiralDifference (targetWithSinglets F.profiles s)) ≠ 0 := by
  intro he
  have hc := congrArg (fun p : ReducedWeight →₀ ℤ => p (smReducedWeight 0)) he
  rw [forgotten_target_coefficient F.profiles F.generations F.totals s] at hc
  exact F.generations_ne_zero (Int.ofNat_eq_zero.mp hc)

variable {T : Type*} [CommGroup T]

def evaluateGauge (weight : ReducedWeight → (T →* ℂ)) (p : ReducedWeight →₀ ℤ)
    (t : T) : ℂ := AbelianActualSpectrum.eval (Finsupp.mapDomain weight p) t

theorem evaluateGauge_eq_sum (weight : ReducedWeight → (T →* ℂ))
    (p : ReducedWeight →₀ ℤ) (t : T) :
    evaluateGauge weight p t = p.sum (fun w n => (n : ℂ) * weight w t) := by
  unfold evaluateGauge AbelianActualSpectrum.eval
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · intros; simp [add_mul]

theorem evaluateGauge_injective (weight : ReducedWeight → (T →* ℂ))
    (hw : Function.Injective weight) (p q : ReducedWeight →₀ ℤ)
    (he : ∀ t, evaluateGauge weight p t = evaluateGauge weight q t) : p = q := by
  have hh := AbelianActualSpectrum.eval_injective _ _ he
  ext w
  have h := congrArg (fun r : AbelianActualSpectrum.Polynomial T => r (weight w)) hh
  simpa only [Finsupp.mapDomain_apply_of_injective hw] using h

theorem evaluated_target_not_zero {A : Type*} [AddCommGroup A]
    (weight : ReducedWeight → (T →* ℂ)) (hw : Function.Injective weight)
    (F : Family A) (s : A →₀ ℤ) :
    ¬ ∀ t, evaluateGauge weight
      (forgetCharges (chiralDifference (targetWithSinglets F.profiles s))) t = 0 := by
  intro he
  apply forgotten_target_ne_zero F s
  apply evaluateGauge_injective weight hw
  intro t
  simpa [evaluateGauge] using he t

variable {K V A : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup A]

/-- The source equality may hold only on the tested gauge torus. -/
theorem not_has_target_of_zero_source (rho : Representation ℂ K V)
    (B : SymmetricMass rho) (test : T →* K)
    (weight : ReducedWeight → (T →* ℂ)) (hw : Function.Injective weight)
    (F : Family A) (s : A →₀ ℤ)
    (hsource : ∀ t, rho.character (test t) = rho.dual.character (test t)) :
    ¬ ∀ t, B.radical.toRepresentation.character (test t) -
      B.radical.toRepresentation.dual.character (test t) =
        evaluateGauge weight
          (forgetCharges (chiralDifference (targetWithSinglets F.profiles s))) t := by
  intro ht
  apply evaluated_target_not_zero weight hw F s
  intro t
  exact (ht t).symm.trans (B.radical_dual_character_zero_at (test t) (hsource t))

variable {G : Type*} [Group G]

theorem not_has_target_of_source_equiv (rho : Representation ℂ G V) (i : K →* G)
    (B : SymmetricMass (rho.comp i)) (test : T →* K)
    (weight : ReducedWeight → (T →* ℂ)) (hw : Function.Injective weight)
    (F : Family A) (s : A →₀ ℤ) (e : Representation.Equiv rho rho.dual) :
    ¬ ∀ t, B.radical.toRepresentation.character (test t) -
      B.radical.toRepresentation.dual.character (test t) =
        evaluateGauge weight
          (forgetCharges (chiralDifference (targetWithSinglets F.profiles s))) t :=
  not_has_target_of_zero_source (rho.comp i) B test weight hw F s
    (fun t => SelfDualCharacter.restrict_character_eq_dual_of_equiv rho i e (test t))

theorem not_has_target_of_inverse_conjugacy (rho : Representation ℂ G V) (i : K →* G)
    (B : SymmetricMass (rho.comp i)) (test : T →* K)
    (weight : ReducedWeight → (T →* ℂ)) (hw : Function.Injective weight)
    (F : Family A) (s : A →₀ ℤ)
    (hconj : ∀ t, ∃ n : G, i (test t⁻¹) = n * i (test t) * n⁻¹) :
    ¬ ∀ t, B.radical.toRepresentation.character (test t) -
      B.radical.toRepresentation.dual.character (test t) =
        evaluateGauge weight
          (forgetCharges (chiralDifference (targetWithSinglets F.profiles s))) t := by
  apply not_has_target_of_zero_source (rho.comp i) B test weight hw F s
  intro t
  have he := SelfDualCharacter.restrict_character_eq_dual_of_conjugate_inverse
    rho (i.comp test) hconj t
  simp only [Representation.char_dual] at he ⊢
  change rho.character (i (test t)) = rho.character (i (test t)⁻¹)
  simpa only [Representation.character, MonoidHom.comp_apply, map_inv] using he

end

end GUT.SelfDualChirality

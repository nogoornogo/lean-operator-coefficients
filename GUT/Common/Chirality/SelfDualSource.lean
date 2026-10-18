import GUT.Common.StandardChain.StandardChain
import Physics.StandardModel.Spectrum.SelfDualChirality

open Math

/-!
# Gauge self-duality excludes the standard-chain light target

Forgetting the residual group is exactly evaluation at its identity. This
adapter checks that the generic gauge evaluator is the existing physical
torus evaluator, rather than postulating a new light-target certificate.
-/

set_option autoImplicit false

namespace GUT.StandardChain.SelfDualSource

noncomputable section

open SU5 StandardModelEmbedding StandardAbelianCharge StandardSMCharacterTarget
open StandardWeylDualTarget FiniteChargeProfiles FiniteAbelianChargeSectors
open InvariantWeylMass

def gaugeWeight (w : ReducedWeight) : MaximalTorus.Torus →* ℂ :=
  Circle.coeHom.comp (TorusCharacter.weightCharacter w)

theorem gaugeWeight_injective : Function.Injective gaugeWeight := by
  intro w v he
  apply TorusCharacter.weightCharacter_injective
  ext z
  exact congrArg (fun chi : MaximalTorus.Torus →* ℂ => chi z) he

theorem evaluate_forgetCharges {H : Type*} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) (z : MaximalTorus.Torus) :
    SelfDualChirality.evaluateGauge gaugeWeight (forgetCharges p) z =
      TorusCharacter.eval p (z, 1) := by
  rw [SelfDualChirality.evaluateGauge_eq_sum]
  unfold forgetCharges
  rw [Finsupp.sum_mapDomain_index]
  · simp only [TorusCharacter.eval, TorusCharacter.keyCharacter_apply,
      map_one, Circle.coe_one, mul_one]
    rfl
  · simp
  · intros; simp [add_mul]

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E}

/-- The gauge restriction, with no residual character attached. -/
def gauge (rho : Representation ℂ (G × H) E) : Representation ℂ G E :=
  rho.comp (MonoidHom.inl G H)

theorem not_model_of_gauge_character (M : Model i rho)
    (hs : ∀ z : MaximalTorus.Torus,
      (gauge rho).character (i (MaximalTorus.hom z)) =
        (gauge rho).dual.character (i (MaximalTorus.hom z))) : False := by
  apply SelfDualChirality.evaluated_target_not_zero gaugeWeight gaugeWeight_injective
    M.profile M.singlets
  intro z
  rw [evaluate_forgetCharges, ← M.lightTarget (z, 1)]
  apply M.mass.radical_dual_character_zero_at
  have he := hs z
  simp only [Representation.char_dual] at he ⊢
  simpa [Representation.character, gauge, torusInclusion, MonoidHom.prodMap] using he

theorem not_model_of_gauge_selfDual (M : Model i rho)
    (e : Representation.Equiv (gauge rho) (gauge rho).dual) : False :=
  not_model_of_gauge_character M (fun z =>
    congrFun (Representation.char_iso e) (i (MaximalTorus.hom z)))

theorem not_model_of_inverse_conjugacy (M : Model i rho)
    (hc : ∀ z : MaximalTorus.Torus, ∃ n : G,
      i (MaximalTorus.hom z⁻¹) = n * i (MaximalTorus.hom z) * n⁻¹) : False := by
  apply not_model_of_gauge_character M
  intro z
  have he := SelfDualCharacter.restrict_character_eq_dual_of_conjugate_inverse
    (gauge rho) (i.comp MaximalTorus.hom) hc z
  simp only [Representation.char_dual] at he ⊢
  simpa only [Representation.character, MonoidHom.comp_apply, map_inv] using he

end

end GUT.StandardChain.SelfDualSource

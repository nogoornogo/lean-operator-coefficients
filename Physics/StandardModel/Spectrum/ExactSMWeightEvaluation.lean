import Physics.StandardModel.Spectrum.ExactSMWeightMultiplicity

open Math

/-! Evaluation on a gauge weight vector identifies the actual residual
multiplicity representation with a light torus sector, not just its dimension. -/

namespace GUT.ExactSMWeightEvaluation
noncomputable section
open scoped TensorProduct
open Representation StandardSMGaugeTensor SMEpsilonTensor ProductFactorization
open InvariantWeylMass ResidualWeightSpace SU5 SU5.TorusCharacter
open StandardSMCharacterTarget ExactSMWeightMultiplicity

variable {H G E U : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (j : MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (r : Representation ℂ GaugeGroup U) (i : Fin 15) (v : U)
  (hv : ∀ z : PhysicalTorus.Coordinates, r (PhysicalTorus.gaugePoint z) v =
    (weightCharacter (smReducedWeight i) (PhysicalTorus.toTorus z) : ℂ) • v)

def evaluation : IntertwiningMap (multiplicityRepresentation D.action r)
    (representation B.radical.toRepresentation (weightCharacter (smReducedWeight i))) where
  toLinearMap :=
    { toFun := fun f => ⟨f v, by
        intro t
        obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
        have ha := DFunLike.congr_fun D.restriction (z, (1 : H))
        change D.action (PhysicalTorus.gaugePoint z, 1) =
          B.radical.toRepresentation (PhysicalTorus.toTorus z, 1) at ha
        change B.radical.toRepresentation (PhysicalTorus.toTorus z, 1) (f v) = _
        rw [← ha]
        have hf := LinearMap.congr_fun (f.isIntertwining' (PhysicalTorus.gaugePoint z)) v
        change f (r _ v) = D.action (_, 1) (f v) at hf
        rw [← hf, hv, map_smul]⟩
      map_add' _ _ := by apply Subtype.ext; rfl
      map_smul' _ _ := by apply Subtype.ext; rfl }
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change D.action (1, h) (f v) = B.radical.toRepresentation (1, h) (f v)
    rw [LightSMAction.residual_agrees j rho B D]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ U] in
theorem evaluation_injective [IsIrreducible r] (hn : v ≠ 0) :
    Function.Injective (evaluation j rho B D r i v hv) := by
  intro f g h
  exact multiplicityEvaluationAt_injective D.action r hn (congrArg Subtype.val h)

def evaluationEquiv [IsIrreducible r] (hn : v ≠ 0)
    (hd : Module.finrank ℂ (MultiplicitySpace D.action r) =
      Module.finrank ℂ (space B.radical.toRepresentation (weightCharacter (smReducedWeight i)))) :
    Representation.Equiv (multiplicityRepresentation D.action r)
      (representation B.radical.toRepresentation (weightCharacter (smReducedWeight i))) :=
  (evaluation j rho B D r i v hv).ofBijective
    ⟨evaluation_injective j rho B D r i v hv hn,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
        (evaluation_injective j rho B D r i v hv hn)⟩

end
end GUT.ExactSMWeightEvaluation

import Physics.StandardModel.Spectrum.ExactSMWeightEvaluation
import Physics.StandardModel.Spectrum.MonitoredSMWeights

open Math

/-! The four residual weight-index equations follow from the SM-only exact
spectrum. No residual generation representation is supplied by the caller. -/

namespace GUT.ExactSMFourWeightTarget
noncomputable section
open scoped TensorProduct
open Representation ProductFactorization StandardSMGaugeTensor SMEpsilonTensor
open InvariantWeylMass ResidualWeightSpace ResidualWeightCharacter
open SU5 SU5.TorusCharacter StandardSMCharacterTarget
open ExactSMResidualSpectrum ExactSMWeightMultiplicity ExactSMWeightEvaluation

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))

include hu in
theorem index_eq_multiplicity {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s)
    {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (r : Representation ℂ GaugeGroup U) [IsIrreducible r] (i : Fin 15)
    (v : U) (hn : v ≠ 0)
    (hv : ∀ z : PhysicalTorus.Coordinates, r (PhysicalTorus.gaugePoint z) v =
      (weightCharacter (smReducedWeight i) (PhysicalTorus.toTorus z) : ℂ) • v)
    (hr : Module.finrank ℂ (MultiplicitySpace D.action r) = n) (h : H) :
    index B.radical.toRepresentation (weightCharacter (smReducedWeight i)) h =
      (multiplicityRepresentation D.action r).character h := by
  let e := evaluationEquiv j rho B D r i v hv hn
    (hr.trans (weight_finrank j rho B D hu hs i).symm)
  let : Subsingleton (space B.radical.toRepresentation (weightCharacter (smReducedWeight i))⁻¹) :=
    Module.finrank_zero_iff.mp (opposite_weight_finrank j rho B D hu hs i)
  have hz : (representation B.radical.toRepresentation
      (weightCharacter (smReducedWeight i))⁻¹).dual h = 0 := Subsingleton.elim _ _
  rw [index, ← char_iso e]
  simp [Representation.character, hz]

include hu in
theorem has_target {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) :
    FourWeightLightQque.HasTarget j rho B (target D.action) := by
  let : IsIrreducible quark := StandardSMIrreducibility.quark_irreducible
  let : IsIrreducible upRight.dual := StandardSMIrreducibility.upLeft_irreducible
  let : IsIrreducible electronRight.dual := StandardSMIrreducibility.electronLeft_irreducible
  obtain ⟨hq, hup, he⟩ := ExactSMSpectrum.exact_species_multiplicities hs
  intro i hi h
  rcases hi with rfl | rfl | rfl | rfl
  · exact index_eq_multiplicity j rho B D hu hs quark 0
      (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) (MonitoredSMWeights.quark_vector_nonzero 0 0)
      MonitoredSMWeights.quark_zero hq h
  · exact index_eq_multiplicity j rho B D hu hs quark 3
      (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) (MonitoredSMWeights.quark_vector_nonzero 1 1)
      MonitoredSMWeights.quark_three hq h
  · exact index_eq_multiplicity j rho B D hu hs upRight.dual 8
      (LinearMap.proj (2 : Fin 3)) MonitoredSMWeights.up_vector_nonzero
      MonitoredSMWeights.up_eight hup h
  · exact index_eq_multiplicity j rho B D hu hs electronRight.dual 14
      LinearMap.id MonitoredSMWeights.electron_vector_nonzero
      MonitoredSMWeights.electron_fourteen he h

end
end GUT.ExactSMFourWeightTarget

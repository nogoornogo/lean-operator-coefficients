import GUT.SU5.SelectionRules.GeorgiGlashowQque
import Physics.StandardModel.Operators.BaryonOne.Qque.VectorlikeSpectrumQque
import Math.LinearAlgebra.Constructions.FiniteBasisHilbertization
import Math.RepresentationTheory.Unitary.ContinuousRepresentationTransport

open Physics

open Math

/-! Retained SU(5) matter plus a full matter/dual-matter pair, all light.
This checks a nonzero-extra source, not a vacuum or Yukawa construction. -/

namespace GUT.SU5.VectorlikeBenchmark
open Physics.SU5
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open ProductFactorization SplitRepresentationProjection
open StandardModelEmbedding

abbrev Original := MatterSource.Space 1
abbrev Raw := Original × (Original × Module.Dual ℂ Original)
abbrev Space := FiniteBasisHilbertization.Copy (Module.finBasis ℂ Raw)
def forget : Space ≃ₗ[ℂ] Raw := FiniteBasisHilbertization.Copy.valLinearEquiv _

def residual := GeorgiGlashowBenchmark.trivialAction 1
def original := GeorgiGlashowSource.joint residual
def rawAction := original.prod (original.prod original.dual)

def joint : Representation ℂ (TargetGroup × PUnit) Space where
  toFun g := forget.symm.conj (rawAction g)
  map_one' := by
    rw [map_one]
    exact forget.symm.conjRingEquiv.map_one
  map_mul' g h := by
    rw [map_mul]
    exact forget.symm.conjRingEquiv.map_mul _ _

def jointEquiv : Representation.Equiv joint rawAction :=
  .mk forget (by intro g; ext v <;> rfl)

def mass := SymmetricMass.zero (joint.comp (MaximalTorus.hom.prodMap (MonoidHom.id PUnit)))
def smAction := joint.comp (hom.prodMap (MonoidHom.id PUnit))

theorem sm_restriction :
    smAction.comp (PhysicalTorus.gaugeHom.prodMap (MonoidHom.id PUnit)) =
      (joint.comp (MaximalTorus.hom.prodMap (MonoidHom.id PUnit))).comp
        (PhysicalTorus.toTorus.prodMap (MonoidHom.id PUnit)) := by
  ext g v
  change joint (hom (PhysicalTorus.gaugePoint g.1), g.2) v = _
  rw [PhysicalTorus.hom_gaugePoint]
  rfl

def compatible : LightSMAction.Compatible MaximalTorus.hom joint mass :=
  LightSMAction.ofInvariantMass _ _ _ smAction (by intros; rfl) sm_restriction

def radicalEquiv : Representation.Equiv compatible.action smAction :=
  .mk (SymmetricMass.zeroRadicalEquiv
    (joint.comp (MaximalTorus.hom.prodMap (MonoidHom.id PUnit)))).toLinearEquiv
    (by intro g; rfl)

abbrev reference := GeorgiGlashowSource.compatible residual

def rawSMEquiv : Representation.Equiv
    (rawAction.comp (hom.prodMap (MonoidHom.id PUnit)))
    ((GeorgiGlashowSource.smAction residual).prod
      ((GeorgiGlashowSource.smAction residual).prod (GeorgiGlashowSource.smAction residual).dual)) := by
  change Representation.Equiv
    (Representation.prod (original.comp (hom.prodMap (MonoidHom.id PUnit)))
      (Representation.prod (original.comp (hom.prodMap (MonoidHom.id PUnit)))
        (original.dual.comp (hom.prodMap (MonoidHom.id PUnit))))) _
  rw [dual_comp]
  exact Representation.Equiv.refl _

def decomposition : Representation.Equiv compatible.action
    (reference.action.prod (reference.action.prod reference.action.dual)) :=
  radicalEquiv.trans
    ((restrictEquiv jointEquiv (hom.prodMap (MonoidHom.id PUnit))).trans
      (rawSMEquiv.trans (prodEquiv (GeorgiGlashowSource.radicalEquiv residual).symm
        (prodEquiv (GeorgiGlashowSource.radicalEquiv residual).symm
          (dualEquiv (GeorgiGlashowSource.radicalEquiv residual).symm)))))

private theorem prod_continuous {G V W : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (a : Representation ℂ G V) (b : Representation ℂ G W)
    (ha : IsJointlyContinuous a) (hb : IsJointlyContinuous b) :
    IsJointlyContinuous (a.prod b) :=
  (Continuous.comp ha (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (Continuous.comp hb (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem joint_continuous : IsJointlyContinuous joint := by
  let := ContinuousDual.dualNormedAddCommGroup (V := Original)
  let := ContinuousDual.dualNormedSpace (V := Original)
  have ho : IsJointlyContinuous original := GeorgiGlashowSource.joint_continuous residual
    (GeorgiGlashowBenchmark.trivialAction_continuous 1)
  have hd := ContinuousDual.jointlyContinuous_dual original ho
  have hr := prod_continuous original (original.prod original.dual) ho
    (prod_continuous original original.dual ho hd)
  exact ContinuousRepresentationTransport.continuous_conjugate forget rawAction hr

theorem compatible_continuous : IsJointlyContinuous compatible.action := by
  apply LightSMAction.ofInvariantMass_continuous
  exact joint_continuous.comp (StandardModelEmbedding.continuousHom.prodMap
    (ContinuousMonoidHom.id PUnit))

theorem reference_continuous : IsJointlyContinuous reference.action :=
  GeorgiGlashowSource.compatible_continuous residual
    (GeorgiGlashowBenchmark.trivialAction_continuous 1)

def extension := VectorlikeSpectrumQque.extension MaximalTorus.hom joint mass compatible
  MaximalTorus.hom (GeorgiGlashowSource.joint residual) (GeorgiGlashowSource.mass residual)
  reference reference.action decomposition reference_continuous

theorem quark_extra_positive : 0 < extension.quark.dimension := by
  change 0 < Module.finrank ℂ (MultiplicitySpace
    (reference.action.prod reference.action.dual) StandardSMGaugeTensor.quark)
  have he := (MultiplicityTransport.prod reference.action reference.action.dual
    StandardSMGaugeTensor.quark).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at he
  have hq := (ExactSMResidualSpectrum.target_finrank reference.action
    (GeorgiGlashowSource.hasSpectrum residual)).1
  change Module.finrank ℂ (MultiplicitySpace reference.action StandardSMGaugeTensor.quark) = 1 at hq
  omega

theorem not_exact (n s : ℕ) :
    ¬ ExactSMSpectrum.HasSpectrum (firstRestriction compatible.action) n s :=
  BalancedSpeciesExtension.not_exact_of_quark_extra _ _ _ _ _ _ _ _
    extension quark_extra_positive n s

theorem exists_actual_exterior :
    LightSMSpeciesQque.HasActualExterior MaximalTorus.hom joint mass compatible :=
  VectorlikeSpectrumQque.exists_actual_exterior _ _ _ _ _ _ _ _ reference.action
    decomposition compatible_continuous reference_continuous
    (GeorgiGlashowSource.hasSpectrum residual) (by decide)
    (GeorgiGlashowSource.torus_unitary residual)
    (StandardChainConjugation.threeConjugations (MonoidHom.id TargetGroup)).toTwo

theorem shared_positive : SharedPositiveSpeciesIndex.SharedPositive
    (AutomaticSMSpeciesIndex.coefficients MaximalTorus.hom joint mass compatible
      compatible_continuous) :=
  VectorlikeSpectrumQque.shared_positive _ _ _ _ _ _ _ _ reference.action
    decomposition compatible_continuous reference_continuous
    (GeorgiGlashowSource.hasSpectrum residual) (by decide)
    (GeorgiGlashowSource.torus_unitary residual)
    (StandardChainConjugation.threeConjugations (MonoidHom.id TargetGroup)).toTwo

end
end GUT.SU5.VectorlikeBenchmark

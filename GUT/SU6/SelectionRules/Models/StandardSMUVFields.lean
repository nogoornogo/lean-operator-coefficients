import GUT.SU6.Adapters.StandardSMExterior
import GUT.SU6.Branching.StandardSMTorus

open Math

/-!
# Full-gauge branching of actual SU(6) 15 + 2 bar6 fields

The source is a direct product of the checked analytic SU(6) spaces.
This explicit realization is not definitionally the charge-sector/list
realization used by `ordinaryFields`.
-/

set_option autoImplicit false

namespace GUT.StandardSMUVFields

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor StandardSMFullGaugeMass
open SplitRepresentationProjection

abbrev UV := (ConcreteSU6Representations.exteriorTwo.V ×
  ConcreteSU6Representations.antifundamental.V) × ConcreteSU6Representations.antifundamental.V

def uvRho : Representation ℂ ActualRestriction.SU6 UV :=
  (ConcreteSU6Representations.exteriorTwo.rho.prod
    ConcreteSU6Representations.antifundamental.rho).prod ConcreteSU6Representations.antifundamental.rho

theorem uv_jointlyContinuous : ContinuousRepresentationScope.IsJointlyContinuous uvRho := by
  have he : Continuous (fun p : ActualRestriction.SU6 × ConcreteSU6Representations.exteriorTwo.V =>
      ConcreteSU6Representations.exteriorTwo.rho p.1 p.2) :=
    ConcreteSU6Representations.exteriorTwo.continuous_action
  have hb : Continuous (fun p : ActualRestriction.SU6 × ConcreteSU6Representations.antifundamental.V =>
      ConcreteSU6Representations.antifundamental.rho p.1 p.2) :=
    ConcreteSU6Representations.antifundamental.continuous_action
  change Continuous (fun p : ActualRestriction.SU6 × UV =>
    ((ConcreteSU6Representations.exteriorTwo.rho p.1 p.2.1.1,
      ConcreteSU6Representations.antifundamental.rho p.1 p.2.1.2),
      ConcreteSU6Representations.antifundamental.rho p.1 p.2.2))
  have h1 := he.comp (show Continuous (fun p : ActualRestriction.SU6 × UV =>
    (p.1, p.2.1.1)) from continuous_fst.prodMk continuous_snd.fst.fst)
  have h2 := hb.comp (show Continuous (fun p : ActualRestriction.SU6 × UV =>
    (p.1, p.2.1.2)) from continuous_fst.prodMk continuous_snd.fst.snd)
  have h3 := hb.comp (show Continuous (fun p : ActualRestriction.SU6 × UV =>
    (p.1, p.2.2)) from continuous_fst.prodMk continuous_snd.snd)
  exact (h1.prodMk h2).prodMk h3

def light : Representation ℂ GaugeGroup Light :=
  quark.prod (upRight.dual.prod (downRight.dual.prod (lepton.prod electronRight.dual)))

def decomposed : Representation ℂ GaugeGroup Fields :=
  SplitWeylMass.representation light StandardSMGroup.heavy

abbrev First := StandardSMExterior.Blocks ×
  (Module.Dual ℂ Color × (Weak × Module.Dual ℂ ℂ))

def singletEquiv : Module.Dual ℂ ℂ ≃ₗ[ℂ] ℂ := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ

def reorder : First ≃ₗ[ℂ] (Light × Heavy) where
  toFun x := ((x.1.2.1, (x.1.1, (x.2.1, (x.2.2.1, x.1.2.2.1)))),
    (x.1.2.2.2.1, (x.1.2.2.2.2, singletEquiv x.2.2.2)))
  invFun y := ((y.1.2.1, (y.1.1, (y.1.2.2.2.2, (y.2.1, y.2.2.1)))),
    (y.1.2.2.1, (y.1.2.2.2.1, singletEquiv.symm y.2.2.2)))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

def reorderEquiv : Representation.Equiv
    (StandardSMExterior.blocksRho.prod StandardSMContragredient.antifundamentalSM)
    (light.prod StandardSMGroup.heavy) where
  toLinearEquiv := reorder
  isIntertwining' g := by
    apply LinearMap.ext; intro x
    rfl

def gaugeEquiv : Representation.Equiv (uvRho.comp StandardSMGroup.hom) decomposed :=
  prodEquiv
    ((prodEquiv StandardSMExterior.analyticEquiv
      StandardSMContragredient.antifundamentalEquiv).trans reorderEquiv)
    StandardSMGroup.analyticAntifundamentalEquiv

/-- Named coordinate formula avoids unfolding the entire representation
transport when checking a selected light vector. -/
theorem gaugeEquiv_apply (x : UV) :
    gaugeEquiv x =
      (reorder (StandardSMExterior.analyticEquiv x.1.1,
        StandardSMContragredient.antifundamentalEquiv x.1.2),
        StandardSMGroup.analyticAntifundamentalEquiv x.2) := by
  let first := prodEquiv StandardSMExterior.analyticEquiv
    StandardSMContragredient.antifundamentalEquiv
  have hfirst := prodEquiv_apply StandardSMExterior.analyticEquiv
    StandardSMContragredient.antifundamentalEquiv x.1
  have houter := prodEquiv_apply (first.trans reorderEquiv)
    StandardSMGroup.analyticAntifundamentalEquiv x
  exact houter.trans (congrArg (fun y => (y, StandardSMGroup.analyticAntifundamentalEquiv x.2))
    (congrArg reorder hfirst))

def neutralCharges (H : Type*) [CommGroup H] :
    StandardBranchProtonObstruction.Charges (FiniteAbelianChargeSectors.ChargeLabel H) :=
  ⟨0, 0, 0, 0, 0⟩

theorem neutral_rho_eq (H : Type*) [CommGroup H] :
    StandardSMFullGaugeMass.rho (neutralCharges H) =
      decomposed.comp (MonoidHom.fst GaugeGroup H) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext; intro x
  simp [StandardSMFullGaugeMass.rho, SplitWeylMass.representation, decomposed,
    lightRho, quarkRho, upRho, downRho, leptonRho, electronRho, heavyRho,
    light, StandardSMGroup.heavy, neutralCharges, StandardSMResidualTensor.charged,
    Representation.dual]

def withResidualEquiv (H : Type*) [CommGroup H] : Representation.Equiv
    (uvRho.comp (StandardSMGroup.withResidual H))
    (StandardSMFullGaugeMass.rho (neutralCharges H)) where
  toLinearEquiv := gaugeEquiv.toLinearEquiv
  isIntertwining' g := by
    rw [neutral_rho_eq]
    exact (restrictEquiv gaugeEquiv (MonoidHom.fst GaugeGroup H)).isIntertwining' g

theorem withResidualEquiv_apply (H : Type*) [CommGroup H] (x : UV) :
    withResidualEquiv H x = gaugeEquiv x := rfl

theorem uv_finrank : Module.finrank ℂ UV = 27 := by
  rw [gaugeEquiv.toLinearEquiv.finrank_eq]
  exact fields_finrank

theorem physicalRestriction_eq (H : Type*) [CommGroup H] :
    (uvRho.comp (StandardSMGroup.withResidual H)).comp
        (StandardSMTorus.hom.prodMap (MonoidHom.id H)) =
      uvRho.comp ((PhysicalSMTorusTarget.embedding (-2) 3).comp
        (MonoidHom.fst PhysicalSMTorusTarget.Group H)) := by
  change uvRho.comp ((StandardSMGroup.withResidual H).comp
    (StandardSMTorus.hom.prodMap (MonoidHom.id H))) = _
  rw [StandardSMTorus.withResidual_comp]

end

end GUT.StandardSMUVFields

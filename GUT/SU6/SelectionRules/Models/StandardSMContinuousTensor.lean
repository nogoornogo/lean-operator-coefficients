import GUT.SU6.SelectionRules.Models.StandardSMOrdinaryMass
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

open Physics

open Math

/-! Full-gauge action and ordered internal tensors on the actual radical
of the continuous Weyl model, transported from the analytic UV benchmark.
The original physical-torus action is retained by a proved equality. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace GUT.StandardSMContinuousTensor

noncomputable section

open StandardSMOrdinaryMass StandardSMOrdinaryFields
open StandardSMGaugeTensor (GaugeGroup)
open SplitRepresentationProjection
open scoped TensorProduct

-- Tensor type comparisons do not need to unfold the underlying charge-sector list.
attribute [local irreducible] ConcreteWeylBenchmark.matter

variable (H : Type*) [CommGroup H]

local instance fullGroupMonoid : Monoid (GaugeGroup × H) :=
  (inferInstance : Group (GaugeGroup × H)).toMonoid

local instance physicalGroupMonoid : Monoid (StandardSMCharacterTarget.CombinedGroup H) :=
  (inferInstance : Group (StandardSMCharacterTarget.CombinedGroup H)).toMonoid

abbrev ZeroModes := (continuousModel H).mass.radical.toSubmodule

def physicalEquiv :=
  (RepresentationConjugation.sealEquiv (ContinuousWeylMassTransport.radicalEquiv (model H))).val

theorem physicalEquiv_eq : physicalEquiv H = ContinuousWeylMassTransport.radicalEquiv (model H) :=
  (RepresentationConjugation.sealEquiv (ContinuousWeylMassTransport.radicalEquiv (model H))).property

def physicalFullEquiv := (physicalEquiv H).trans
  (EquivariantWeylMassTransport.restrictToRadicalEquiv (fullMass H) (torusHom H)
    (StandardWeylMassSource.ordinaryFields (ConcreteWeylBenchmark.matter H)).rho
    (gauge_restriction H))

def fullRho := RepresentationConjugation.pullback (physicalFullEquiv H).toLinearEquiv (fullZeroRho H)

def fullEquiv := RepresentationConjugation.equiv (physicalFullEquiv H).toLinearEquiv (fullZeroRho H)

theorem physical_restriction :
    (fullRho H).comp (torusHom H) = (continuousModel H).mass.radical.toRepresentation :=
  RepresentationConjugation.restriction_of_eq (physicalFullEquiv H) (fullZeroRho H)
    (torusHom H) rfl

def uvEquiv : Representation.Equiv (fullRho H) (StandardSMUVMass.zeroRho H) :=
  (fullEquiv H).trans (StandardSMOrdinaryMass.radicalEquiv H)

abbrev QQueSpace := (ZeroModes H ⊗[ℂ] ZeroModes H) ⊗[ℂ]
  (Module.Dual ℂ (ZeroModes H) ⊗[ℂ] Module.Dual ℂ (ZeroModes H))

abbrev DuqlSpace := (Module.Dual ℂ (ZeroModes H) ⊗[ℂ] Module.Dual ℂ (ZeroModes H)) ⊗[ℂ]
  (ZeroModes H ⊗[ℂ] ZeroModes H)

def qqueRho :=
  ((fullRho H).tprod (fullRho H)).tprod ((fullRho H).dual.tprod (fullRho H).dual)

def duqlRho :=
  ((fullRho H).dual.tprod (fullRho H).dual).tprod ((fullRho H).tprod (fullRho H))

def qqueSplit : Split (qqueRho H) (StandardSMUVMass.qqueRho H) :=
  let S := Split.ofEquiv (uvEquiv H)
  (S.tensor S).tensor (S.dual.tensor S.dual)

def duqlSplit : Split (duqlRho H) (StandardSMUVMass.duqlRho H) :=
  let S := Split.ofEquiv (uvEquiv H)
  (S.dual.tensor S.dual).tensor (S.tensor S)

def qqueTransport := (qqueSplit H).certificate (StandardSMUVMass.qque H)

def duqlTransport := (duqlSplit H).certificate (StandardSMUVMass.duql H)

def qque := (qqueTransport H).form

def duql := (duqlTransport H).form

theorem qque_form_eq : qque H =
    (StandardSMUVMass.qque H).comp (qqueSplit H).project.toLinearMap :=
  (qqueTransport H).form_eq

theorem duql_form_eq : duql H =
    (StandardSMUVMass.duql H).comp (duqlSplit H).project.toLinearMap :=
  (duqlTransport H).form_eq

theorem qque_nonzero : qque H ≠ 0 :=
  (qqueTransport H).nonzero_of (StandardSMUVMass.qque_nonzero H)

theorem duql_nonzero : duql H ≠ 0 :=
  (duqlTransport H).nonzero_of (StandardSMUVMass.duql_nonzero H)

theorem qque_witness : qque H ((qqueSplit H).embed
    ((StandardSMUVMass.qqueSplit H).embed StandardSMGaugeTensor.qqueWitness)) = 1 :=
  ((qqueTransport H).apply_embed _).trans (StandardSMUVMass.qque_witness H)

theorem duql_witness : duql H ((duqlSplit H).embed
    ((StandardSMUVMass.duqlSplit H).embed StandardSMGaugeTensor.duqlWitness)) = 1 :=
  ((duqlTransport H).apply_embed _).trans (StandardSMUVMass.duql_witness H)

theorem qque_invariant (g : GaugeGroup × H) (x) :
    qque H (qqueRho H g x) = qque H x :=
  (qqueTransport H).invariant_of (StandardSMUVMass.qque_invariant H) g x

theorem duql_invariant (g : GaugeGroup × H) (x) :
    duql H (duqlRho H g x) = duql H x :=
  (duqlTransport H).invariant_of (StandardSMUVMass.duql_invariant H) g x

end

end GUT.StandardSMContinuousTensor

import GUT.SU6.SelectionRules.Models.StandardSMUVFields
import Physics.FieldTheory.Mass.EquivariantWeylMassTransport
import GUT.SU6.SelectionRules.StandardBranch.StandardSMRadicalTensor

open Math

/-!
# A full-gauge mass and radical tensors on actual SU(6) matter

The source is the actual analytic 15 + 2 bar6 direct-product realization.
The mass is pulled back along the proved full-group branching equivalence,
not assumed invariant from torus data. Residual Abelian actions are neutral.
-/

set_option autoImplicit false

namespace GUT.StandardSMUVMass

noncomputable section

open StandardSMUVFields SplitRepresentationProjection
open StandardSMGaugeTensor (GaugeGroup)
open InvariantWeylMass FiniteAbelianChargeSectors
open scoped TensorProduct

variable (H : Type*) [CommGroup H]

def rho : Representation ℂ (GaugeGroup × H) UV :=
  uvRho.comp (StandardSMGroup.withResidual H)

def mass : SymmetricMass (rho H) :=
  EquivariantWeylMassTransport.pullback (withResidualEquiv H)
    (StandardSMFullGaugeMass.mass (neutralCharges H))

abbrev ZeroModes := (mass H).radical.toSubmodule

theorem mem_radical_iff (x : UV) :
    x ∈ (mass H).radical.toSubmodule ↔
      withResidualEquiv H x ∈
        (StandardSMFullGaugeMass.mass (neutralCharges H)).radical.toSubmodule :=
  EquivariantWeylMassTransport.mem_radical_iff _ _ x

def zeroRho : Representation ℂ (GaugeGroup × H) (ZeroModes H) :=
  (mass H).radical.toRepresentation

set_option maxHeartbeats 800000 in
def radicalEquiv : Representation.Equiv (zeroRho H)
    (StandardSMRadicalTensor.zeroRho (neutralCharges H)) :=
  EquivariantWeylMassTransport.radicalEquiv (withResidualEquiv H)
    (StandardSMFullGaugeMass.mass (neutralCharges H))

def lightEquiv : Representation.Equiv (zeroRho H)
    (StandardSMFullGaugeMass.lightRho (neutralCharges H)) :=
  (radicalEquiv H).trans (StandardSMFullGaugeMass.radicalEquiv (neutralCharges H))

theorem mass_nonzero : (mass H).form ≠ 0 :=
  EquivariantWeylMassTransport.pullback_nonzero _ _ (StandardSMFullGaugeMass.mass_nonzero _)

theorem radical_finrank : Module.finrank ℂ (ZeroModes H) = 15 := by
  rw [(lightEquiv H).toLinearEquiv.finrank_eq]
  exact StandardSMFullGaugeMass.light_finrank

theorem radical_character (g : GaugeGroup × H) :
    (zeroRho H).character g = (StandardSMFullGaugeMass.lightRho (neutralCharges H)).character g :=
  congrFun (Representation.char_iso (lightEquiv H)) g

abbrev QQueSpace := (ZeroModes H ⊗[ℂ] ZeroModes H) ⊗[ℂ]
  (Module.Dual ℂ (ZeroModes H) ⊗[ℂ] Module.Dual ℂ (ZeroModes H))

abbrev DuqlSpace := (Module.Dual ℂ (ZeroModes H) ⊗[ℂ] Module.Dual ℂ (ZeroModes H)) ⊗[ℂ]
  (ZeroModes H ⊗[ℂ] ZeroModes H)

def qqueRho : Representation ℂ (GaugeGroup × H) (QQueSpace H) :=
  ((zeroRho H).tprod (zeroRho H)).tprod ((zeroRho H).dual.tprod (zeroRho H).dual)

def duqlRho : Representation ℂ (GaugeGroup × H) (DuqlSpace H) :=
  ((zeroRho H).dual.tprod (zeroRho H).dual).tprod ((zeroRho H).tprod (zeroRho H))

def qqueSplit : Split (qqueRho H) (StandardSMResidualTensor.qqueRepresentation (neutralCharges H)) :=
  let S := Split.ofEquiv (radicalEquiv H)
  ((S.tensor S).tensor (S.dual.tensor S.dual)).trans
    (StandardSMRadicalTensor.qqueSplit (neutralCharges H))

def duqlSplit : Split (duqlRho H) (StandardSMResidualTensor.duqlRepresentation (neutralCharges H)) :=
  let S := Split.ofEquiv (radicalEquiv H)
  ((S.dual.tensor S.dual).tensor (S.tensor S)).trans
    (StandardSMRadicalTensor.duqlSplit (neutralCharges H))

def qque : QQueSpace H →ₗ[ℂ] ℂ :=
  StandardSMGaugeTensor.qque.comp (qqueSplit H).project.toLinearMap

def duql : DuqlSpace H →ₗ[ℂ] ℂ :=
  StandardSMGaugeTensor.duql.comp (duqlSplit H).project.toLinearMap

theorem qque_nonzero : qque H ≠ 0 :=
  (qqueSplit H).pullback_nonzero _ StandardSMGaugeTensor.qque_nonzero

theorem duql_nonzero : duql H ≠ 0 :=
  (duqlSplit H).pullback_nonzero _ StandardSMGaugeTensor.duql_nonzero

theorem qque_witness : qque H ((qqueSplit H).embed StandardSMGaugeTensor.qqueWitness) = 1 := by
  change StandardSMGaugeTensor.qque
    ((qqueSplit H).project ((qqueSplit H).embed StandardSMGaugeTensor.qqueWitness)) = 1
  rw [(qqueSplit H).left_inv, StandardSMGaugeTensor.qque_witness]

theorem duql_witness : duql H ((duqlSplit H).embed StandardSMGaugeTensor.duqlWitness) = 1 := by
  change StandardSMGaugeTensor.duql
    ((duqlSplit H).project ((duqlSplit H).embed StandardSMGaugeTensor.duqlWitness)) = 1
  rw [(duqlSplit H).left_inv, StandardSMGaugeTensor.duql_witness]

theorem qque_invariant (g : GaugeGroup × H) (x : QQueSpace H) :
    qque H (qqueRho H g x) = qque H x := by
  change StandardSMGaugeTensor.qque ((qqueSplit H).project (qqueRho H g x)) = _
  rw [Representation.IntertwiningMap.isIntertwining _ _ (qqueSplit H).project]
  have hz : protonFirstCharacter (neutralCharges H) g.2 = 1 := by
    simp [protonFirstCharacter_apply, neutralCharges]
  have hc := StandardSMResidualTensor.qque_covariant (neutralCharges H) g ((qqueSplit H).project x)
  rw [hz, Circle.coe_one, one_mul] at hc
  exact hc

theorem duql_invariant (g : GaugeGroup × H) (x : DuqlSpace H) :
    duql H (duqlRho H g x) = duql H x := by
  change StandardSMGaugeTensor.duql ((duqlSplit H).project (duqlRho H g x)) = _
  rw [Representation.IntertwiningMap.isIntertwining _ _ (duqlSplit H).project]
  have hz : protonSecondCharacter (neutralCharges H) g.2 = 1 := by
    simp [protonSecondCharacter_apply, neutralCharges]
  have hc := StandardSMResidualTensor.duql_covariant (neutralCharges H) g ((duqlSplit H).project x)
  rw [hz, Circle.coe_one, one_mul] at hc
  exact hc

end

end GUT.StandardSMUVMass

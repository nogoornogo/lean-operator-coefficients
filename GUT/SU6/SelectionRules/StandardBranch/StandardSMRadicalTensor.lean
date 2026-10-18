import GUT.SU6.SelectionRules.Models.StandardSMFullGaugeMass
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

open Math

/-!
# Nonzero internal gauge tensors on an actual symmetric-mass radical

This uses the explicitly decomposed full-gauge benchmark, not an assumed
identification of an arbitrary SU(6) model. Right-handed slots belong to the
contragredient of the all-left-handed zero-mode space. No Grassmann quotient
or nonzero interaction coefficient is asserted.
-/

set_option autoImplicit false

namespace GUT.StandardSMRadicalTensor

noncomputable section

open StandardSMFullGaugeMass SplitRepresentationProjection
open StandardBranchProtonObstruction FiniteAbelianChargeSectors
open scoped TensorProduct

variable {H : Type*} [CommGroup H]

def zeroRho (k : Charges (ChargeLabel H)) :
    Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) (ZeroModes k) :=
  (mass k).radical.toRepresentation

def lightQuark (k : Charges (ChargeLabel H)) : Split (lightRho k) (quarkRho k) :=
  Split.fst _ _

def lightUp (k : Charges (ChargeLabel H)) : Split (lightRho k) (upRho k).dual :=
  (Split.snd _ _).trans (Split.fst _ _)

def lightDown (k : Charges (ChargeLabel H)) : Split (lightRho k) (downRho k).dual :=
  (Split.snd _ _).trans ((Split.snd _ _).trans (Split.fst _ _))

def lightLepton (k : Charges (ChargeLabel H)) : Split (lightRho k) (leptonRho k) :=
  (Split.snd _ _).trans ((Split.snd _ _).trans ((Split.snd _ _).trans (Split.fst _ _)))

def lightElectron (k : Charges (ChargeLabel H)) : Split (lightRho k) (electronRho k).dual :=
  (Split.snd _ _).trans ((Split.snd _ _).trans ((Split.snd _ _).trans (Split.snd _ _)))

def quarkSplit (k : Charges (ChargeLabel H)) : Split (zeroRho k) (quarkRho k) :=
  (Split.ofEquiv (radicalEquiv k)).trans (lightQuark k)

def leptonSplit (k : Charges (ChargeLabel H)) : Split (zeroRho k) (leptonRho k) :=
  (Split.ofEquiv (radicalEquiv k)).trans (lightLepton k)

def upSplit (k : Charges (ChargeLabel H)) : Split (zeroRho k).dual (upRho k) :=
  ((Split.ofEquiv (radicalEquiv k)).trans (lightUp k)).dual.trans
    (Split.ofEquiv (bidualEquiv (upRho k)).symm)

def downSplit (k : Charges (ChargeLabel H)) : Split (zeroRho k).dual (downRho k) :=
  ((Split.ofEquiv (radicalEquiv k)).trans (lightDown k)).dual.trans
    (Split.ofEquiv (bidualEquiv (downRho k)).symm)

def electronSplit (k : Charges (ChargeLabel H)) : Split (zeroRho k).dual (electronRho k) :=
  ((Split.ofEquiv (radicalEquiv k)).trans (lightElectron k)).dual.trans
    (Split.ofEquiv (bidualEquiv (electronRho k)).symm)

abbrev QQueSpace (k : Charges (ChargeLabel H)) :=
  (ZeroModes k ⊗[ℂ] ZeroModes k) ⊗[ℂ]
    (Module.Dual ℂ (ZeroModes k) ⊗[ℂ] Module.Dual ℂ (ZeroModes k))

abbrev DuqlSpace (k : Charges (ChargeLabel H)) :=
  (Module.Dual ℂ (ZeroModes k) ⊗[ℂ] Module.Dual ℂ (ZeroModes k)) ⊗[ℂ]
    (ZeroModes k ⊗[ℂ] ZeroModes k)

def qqueRho (k : Charges (ChargeLabel H)) :
    Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) (QQueSpace k) :=
  ((zeroRho k).tprod (zeroRho k)).tprod ((zeroRho k).dual.tprod (zeroRho k).dual)

def duqlRho (k : Charges (ChargeLabel H)) :
    Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) (DuqlSpace k) :=
  ((zeroRho k).dual.tprod (zeroRho k).dual).tprod ((zeroRho k).tprod (zeroRho k))

def qqueSplit (k : Charges (ChargeLabel H)) :
    Split (qqueRho k) (StandardSMResidualTensor.qqueRepresentation k) :=
  ((quarkSplit k).tensor (quarkSplit k)).tensor ((upSplit k).tensor (electronSplit k))

def duqlSplit (k : Charges (ChargeLabel H)) :
    Split (duqlRho k) (StandardSMResidualTensor.duqlRepresentation k) :=
  ((downSplit k).tensor (upSplit k)).tensor ((quarkSplit k).tensor (leptonSplit k))

def qque (k : Charges (ChargeLabel H)) : QQueSpace k →ₗ[ℂ] ℂ :=
  StandardSMGaugeTensor.qque.comp (qqueSplit k).project.toLinearMap

def duql (k : Charges (ChargeLabel H)) : DuqlSpace k →ₗ[ℂ] ℂ :=
  StandardSMGaugeTensor.duql.comp (duqlSplit k).project.toLinearMap

theorem qque_nonzero (k : Charges (ChargeLabel H)) : qque k ≠ 0 :=
  (qqueSplit k).pullback_nonzero _ StandardSMGaugeTensor.qque_nonzero

theorem duql_nonzero (k : Charges (ChargeLabel H)) : duql k ≠ 0 :=
  (duqlSplit k).pullback_nonzero _ StandardSMGaugeTensor.duql_nonzero

theorem qque_witness (k : Charges (ChargeLabel H)) :
    qque k ((qqueSplit k).embed StandardSMGaugeTensor.qqueWitness) = 1 := by
  change StandardSMGaugeTensor.qque
    ((qqueSplit k).project ((qqueSplit k).embed StandardSMGaugeTensor.qqueWitness)) = 1
  rw [(qqueSplit k).left_inv, StandardSMGaugeTensor.qque_witness]

theorem duql_witness (k : Charges (ChargeLabel H)) :
    duql k ((duqlSplit k).embed StandardSMGaugeTensor.duqlWitness) = 1 := by
  change StandardSMGaugeTensor.duql
    ((duqlSplit k).project ((duqlSplit k).embed StandardSMGaugeTensor.duqlWitness)) = 1
  rw [(duqlSplit k).left_inv, StandardSMGaugeTensor.duql_witness]

theorem qque_covariant (k : Charges (ChargeLabel H))
    (g : StandardSMGaugeTensor.GaugeGroup × H) (x : QQueSpace k) :
    qque k (qqueRho k g x) = (protonFirstCharacter k g.2 : ℂ) * qque k x := by
  change StandardSMGaugeTensor.qque ((qqueSplit k).project (qqueRho k g x)) = _
  rw [Representation.IntertwiningMap.isIntertwining _ _ (qqueSplit k).project]
  exact StandardSMResidualTensor.qque_covariant k g _

theorem duql_covariant (k : Charges (ChargeLabel H))
    (g : StandardSMGaugeTensor.GaugeGroup × H) (x : DuqlSpace k) :
    duql k (duqlRho k g x) = (protonSecondCharacter k g.2 : ℂ) * duql k x := by
  change StandardSMGaugeTensor.duql ((duqlSplit k).project (duqlRho k g x)) = _
  rw [Representation.IntertwiningMap.isIntertwining _ _ (duqlSplit k).project]
  exact StandardSMResidualTensor.duql_covariant k g _

def qqueIntertwiner (k : Charges (ChargeLabel H)) (hk : protonFirstCharacter k = 1) :
    Representation.IntertwiningMap (qqueRho k)
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ) :=
  (StandardSMResidualTensor.qqueIntertwiner k hk).comp (qqueSplit k).project

def duqlIntertwiner (k : Charges (ChargeLabel H)) (hk : protonSecondCharacter k = 1) :
    Representation.IntertwiningMap (duqlRho k)
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ) :=
  (StandardSMResidualTensor.duqlIntertwiner k hk).comp (duqlSplit k).project

set_option maxHeartbeats 800000 in
/-- This conclusion concerns the constructed benchmark with S's charges,
not an identification with an original mass sector underlying S. -/
theorem source_benchmark (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H)) :
    (mass S.charges).form ≠ 0 ∧ Module.finrank ℂ (ZeroModes S.charges) = 15 ∧
      qque S.charges ≠ 0 ∧ duql S.charges ≠ 0 ∧
      (∀ g x, qque S.charges (qqueRho S.charges g x) = qque S.charges x) ∧
      (∀ g x, duql S.charges (duqlRho S.charges g x) = duql S.charges x) := by
  obtain ⟨hFirst, hSecond⟩ := residual_protonCharacters_eq_one S
  refine ⟨mass_nonzero _, radical_finrank _, qque_nonzero _, duql_nonzero _, ?_, ?_⟩
  · intro g x
    rw [qque_covariant, hFirst]
    simp
  · intro g x
    rw [duql_covariant, hSecond]
    simp

end

end GUT.StandardSMRadicalTensor

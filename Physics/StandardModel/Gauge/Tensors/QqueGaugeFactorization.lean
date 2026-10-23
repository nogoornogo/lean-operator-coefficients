import Physics.StandardModel.Gauge.Tensors.QqueGaugeUniqueness
import Physics.StandardModel.Gauge.Tensors.ExplicitSMResidualTensor
import Math.RepresentationTheory.Invariants.ExternalInvariantFactorization

open Math

/-! Exhaustive removal of the qque gauge contraction with arbitrary multiplicities. -/
namespace Physics.QqueGaugeFactorization
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization StandardSMGaugeTensor
open scoped TensorProduct

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] Quark) := inferInstance
local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] ℂ) := inferInstance
local instance : AddCommGroup QQueSpace := inferInstance

variable {H A B C D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (c : Representation ℂ H C) (d : Representation ℂ H D)

abbrev Coefficient := IntertwiningMap (ExplicitSMResidualTensor.fields a b c d)
  (Representation.trivial ℂ (GaugeGroup × H) ℂ)

def regrouped (f : Coefficient a b c d) :=
  f.comp (regroupFour quark quark upRight electronRight a b c d).symm.toIntertwiningMap

def strip (f : Coefficient a b c d) :
    IntertwiningMap (ExplicitSMResidualTensor.multiplicity a b c d) (Representation.trivial ℂ H ℂ) :=
  rightSlice _ _ (regrouped a b c d f) qqueWitness

theorem reconstruct (f : Coefficient a b c d) :
    ExplicitSMResidualTensor.qque a b c d (strip a b c d f) = f := by
  have h := factor_left _ _ qqueIntertwiner qqueWitness
    QqueGaugeUniqueness.eq_smul_qque (regrouped a b c d f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h (regroupFour quark quark upRight electronRight a b c d v)
  change f ((regroupFour quark quark upRight electronRight a b c d).symm
    (regroupFour quark quark upRight electronRight a b c d v)) =
    ExplicitSMResidualTensor.qque a b c d (strip a b c d f) v at hv
  simpa using hv.symm

end
end Physics.QqueGaugeFactorization

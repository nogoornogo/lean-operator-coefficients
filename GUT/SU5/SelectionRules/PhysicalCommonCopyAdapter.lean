import GUT.SU5.SelectionRules.NonScalarInvariantMass
import Physics.FieldTheory.Mass.PhysicalCommonCopyModel

/-! SU(5) is a checked realization of the model-independent physical theorem.
The original symmetric mass is arbitrary; classification remains in this adapter. -/
namespace GUT.SU5.PhysicalCommonCopyAdapter
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter ExteriorSquareBranching
open StandardSMGaugeTensor ExternalInvariantTensor InvariantWeylMass BipartiteNormalForm
open NonScalarCopyMass NonScalarInvariantMass
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance
universe u
variable {H : Type*} [Group H] {S T : Type u}
  [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T) (psi : H →* Circle)

section Species
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (r : Representation ℂ GaugeGroup V) (f : IntertwiningMap r (ten.comp hom))

def sourceEmbedding : IntertwiningMap (external r s) (sourceRho s psi) :=
  (IntertwiningMap.inl ℂ (external (ten.comp hom) s) (barAction psi)).comp
    (PhysicalCommonCopyModel.externalMap f (IntertwiningMap.id s))

def targetEmbedding : IntertwiningMap (external r t) (targetRho t) :=
  PhysicalCommonCopyModel.externalMap f (IntertwiningMap.id t)

omit [FiniteDimensional ℂ T] in
theorem source_injective (hf : Function.Injective f) :
    Function.Injective (sourceEmbedding s psi r f) := by
  intro x y he
  exact TensorProduct.map_injective_of_flat_flat f.toLinearMap LinearMap.id hf
    Function.injective_id (congrArg Prod.fst he)
end Species

variable (B : SymmetricMass (fieldsRho s t psi))

/-- All structural mass-square obligations are derived from the actual
SU(5) branching and arbitrary invariant-mass normal form. -/
def realization : PhysicalCommonCopyModel.Realization (s := s) (t := t) B := by
  let M := crossMap (sourceRho s psi) (targetRho t) B
  have hB : B.form = (ofDirac M).form := normal_form s t psi B
  refine {
    q := PhysicalCommonCopyModel.speciesOfDirac quark M B hB
      (quarkMap s t psi M) (sourceEmbedding s psi quark quarkTenMap)
      (source_injective s psi quark quarkTenMap MixedTenMass.quarkTen_injective)
      (targetEmbedding t quark quarkTenMap) ?_
    u := PhysicalCommonCopyModel.speciesOfDirac upRight.dual M B hB
      (upMap s t psi M) (sourceEmbedding s psi upRight.dual upTenMap)
      (source_injective s psi upRight.dual upTenMap MixedTenMass.upTen_injective)
      (targetEmbedding t upRight.dual upTenMap) ?_
    e := PhysicalCommonCopyModel.speciesOfDirac electronRight.dual M B hB
      (electronMap s t psi M) (sourceEmbedding s psi electronRight.dual electronTenMap)
      (source_injective s psi electronRight.dual electronTenMap MixedTenMass.electronTen_injective)
      (targetEmbedding t electronRight.dual electronTenMap) ?_ }
  · apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro v x
    exact quark_pure s t psi M v x
  · apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro v x
    exact up_pure s t psi M v x
  · apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro v x
    exact electron_pure s t psi M v x

/-- Checked SU(5) instance of the model interface, for every invariant mass. -/
def model : PhysicalCommonCopyModel.Model s t (fieldsRho s t psi) where
  realize := realization s t psi

/-- The SU(5) application consumes the shared physical theorem directly. -/
theorem arbitrary_mass_light_exterior (hs : IsSemisimpleRepresentation s)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    (realization s t psi B).HasLightExterior :=
  (model s t psi).arbitrary_mass_light_exterior B hs hd

end
end GUT.SU5.PhysicalCommonCopyAdapter

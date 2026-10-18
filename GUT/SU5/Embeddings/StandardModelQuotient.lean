import GUT.SU5.Embeddings.StandardModelKernel
import Mathlib.Topology.Maps.Strict.Group

/-!
# The Standard Model quotient as a closed subgroup of SU(5)

The actual kernel was identified with the central cyclic group of order six
in `StandardModelKernel`. Here the induced injective homomorphism is a
topological embedding, and the quotient is topologically isomorphic to its image.
-/

set_option autoImplicit false

namespace GUT.SU5.StandardModelEmbedding

noncomputable section

open StandardSMGaugeTensor

abbrev SMQuotient := GaugeGroup ⧸ hom.ker

def quotientHom : SMQuotient →* TargetGroup := QuotientGroup.kerLift hom

@[simp] theorem quotientHom_mk (g : GaugeGroup) :
    quotientHom (QuotientGroup.mk g) = hom g := rfl

theorem quotientHom_injective : Function.Injective quotientHom :=
  QuotientGroup.kerLift_injective hom

theorem hom_isStrictMap : Topology.IsStrictMap hom :=
  continuous_hom.isClosedMap.isStrictMap continuous_hom

theorem quotientHom_isEmbedding : Topology.IsEmbedding quotientHom :=
  hom.isStrictMap_iff_isEmbedding_kerLift.mp hom_isStrictMap

theorem quotientHom_isClosedEmbedding : Topology.IsClosedEmbedding quotientHom :=
  quotientHom_isEmbedding.continuous.isClosedEmbedding quotientHom_injective

instance quotientT2Space : T2Space SMQuotient := quotientHom_isEmbedding.t2Space

def quotientContinuousHom : SMQuotient →ₜ* TargetGroup where
  toMonoidHom := quotientHom
  continuous_toFun := quotientHom_isEmbedding.continuous

def quotientImageEquiv : SMQuotient ≃ₜ* hom.range :=
  ContinuousMulEquiv.quotientKerEquivRange hom_isStrictMap

@[simp] theorem quotientImageEquiv_mk (g : GaugeGroup) :
    (quotientImageEquiv (QuotientGroup.mk g) : TargetGroup) = hom g := rfl

theorem image_isClosed : IsClosed (hom.range : Set TargetGroup) := by
  exact (isCompact_range continuous_hom).isClosed

end

end GUT.SU5.StandardModelEmbedding

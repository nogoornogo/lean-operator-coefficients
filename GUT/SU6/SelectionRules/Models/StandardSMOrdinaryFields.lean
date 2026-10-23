import GUT.SU6.SelectionRules.Models.StandardSMUVFields
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylBenchmark
import GUT.SU6.Adapters.AbelianCharacterEquivalence
import Math.RepresentationTheory.Unitary.ContinuousRepresentationTransport

open Physics

open Math

/-!
# Full SU(6) action on the canonical neutral benchmark fields

An actual Abelian representation equivalence identifies `ordinaryFields`
with the analytic direct-product UV realization. Transporting its SU(6)
action constructs an extension of the existing physical-torus action.
No uniqueness of this extension or unitarity of this chosen equivalence
with respect to the original canonical inner product is claimed.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace GUT.StandardSMOrdinaryFields

noncomputable section

open StandardSMUVFields ConcreteSU6Representations
open StandardSMCharacterTarget StandardWeylMassSource
open UnitaryVirtualRealization SplitRepresentationProjection
open ActualUnitaryGroupRepresentation

variable (H : Type*) [CommGroup H]

abbrev Fields := (ordinaryFields (ConcreteWeylBenchmark.matter H)).V

def physicalHom : CombinedGroup H →* ActualRestriction.SU6 :=
  (PhysicalSMTorusTarget.embedding (-2) 3).comp
    (MonoidHom.fst PhysicalSMTorusTarget.Group H)

def restricted (R : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := R.V
  rho := R.rho.comp (physicalHom H)
  unitary g := R.unitary (physicalHom H g)

def unitaryUV : ActualUnitaryGroupRepresentation (CombinedGroup H) :=
  product (product (restricted H exteriorTwo) (restricted H antifundamental))
    (restricted H antifundamental)

def unitaryUVEquiv : Representation.Equiv (unitaryUV H).rho (uvRho.comp (physicalHom H)) :=
  (productEquiv _ _).trans
    (prodEquiv (productEquiv _ _) (Representation.Equiv.refl _))

theorem character_eq (g : CombinedGroup H) :
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho.character g =
      (unitaryUV H).rho.character g := by
  change (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho.character
    (Multiplicative.ofAdd g.1.toAdd, g.2) = _
  rw [ConcreteWeylBenchmark.fields_character]
  change _ = (product (product _ _) _).rho.character g
  rw [product_character, product_character]
  change _ = (exteriorTwo.rho.character (physicalHom H g) +
    antifundamental.rho.character (physicalHom H g)) +
    antifundamental.rho.character (physicalHom H g)
  change exteriorTwo.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1) +
      2 * antifundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1) =
    (exteriorTwo.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1) +
      antifundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1)) +
      antifundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1)
  ring

def physicalEquiv : Representation.Equiv
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho (uvRho.comp (physicalHom H)) :=
  (AbelianCharacterEquivalence.ofCharacter _ _ (character_eq H)).trans (unitaryUVEquiv H)

def su6Rho : Representation ℂ ActualRestriction.SU6
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).V where
  toFun g := (physicalEquiv H).toLinearEquiv.symm.conj (uvRho g)
  map_one' := by ext x; simp [Representation.Equiv.coe_invFun]
  map_mul' g h := by ext x; simp [Representation.Equiv.coe_invFun]

def su6Equiv : Representation.Equiv (su6Rho H) uvRho :=
  .mk (physicalEquiv H).toLinearEquiv (by
    intro g
    apply LinearMap.ext; intro x
    simp [su6Rho, Representation.Equiv.coe_invFun])

theorem physical_restriction :
    (su6Rho H).comp (physicalHom H) =
      (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho := by
  apply MonoidHom.ext; intro g
  exact (physicalEquiv H).symm.conj_apply_self g

theorem su6_jointlyContinuous : ContinuousRepresentationScope.IsJointlyContinuous (su6Rho H) := by
  change Continuous (fun p : ActualRestriction.SU6 × Fields H =>
    (physicalEquiv H).toLinearEquiv.symm (uvRho p.1 ((physicalEquiv H).toLinearEquiv p.2)))
  exact ContinuousRepresentationTransport.continuous_conjugate
    (physicalEquiv H).toLinearEquiv uvRho uv_jointlyContinuous

def gaugeRho : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H)
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).V :=
  (su6Rho H).comp (StandardSMGroup.withResidual H)

def gaugeEquiv : Representation.Equiv (gaugeRho H)
    (uvRho.comp (StandardSMGroup.withResidual H)) :=
  restrictEquiv (su6Equiv H) (StandardSMGroup.withResidual H)

def torusHom : CombinedGroup H →* (StandardSMGaugeTensor.GaugeGroup × H) :=
  StandardSMTorus.hom.prodMap (MonoidHom.id H)

theorem gauge_restriction :
    (gaugeRho H).comp (torusHom H) =
      (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho := by
  change (su6Rho H).comp ((StandardSMGroup.withResidual H).comp (torusHom H)) = _
  unfold torusHom
  rw [StandardSMTorus.withResidual_comp]
  exact physical_restriction H

end

end GUT.StandardSMOrdinaryFields

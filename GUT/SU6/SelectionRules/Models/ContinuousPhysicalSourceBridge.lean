import GUT.SU6.Adapters.CompactRepresentationUnitarization
import GUT.SU6.Branching.PhysicalSMTorusTarget

/-!
# Continuous physical-source specializations of hypercharge character rigidity

This module connects compact Haar unitarization to the already checked
fifth-moment and physical-torus targets.  The source consists of an arbitrary
finite integer virtual combination of finite-dimensional complex `SU(6)`
representations whose actions are jointly continuous.  No invariant inner
product is assumed on any supplied summand.
-/

namespace GUT
namespace ContinuousPhysicalSourceBridge

open CompactRepresentationUnitarization

noncomputable section

/-- A jointly continuous finite virtual source with the exact SM finite-weight
restriction has the standard cocharacter pair. -/
theorem eq_standard_of_exactSMRestriction
    (source : FiniteContinuousVirtualRepresentation)
    (generations singlets : ℤ) (m n : ℚ)
    (hGenerations : generations ≠ 0)
    (hExact : PhysicalFifthMomentBridge.IsExactSMRestriction
      source.ambientLaurentModel.poly generations singlets m n) :
    m = -2 ∧ n = 3 :=
  PhysicalFifthMomentBridge.eq_standard_of_virtualModel_exactSMRestriction
    source.ambientLaurentModel generations singlets m n hGenerations hExact

/-- Function equality on the actual compact physical torus is enough for the
same conclusion for every jointly continuous finite virtual source. -/
theorem eq_standard_of_characterOnPhysicalTorus
    (source : FiniteContinuousVirtualRepresentation)
    (generations singlets m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hExact : PhysicalTorusCharacterBridge.IsExactSMCharacterOnPhysicalTorus
      (chi := source.toVirtual) generations singlets m n) :
    m = -2 ∧ n = 3 :=
  PhysicalTorusCharacterBridge.eq_standard_of_virtualModel_characterOnPhysicalTorus
    source.ambientLaurentModel generations singlets m n hGenerations hExact

/-- Fully representation-theoretic formulation: character equivalence between
the restricted jointly continuous source and the explicit SM-plus-singlets
physical-torus target forces the standard cocharacter. -/
theorem eq_standard_of_characterEquivalent
    (source : FiniteContinuousVirtualRepresentation)
    (generations singlets m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hEquivalent : PhysicalSMTorusTarget.IsSMTargetCharacterEquivalent
      source.toVirtual generations singlets m n) :
    m = -2 ∧ n = 3 :=
  PhysicalSMTorusTarget.eq_standard_of_virtualModel_characterEquivalent
    source.ambientLaurentModel generations singlets m n
      hGenerations hEquivalent

end
end ContinuousPhysicalSourceBridge
end GUT

import GUT.SU6.Representations.UnitaryVirtualRestriction
import GUT.SU5.Branching.TorusCharacter

/-! Old GUT restriction imports retain legacy type heads and repeated method
calls. The expected deprecation warnings show their canonical replacements. -/

namespace GUT.SourceCompatibilityRestrictionControl
open GUT.UnitaryVirtualRealization
variable {G K J : Type*} [Group G] [Group K] [Group J]
    (f : K →* G) (h : J →* K)

example (R : ActualUnitaryGroupRepresentation G) :
    R.restrict f = ActualUnitaryGroupRepresentation.restrict f R := rfl

example (R : ActualUnitaryGroupRepresentation G) :
    (R.restrict f).restrict h =
      ActualUnitaryGroupRepresentation.restrict h
        (ActualUnitaryGroupRepresentation.restrict f R) := rfl

example (source : FiniteUnitaryVirtualRepresentation G) :
    (FiniteUnitaryVirtualRepresentation.positive source).restrict f =
      FiniteUnitaryVirtualRepresentation.positive (source.restrict f) :=
  FiniteUnitaryVirtualRepresentation.restrict_positive f source

-- The retained GUT import carrier still exposes the shared character API.
open GUT.SU5.TorusCharacter in
example : @rawCharacter = @Physics.SU5.TorusCharacter.rawCharacter := rfl

end GUT.SourceCompatibilityRestrictionControl

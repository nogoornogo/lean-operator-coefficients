import GUT.SU6.SelectionRules.StandardBranch.StandardBlockGaugeCancellation

/-!
# Ambient models of strict ordinary Abelian sources

These definitions forget only the residual ordinary Abelian action and retain
the underlying finite virtual `SU(6)` representation and its canonical hypercharge character rigidity
ambient Laurent model.
-/

namespace GUT
namespace StandardBlockGaugeCancellation

noncomputable section

universe u

namespace OrdinaryAbelianSummand

variable {H : Type u} [CommGroup H]

/-- Forget the residual Abelian action while retaining the underlying actual
finite-dimensional `SU(6)` representation and its virtual coefficient. -/
def toVirtualSummand (s : OrdinaryAbelianSummand H) :
    VirtualRestriction.VirtualSummand where
  coeff := s.coeff
  rep :=
    ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.toActualRepresentation
      s.rep

/-- Retain the canonical hypercharge character rigidity ambient Laurent character while forgetting the
ordinary residual action. -/
def toModeledVirtualSummand (s : OrdinaryAbelianSummand H) :
    AmbientCharacterBridge.ModeledVirtualSummand where
  coeff := s.coeff
  rep :=
    ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.toActualRepresentation
      s.rep
  poly :=
    (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.ambientLaurentModel
      s.rep).poly
  evaluates_rep :=
    (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.ambientLaurentModel
      s.rep).evaluates_character

end OrdinaryAbelianSummand

namespace OrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- The finite virtual `SU(6)` representation underlying a strict ordinary
Abelian source. -/
def toFiniteVirtual (source : OrdinaryAbelianSource H) :
    VirtualRestriction.FiniteVirtualSU6Representation :=
  source.map OrdinaryAbelianSummand.toVirtualSummand

/-- The same finite virtual source with each summand's checked hypercharge character rigidity Laurent
model retained. -/
def toModeledFiniteVirtual (source : OrdinaryAbelianSource H) :
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation :=
  source.map OrdinaryAbelianSummand.toModeledVirtualSummand

theorem toModeledFiniteVirtual_toVirtual
    (source : OrdinaryAbelianSource H) :
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual
        source.toModeledFiniteVirtual =
      source.toFiniteVirtual := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        s.toModeledVirtualSummand.toVirtualSummand ::
            AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual
              (toModeledFiniteVirtual source) =
          s.toVirtualSummand :: toFiniteVirtual source
      rw [ih]
      rfl

/-- hypercharge character rigidity Laurent model for the underlying finite virtual `SU(6)` character of
every strict ordinary Abelian source. -/
def ambientLaurentModel (source : OrdinaryAbelianSource H) :
    AmbientCharacterBridge.VirtualAmbientLaurentModel
      source.toFiniteVirtual where
  poly :=
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.poly
      source.toModeledFiniteVirtual
  evaluates_character t := by
    rw [← source.toModeledFiniteVirtual_toVirtual]
    exact
      AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.poly_evaluates
        source.toModeledFiniteVirtual t

@[simp]
theorem toFiniteVirtual_nil :
    toFiniteVirtual ([] : OrdinaryAbelianSource H) = [] :=
  rfl

@[simp]
theorem toFiniteVirtual_cons
    (s : OrdinaryAbelianSummand H) (source : OrdinaryAbelianSource H) :
    toFiniteVirtual (s :: source) =
      s.toVirtualSummand :: toFiniteVirtual source :=
  rfl

end OrdinaryAbelianSource

end

end StandardBlockGaugeCancellation
end GUT

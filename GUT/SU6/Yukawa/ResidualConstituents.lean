import GUT.SU6.Yukawa.NonSingletCoordinates
import Physics.StandardModel.Gauge.TwistedFundamentalIrreducibility

open Math

/-! Irreducible factors of the ten, five and dual-five residual representations. -/
set_option autoImplicit false
namespace GUT.SU6ResidualConstituents
noncomputable section
open StandardSMGaugeTensor SU6NonSingletCoordinates SplitRepresentationProjection
open StandardSMIrreducibility

def dualFiveSplit : Representation.Equiv fiveRho.dual
    ((twist color (-2)).dual.prod (twist weak 3).dual) :=
  (dualProdEquiv (twist color (-2)) (twist weak 3)).symm

variable (H : Type*) [CommGroup H]

def residualDualFiveSplit : Representation.Equiv
    (fiveRho.dual.comp (MonoidHom.fst GaugeGroup H))
    (Representation.prod ((twist color (-2)).dual.comp (MonoidHom.fst GaugeGroup H))
      ((twist weak 3).dual.comp (MonoidHom.fst GaugeGroup H))) :=
  restrictEquiv dualFiveSplit (MonoidHom.fst GaugeGroup H)

theorem factors_irreducible :
    Representation.IsIrreducible (upRight.dual.comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible (quark.comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible (electronRight.dual.comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible ((twist color (-2)).comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible ((twist weak 3).comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible ((twist color (-2)).dual.comp (MonoidHom.fst GaugeGroup H)) ∧
    Representation.IsIrreducible ((twist weak 3).dual.comp (MonoidHom.fst GaugeGroup H)) := by
  let : upRight.dual.IsIrreducible := upLeft_irreducible
  let : quark.IsIrreducible := quark_irreducible
  let : electronRight.dual.IsIrreducible := electronLeft_irreducible
  let : (twist color (-2)).IsIrreducible := twisted_color_irreducible _
  let : (twist weak 3).IsIrreducible := twisted_weak_irreducible _
  let : (twist color (-2)).dual.IsIrreducible := twisted_color_dual_irreducible _
  let : (twist weak 3).dual.IsIrreducible := twisted_weak_dual_irreducible _
  exact ⟨neutral_extension_irreducible _ H, neutral_extension_irreducible _ H,
    neutral_extension_irreducible _ H, neutral_extension_irreducible _ H,
    neutral_extension_irreducible _ H, neutral_extension_irreducible _ H,
    neutral_extension_irreducible _ H⟩

end
end GUT.SU6ResidualConstituents

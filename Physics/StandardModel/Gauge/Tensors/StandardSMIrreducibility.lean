import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Math.RepresentationTheory.Decomposition.IrreducibilityTransport
import Math.RepresentationTheory.Decomposition.ProductIrreducibility
import Mathlib.Analysis.Complex.Polynomial.Basic

open Math

/-! The fixed Q, up and electron gauge representations are irreducible.
These are proved facts about the SM covering group, not source assumptions. -/

namespace Physics.StandardSMIrreducibility
noncomputable section
open Representation StandardSMGaugeTensor SmallSpecialUnitary ExternalTensorProduct
open scoped TensorProduct

private def colorInclusion : Matrix.specialUnitaryGroup (Fin 3) ℂ →* GaugeGroup :=
  MonoidHom.inl _ _

private def nonabelianInclusion :
    (Matrix.specialUnitaryGroup (Fin 3) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) →*
      GaugeGroup where
  toFun g := (g.1, g.2, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

theorem quark_irreducible : quark.IsIrreducible := by
  let : IsIrreducible (defining 3) := defining_three_irreducible
  let : IsIrreducible (defining 2) := defining_two_irreducible
  have he : quark.comp nonabelianInclusion = externalTprod (defining 3) (defining 2) := by
    apply MonoidHom.ext
    intro g
    apply TensorProduct.ext'
    intro v w
    simp [quark, twist, phase, nonabelianInclusion, Representation.tprod_apply,
      externalTprod, color, weak, defining]
  have : IsIrreducible (quark.comp nonabelianInclusion) := by
    rw [he]
    exact ProductIrreducibility.externalTprod_isIrreducible _ _
  exact Math.RepresentationTheory.isIrreducible_of_comp quark nonabelianInclusion

theorem upRight_irreducible : upRight.IsIrreducible := by
  have he : upRight.comp colorInclusion = defining 3 := by
    ext g v
    simp [upRight, twist, phase, colorInclusion, color, defining]
  have : IsIrreducible (upRight.comp colorInclusion) := he.symm ▸ defining_three_irreducible
  exact Math.RepresentationTheory.isIrreducible_of_comp upRight colorInclusion

theorem electronRight_irreducible : electronRight.IsIrreducible :=
  Representation.isIrreducible_of_finrank_eq_one electronRight (by simp)

theorem upLeft_irreducible : upRight.dual.IsIrreducible := by
  let : IsIrreducible upRight := upRight_irreducible
  exact Math.RepresentationTheory.dual_isIrreducible upRight

theorem electronLeft_irreducible : electronRight.dual.IsIrreducible := by
  let : IsIrreducible electronRight := electronRight_irreducible
  exact Math.RepresentationTheory.dual_isIrreducible electronRight

end
end Physics.StandardSMIrreducibility

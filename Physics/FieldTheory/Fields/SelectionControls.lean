import Physics.FieldTheory.Fields.SelectedFields
import Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary
import Math.RepresentationTheory.Fields.Controls
import Physics.FieldTheory.Jets.Lagrangian.FieldInputConnection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A neutral extra light dual pair leaves the dual chiral index unchanged,
while it prevents an exact field dictionary to the smaller light target. -/
namespace Physics.FieldSelectionControls
set_option autoImplicit false
noncomputable section
open Math Representation
abbrev neutral := Representation.trivial ℂ Unit ℂ
abbrev withPair := neutral.prod (neutral.prod neutral.dual)
def zeroMass : InvariantWeylMass.SymmetricMass withPair :=
  InvariantWeylMass.SymmetricMass.zero withPair

theorem unchanged_index (g : Unit) :
    withPair.character g - withPair.dual.character g =
      neutral.character g - neutral.dual.character g := by
  rw [Representation.char_dual, Representation.char_dual]
  have h : g⁻¹ = g := Subsingleton.elim _ _
  rw [h, sub_self, sub_self]

theorem extra_pair_light :
    ((0 : ℂ), ((1 : ℂ), (0 : Module.Dual ℂ ℂ))) ∈ zeroMass.radical.toSubmodule := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical]
  intro y
  rfl

theorem no_exact_dictionary : ¬ Nonempty (Representation.Equiv neutral zeroMass.radical.toRepresentation) := by
  rintro ⟨e⟩
  let r := InvariantWeylMass.SymmetricMass.zeroRadicalEquiv withPair
  have h := (e.trans r).toLinearEquiv.finrank_eq
  norm_num [Module.finrank_prod, Subspace.dual_finrank_eq] at h

theorem mixing_lifts :
    (1 : ℂ) ∈ (InvariantWeylMass.SymmetricMass.zero neutral).radical.toSubmodule ∧
      LightInheritanceBoundary.retained neutral 1 ∉
        (LightInheritanceBoundary.pairedMass neutral).radical.toSubmodule :=
  LightInheritanceBoundary.light_not_preserved neutral 1 one_ne_zero

theorem broken_density : ¬ ∀ g : LagrangianFieldInputConnection.Group,
    PairedWeylInput.action g YukawaModelControls.nonScalar = YukawaModelControls.nonScalar :=
  EulerDensityConnection.broken_density_rejected

end
end Physics.FieldSelectionControls

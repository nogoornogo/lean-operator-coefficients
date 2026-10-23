import Physics.FieldTheory.Mass.Spectrum.UnitaryVirtualRealization

/-! Restriction of the legacy bundled Hilbert representations commutes with
their canonical products and multiplicities, including zero-dimensional ones.
The equalities retain the field spaces and their inner products. -/

set_option autoImplicit false

namespace Physics.UnitaryVirtualRealization

noncomputable section

namespace ActualUnitaryGroupRepresentation

variable {G K : Type*} [Group G] [Group K] (f : K →* G)

def restrict (R : ActualUnitaryGroupRepresentation G) : ActualUnitaryGroupRepresentation K where
  V := R.V
  rho := R.rho.comp f
  unitary := fun g => R.unitary (f g)

theorem restrict_zero : restrict f (zero : ActualUnitaryGroupRepresentation G) = zero := rfl

theorem restrict_product (R S : ActualUnitaryGroupRepresentation G) :
    restrict f (product R S) = product (restrict f R) (restrict f S) := rfl

theorem restrict_copies (n : ℕ) (R : ActualUnitaryGroupRepresentation G) :
    restrict f (copies n R) = copies n (restrict f R) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copies, restrict_product, ih, copies]

end ActualUnitaryGroupRepresentation

namespace FiniteUnitaryVirtualRepresentation

variable {G K : Type*} [Group G] [Group K] (f : K →* G)

def restrict : FiniteUnitaryVirtualRepresentation G → FiniteUnitaryVirtualRepresentation K
  | [] => []
  | s :: source => ⟨s.coeff, s.rep.restrict f⟩ :: restrict source

theorem restrict_positive (source : FiniteUnitaryVirtualRepresentation G) :
    (positive source).restrict f = positive (restrict f source) := by
  induction source with
  | nil => rfl
  | cons s source ih =>
    simp only [positive, restrict, ActualUnitaryGroupRepresentation.restrict_product,
      ActualUnitaryGroupRepresentation.restrict_copies, ih]

end FiniteUnitaryVirtualRepresentation

end

end Physics.UnitaryVirtualRealization

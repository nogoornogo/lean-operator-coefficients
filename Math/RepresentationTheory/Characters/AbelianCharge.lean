import Mathlib.Analysis.Complex.Circle

/-!
# Circle-valued residual characters as additive charge labels

Charge labels are characters of the acting group, not elements of that group.
The compatibility namespace does not impose finiteness or an SU(6) action.
-/

namespace Math.FiniteAbelianChargeSectors

noncomputable section

/-- Additive charge labels associated with a multiplicative Abelian
residual group.  Addition of labels is pointwise multiplication of physical
circle-valued characters. -/
abbrev ChargeLabel (H : Type*) [Group H] := Additive (H →* Circle)

@[simp]
theorem chargeLabel_zero_apply
    {H : Type*} [Group H] (h : H) :
    ((0 : ChargeLabel H).toMul h : ℂ) = 1 := by
  rfl

@[simp]
theorem chargeLabel_add_apply
    {H : Type*} [CommGroup H]
    (a b : ChargeLabel H) (h : H) :
    (((a + b).toMul h : Circle) : ℂ) =
      ((a.toMul h : Circle) : ℂ) * ((b.toMul h : Circle) : ℂ) := by
  rfl

@[simp]
theorem chargeLabel_neg_apply
    {H : Type*} [CommGroup H]
    (a : ChargeLabel H) (h : H) :
    (((-a).toMul h : Circle) : ℂ) =
      (((a.toMul h : Circle) : ℂ))⁻¹ := by
  rfl

/-- A circle-valued residual character defines the common homomorphism from
integer central degree to additive charge labels. -/
def centralDegreeCharge
    {H : Type*} [CommGroup H] (eta : H →* Circle) :
    ℤ →+ ChargeLabel H where
  toFun n := Additive.ofMul (eta ^ n)
  map_zero' := by
    apply Additive.toMul.injective
    simp
  map_add' m n := by
    apply Additive.toMul.injective
    simp [zpow_add]

@[simp]
theorem centralDegreeCharge_toMul
    {H : Type*} [CommGroup H] (eta : H →* Circle) (n : ℤ) :
    (centralDegreeCharge eta n).toMul = eta ^ n :=
  rfl

/-- Evaluation of the affine source charge is multiplication of the
independent source character by the central character to the weight degree. -/
theorem affineCharge_apply
    {H : Type*} [CommGroup H]
    (eta offset : H →* Circle) (degree : ℤ) (h : H) :
    (Additive.ofMul offset + centralDegreeCharge eta degree).toMul h =
      offset h * (eta h) ^ degree := by
  rfl


end

end Math.FiniteAbelianChargeSectors

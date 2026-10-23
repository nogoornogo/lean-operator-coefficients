import Math.RepresentationTheory.Characters.AbelianCharge
import Physics.StandardModel.Operators.Selection.AbelianProtonCharge

open Math

/-!
# Residual characters of the two Standard Model proton-operator signatures

These character identities are independent of any UV gauge representation.
-/

namespace Physics.FiniteAbelianChargeSectors

open Math.FiniteAbelianChargeSectors
noncomputable section

open StandardBranchProtonObstruction

/-- The physical residual-group character carried by the first proton
contraction. -/
def protonFirstCharacter
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H)) : H →* Circle :=
  (protonFirst k).toMul

/-- The physical residual-group character carried by the second proton
contraction. -/
def protonSecondCharacter
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H)) : H →* Circle :=
  (protonSecond k).toMul

@[simp]
theorem protonFirstCharacter_apply
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H)) (h : H) :
    protonFirstCharacter k h =
      k.quark.toMul h * k.quark.toMul h *
        (k.up.toMul h)⁻¹ * (k.electron.toMul h)⁻¹ := by
  rfl

@[simp]
theorem protonSecondCharacter_apply
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H)) (h : H) :
    protonSecondCharacter k h =
      k.quark.toMul h * k.lepton.toMul h *
        (k.up.toMul h)⁻¹ * (k.down.toMul h)⁻¹ := by
  rfl

theorem protonFirstCharacter_eq_one_of_eq_zero
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H))
    (hk : protonFirst k = 0) : protonFirstCharacter k = 1 := by
  apply MonoidHom.ext
  intro h
  have hAt := congrArg (fun q : ChargeLabel H => q.toMul h) hk
  simpa [protonFirstCharacter] using hAt

theorem protonSecondCharacter_eq_one_of_eq_zero
    {H : Type*} [CommGroup H]
    (k : Charges (ChargeLabel H))
    (hk : protonSecond k = 0) : protonSecondCharacter k = 1 := by
  apply MonoidHom.ext
  intro h
  have hAt := congrArg (fun q : ChargeLabel H => q.toMul h) hk
  simpa [protonSecondCharacter] using hAt


/-- Multiplet-compatible charges give trivial characters, including torsion. -/
theorem protonCharacters_eq_one_of_su5OrbitCompatible
    {H : Type*} [CommGroup H] (k : Charges (ChargeLabel H))
    (hk : SU5OrbitCompatible k) :
    protonFirstCharacter k = 1 ∧ protonSecondCharacter k = 1 := by
  obtain ⟨hFirst, hSecond⟩ := proton_functionals_eq_zero_of_su5OrbitCompatible k hk
  exact ⟨protonFirstCharacter_eq_one_of_eq_zero k hFirst,
    protonSecondCharacter_eq_one_of_eq_zero k hSecond⟩

end

end Physics.FiniteAbelianChargeSectors

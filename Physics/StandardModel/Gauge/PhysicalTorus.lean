import Physics.StandardModel.Spectrum.TorusCharacter
import Physics.StandardModel.Gauge.StandardSMGaugeTensor

open Math

/-!
# Physical color/weak/hypercharge coordinates

The existing namespace is retained for compatibility. No UV representation
is assumed by these physical SM coordinate constructions.

The four circles cover the determinant-one diagonal torus, with integral
hypercharges (-2,3). Surjectivity is proved using a circle sixth root, not
assumed. These are coordinates of a covering torus, not an injective chart.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GUT.SU5.PhysicalTorus

open Math.SU5
noncomputable section

open MaximalTorus StandardAbelianCharge TorusCharacter

abbrev Coordinates := Fin 4 → Circle

def entries (z : Coordinates) : Fin 5 → Circle :=
  ![z 0 * z 3 ^ (-2 : ℤ), z 1 * z 3 ^ (-2 : ℤ),
    (z 0 * z 1)⁻¹ * z 3 ^ (-2 : ℤ), z 2 * z 3 ^ (3 : ℤ),
    (z 2)⁻¹ * z 3 ^ (3 : ℤ)]

theorem entries_prod (z : Coordinates) : ∏ i, entries z i = 1 := by
  simp only [entries, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
  abel

def toTorus : Coordinates →* Torus where
  toFun z := ⟨entries z, entries_prod z⟩
  map_one' := by
    apply Subtype.ext
    funext i
    change entries 1 i = 1
    fin_cases i <;> norm_num [entries]
  map_mul' z w := by
    apply Subtype.ext
    funext i
    change entries (z * w) i = entries z i * entries w i
    fin_cases i <;> dsimp [entries] <;>
      simp only [mul_zpow] <;>
      apply Additive.ofMul.injective <;>
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] <;> abel

theorem exists_sixth_root (a : Circle) : ∃ z : Circle, z ^ (6 : ℤ) = a := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective a
  refine ⟨Circle.exp (t / 6), ?_⟩
  rw [zpow_ofNat, ← Circle.exp_natCast_mul]
  congr 1
  ring

theorem toTorus_surjective : Function.Surjective toTorus := by
  intro t
  obtain ⟨z, hz⟩ := exists_sixth_root ((t.val 0 * t.val 1 * t.val 2)⁻¹)
  refine ⟨![t.val 0 * z ^ (2 : ℤ), t.val 1 * z ^ (2 : ℤ),
    t.val 3 * z ^ (-3 : ℤ), z], ?_⟩
  apply Subtype.ext
  funext i
  have ht : t.val 0 * t.val 1 * t.val 2 * t.val 3 * t.val 4 = 1 := by
    have hp : ∏ i : Fin 5, t.val i = 1 := t.property
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hp
    change t.val 0 * (t.val 1 * (t.val 2 * (t.val 3 * t.val 4))) = 1 at hp
    simpa only [mul_assoc] using hp
  fin_cases i
  · change (t.val 0 * z ^ (2 : ℤ)) * z ^ (-2 : ℤ) = t.val 0
    group
  · change (t.val 1 * z ^ (2 : ℤ)) * z ^ (-2 : ℤ) = t.val 1
    group
  · change ((t.val 0 * z ^ (2 : ℤ)) * (t.val 1 * z ^ (2 : ℤ)))⁻¹ *
      z ^ (-2 : ℤ) = t.val 2
    calc
      _ = (t.val 0 * t.val 1)⁻¹ * (z ^ (6 : ℤ))⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      _ = t.val 2 := by rw [hz]; simp [mul_assoc]
  · change (t.val 3 * z ^ (-3 : ℤ)) * z ^ (3 : ℤ) = t.val 3
    group
  · change (t.val 3 * z ^ (-3 : ℤ))⁻¹ * z ^ (3 : ℤ) = t.val 4
    have he : (t.val 0 * t.val 1 * t.val 2 * t.val 3)⁻¹ = t.val 4 :=
      inv_eq_of_mul_eq_one_right ht
    calc
      _ = (t.val 3)⁻¹ * z ^ (6 : ℤ) := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      _ = (t.val 0 * t.val 1 * t.val 2 * t.val 3)⁻¹ := by
        simp only [hz, mul_inv_rev]
      _ = t.val 4 := he

/-- The physical integer exponents are obtained from the actual diagonal
entries; the last raw exponent is zero in the rank-four normal form. -/
def exponent (w : ReducedWeight) : Fin 4 → ℤ :=
  ![w 0 - w 2, w 1 - w 2, w 3, -2 * (w 0 + w 1 + w 2) + 3 * w 3]

theorem weightCharacter_toTorus (w : ReducedWeight) (z : Coordinates) :
    weightCharacter w (toTorus z) = ∏ i, z i ^ exponent w i := by
  change (∏ i : Fin 5, entries z i ^ rawReducedWeight w i) = _
  rw [Fin.prod_univ_castSucc]
  simp only [rawReducedWeight_last, rawReducedWeight_castSucc, zpow_zero, mul_one]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, entries, exponent,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  dsimp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem weightCharacter_fourier (w : ReducedWeight) (x : UnitAddTorus (Fin 4)) :
    (weightCharacter w (toTorus (fun i => AddCircle.toCircle (x i))) : ℂ) =
      UnitAddTorus.mFourier (exponent w) x := by
  rw [weightCharacter_toTorus]
  change Circle.coeHom (∏ i, AddCircle.toCircle (x i) ^ exponent w i) = _
  rw [map_prod]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    AddCircle.toCircle_zsmul]
  rfl

theorem eval_physical_iff {H : Type*} [CommGroup H]
    (p q : ResolvedCharacter (FiniteAbelianChargeSectors.ChargeLabel H)) :
    (∀ z h, eval p (toTorus z, h) = eval q (toTorus z, h)) ↔ p = q := by
  constructor
  · intro he
    apply eval_injective
    rintro ⟨t, h⟩
    obtain ⟨z, rfl⟩ := toTorus_surjective t
    exact he z h
  · rintro rfl
    intros
    rfl

def color (z : Coordinates) : Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  diagonalElement ![z 0, z 1, (z 0 * z 1)⁻¹] (by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one]
    group)

def weak (z : Coordinates) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  diagonalElement ![z 2, (z 2)⁻¹] (by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one]
    group)

def gaugePoint (z : Coordinates) : StandardSMGaugeTensor.GaugeGroup :=
  (color z, weak z, z 3)

/-- The physical coordinates act on actual SM fields by a group homomorphism. -/
def gaugeHom : Coordinates →* StandardSMGaugeTensor.GaugeGroup where
  toFun := gaugePoint
  map_one' := by
    apply Prod.ext
    · apply Subtype.ext
      simp [gaugePoint, color, diagonalElement]
      funext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Subtype.ext
        simp [gaugePoint, weak, diagonalElement]
        funext i
        fin_cases i <;> rfl
      · rfl
  map_mul' z w := by
    apply Prod.ext
    · apply Subtype.ext
      change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]
    · apply Prod.ext
      · apply Subtype.ext
        change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp [mul_comm]
      · rfl

end

end GUT.SU5.PhysicalTorus

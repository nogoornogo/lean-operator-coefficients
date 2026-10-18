import GUT.SU6.SelectionRules.FlippedBranch.ColorNeutralSMGroup
import GUT.SU6.SelectionRules.FlippedBranch.PhysicalRestrictionBridge
import Mathlib.RepresentationTheory.Character

open Math

/-!
# The physical Standard Model target in the color-neutral branch

For the concrete group `SU(3) x U(2)`, the five left-handed Standard Model
multiplets are represented by

* `Q  = 3 tensor 2`,
* `Uc = 3* tensor det^-2`,
* `Dc = 3* tensor det`,
* `L  = 2 tensor det^-2`,
* `Ec = det^3`.

The center of `U(2)` acts on its defining representation with weight one and
on its determinant with weight two.  These formulas therefore give
six-times-hypercharges `1,-4,2,-3,6`, respectively.  This file constructs the
actual finite virtual target, computes its trace on the lifted torus, and
identifies it with `ColorNeutralBranch.colorNeutralSMCharacter`.  The
function-level obstruction then excludes the physical target from the
restriction image of finite virtual `SU(6)` representations.
-/

namespace GUT
namespace ColorNeutralSMTarget

open ColorNeutralSMGroup
open PhysicalRestrictionBridge
open scoped TensorProduct

noncomputable section

abbrev ColorStd := Fin 3 → ℂ
abbrev WeakStd := Fin 2 → ℂ
abbrev DiagonalPoint := ColorNeutralBranch.DiagonalPoint

def colorRho : Representation ℂ Group ColorStd where
  toFun g := Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul
    (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
    (h.1 : Matrix (Fin 3) (Fin 3) ℂ)

def weakRho : Representation ℂ Group WeakStd where
  toFun g := Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul
    (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
    (h.2 : Matrix (Fin 2) (Fin 2) ℂ)

def detValue (n : ℤ) (g : Group) : ℂ :=
  Matrix.det (g.2 : Matrix (Fin 2) (Fin 2) ℂ) ^ n

def detRho (n : ℤ) : Representation ℂ Group ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (detValue n g)
  map_one' := by
    ext
    simp [detValue]
  map_mul' g h := by
    ext
    simp [detValue, Matrix.det_mul, mul_zpow]

theorem detRho_character (n : ℤ) (g : Group) :
    (detRho n).character g = detValue n g := by
  change LinearMap.trace ℂ ℂ
    (LinearMap.lsmul ℂ ℂ (detValue n g)) = detValue n g
  rw [show LinearMap.lsmul ℂ ℂ (detValue n g) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (detValue n g) by
    apply LinearMap.ext
    intro x
    simp [mul_comm]]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) _

theorem colorRho_character (g : Group) :
    colorRho.character g = Matrix.trace (g.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  change LinearMap.trace ℂ ColorStd
    (Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

theorem weakRho_character (g : Group) :
    weakRho.character g = Matrix.trace (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  change LinearMap.trace ℂ WeakStd
    (Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

theorem colorRho_character_torus (t : DiagonalPoint) :
    colorRho.character (torusPoint t) =
      t.coords 0 + t.coords 1 + t.coords 2 := by
  rw [colorRho_character]
  simp [torusPoint, colorPoint, colorMatrix, Matrix.trace_diagonal,
    Fin.sum_univ_three, colorIndex]

theorem weakRho_character_torus (t : DiagonalPoint) :
    weakRho.character (torusPoint t) = t.coords 3 + t.coords 4 := by
  rw [weakRho_character]
  simp [torusPoint, weakPoint, weakMatrix, Matrix.trace_diagonal,
    Fin.sum_univ_two, weakIndex]

theorem colorRho_character_inv_torus (t : DiagonalPoint) :
    colorRho.character (torusPoint t)⁻¹ =
      (t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹ := by
  rw [colorRho_character]
  change Matrix.trace (star (colorMatrix t)) = _
  simp [colorMatrix, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.trace_diagonal,
    Fin.sum_univ_three, colorIndex, star_coord_eq_inv]

theorem weakRho_character_inv_torus (t : DiagonalPoint) :
    weakRho.character (torusPoint t)⁻¹ =
      (t.coords 3)⁻¹ + (t.coords 4)⁻¹ := by
  rw [weakRho_character]
  change Matrix.trace (star (weakMatrix t)) = _
  simp [weakMatrix, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.trace_diagonal,
    Fin.sum_univ_two, weakIndex, star_coord_eq_inv]

theorem detValue_torus (n : ℤ) (t : DiagonalPoint) :
    detValue n (torusPoint t) = (t.coords 3 * t.coords 4) ^ n := by
  simp [detValue, torusPoint, weakPoint, weakMatrix,
    Matrix.det_diagonal, Fin.prod_univ_two, weakIndex]

theorem detValue_inv_torus (n : ℤ) (t : DiagonalPoint) :
    detValue n (torusPoint t)⁻¹ =
      (t.coords 3 * t.coords 4) ^ (-n) := by
  rw [show (torusPoint t)⁻¹ = ((colorPoint t)⁻¹, (weakPoint t)⁻¹) by rfl]
  simp only [detValue, Matrix.UnitaryGroup.inv_val]
  change Matrix.det (star (weakMatrix t)) ^ n = _
  rw [show star (weakMatrix t) =
      Matrix.diagonal (fun i => star (t.coords (weakIndex i))) by
    simp [weakMatrix, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]]
  simp [Matrix.det_diagonal, Fin.prod_univ_two, weakIndex,
    star_coord_eq_inv, zpow_neg, mul_inv_rev]
  have hbase :
      (t.coords 4)⁻¹ * (t.coords 3)⁻¹ =
        (t.coords 3 * t.coords 4)⁻¹ := by
    simp [mul_inv_rev]
  rw [hbase, inv_zpow']
  exact zpow_neg _ _

def actualDual (R : ActualGroupRepresentation Group) :
    ActualGroupRepresentation Group where
  V := Module.Dual ℂ R.V
  rho := R.rho.dual

theorem actualDual_character (R : ActualGroupRepresentation Group) (g : Group) :
    (actualDual R).character g = R.character g⁻¹ := by
  exact Representation.char_dual R.rho g

def Q : ActualGroupRepresentation Group where
  V := ColorStd ⊗[ℂ] WeakStd
  rho := colorRho.tprod weakRho

def Uc : ActualGroupRepresentation Group where
  V := Module.Dual ℂ ColorStd ⊗[ℂ] ℂ
  rho := colorRho.dual.tprod (detRho (-2))

def Dc : ActualGroupRepresentation Group where
  V := Module.Dual ℂ ColorStd ⊗[ℂ] ℂ
  rho := colorRho.dual.tprod (detRho 1)

def L : ActualGroupRepresentation Group where
  V := WeakStd ⊗[ℂ] ℂ
  rho := weakRho.tprod (detRho (-2))

def Ec : ActualGroupRepresentation Group where
  V := ℂ
  rho := detRho 3

def target : FiniteVirtualGroupRepresentation Group :=
  [ ⟨ 1, Q ⟩, ⟨-1, actualDual Q ⟩
  , ⟨ 1, Uc ⟩, ⟨-1, actualDual Uc ⟩
  , ⟨ 1, Dc ⟩, ⟨-1, actualDual Dc ⟩
  , ⟨ 1, L ⟩, ⟨-1, actualDual L ⟩
  , ⟨ 1, Ec ⟩, ⟨-1, actualDual Ec ⟩ ]

theorem tprod_character
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W)
    (g : Group) :
    (rho.tprod sigma).character g = rho.character g * sigma.character g := by
  exact congrFun (Representation.char_tensor rho sigma) g

theorem Q_character_torus (t : DiagonalPoint) :
    Q.character (torusPoint t) =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 3 + t.coords 4) := by
  change (colorRho.tprod weakRho).character (torusPoint t) = _
  rw [tprod_character, colorRho_character_torus, weakRho_character_torus]

theorem Q_character_inv_torus (t : DiagonalPoint) :
    Q.character (torusPoint t)⁻¹ =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        ((t.coords 3)⁻¹ + (t.coords 4)⁻¹) := by
  change (colorRho.tprod weakRho).character (torusPoint t)⁻¹ = _
  rw [tprod_character, colorRho_character_inv_torus,
    weakRho_character_inv_torus]

theorem Uc_character_torus (t : DiagonalPoint) :
    Uc.character (torusPoint t) =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        ((t.coords 3)⁻¹ ^ 2 * (t.coords 4)⁻¹ ^ 2) := by
  change (colorRho.dual.tprod (detRho (-2))).character (torusPoint t) = _
  rw [tprod_character, Representation.char_dual,
    colorRho_character_inv_torus, detRho_character, detValue_torus]
  rw [mul_zpow]
  norm_num [zpow_negSucc]

theorem Uc_character_inv_torus (t : DiagonalPoint) :
    Uc.character (torusPoint t)⁻¹ =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 3 ^ 2 * t.coords 4 ^ 2) := by
  change (colorRho.dual.tprod (detRho (-2))).character (torusPoint t)⁻¹ = _
  rw [tprod_character, Representation.char_dual]
  simp only [inv_inv]
  rw [colorRho_character_torus, detRho_character, detValue_inv_torus]
  rw [mul_zpow]
  norm_num

theorem Dc_character_torus (t : DiagonalPoint) :
    Dc.character (torusPoint t) =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        (t.coords 3 * t.coords 4) := by
  change (colorRho.dual.tprod (detRho 1)).character (torusPoint t) = _
  rw [tprod_character, Representation.char_dual,
    colorRho_character_inv_torus, detRho_character, detValue_torus]
  simp

theorem Dc_character_inv_torus (t : DiagonalPoint) :
    Dc.character (torusPoint t)⁻¹ =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        ((t.coords 3)⁻¹ * (t.coords 4)⁻¹) := by
  change (colorRho.dual.tprod (detRho 1)).character (torusPoint t)⁻¹ = _
  rw [tprod_character, Representation.char_dual]
  simp only [inv_inv]
  rw [colorRho_character_torus, detRho_character, detValue_inv_torus]
  simp [mul_inv_rev, mul_comm]

theorem L_character_torus (t : DiagonalPoint) :
    L.character (torusPoint t) =
      (t.coords 3 + t.coords 4) *
        ((t.coords 3)⁻¹ ^ 2 * (t.coords 4)⁻¹ ^ 2) := by
  change (weakRho.tprod (detRho (-2))).character (torusPoint t) = _
  rw [tprod_character, weakRho_character_torus,
    detRho_character, detValue_torus]
  rw [mul_zpow]
  norm_num [zpow_negSucc]

theorem L_character_inv_torus (t : DiagonalPoint) :
    L.character (torusPoint t)⁻¹ =
      ((t.coords 3)⁻¹ + (t.coords 4)⁻¹) *
        (t.coords 3 ^ 2 * t.coords 4 ^ 2) := by
  change (weakRho.tprod (detRho (-2))).character (torusPoint t)⁻¹ = _
  rw [tprod_character, weakRho_character_inv_torus,
    detRho_character, detValue_inv_torus]
  rw [mul_zpow]
  norm_num

theorem Ec_character_torus (t : DiagonalPoint) :
    Ec.character (torusPoint t) =
      t.coords 3 ^ 3 * t.coords 4 ^ 3 := by
  change (detRho 3).character (torusPoint t) = _
  rw [detRho_character, detValue_torus]
  rw [mul_zpow]
  norm_num

theorem Ec_character_inv_torus (t : DiagonalPoint) :
    Ec.character (torusPoint t)⁻¹ =
      (t.coords 3)⁻¹ ^ 3 * (t.coords 4)⁻¹ ^ 3 := by
  change (detRho 3).character (torusPoint t)⁻¹ = _
  rw [detRho_character, detValue_inv_torus]
  rw [mul_zpow]
  norm_num [zpow_negSucc]

def targetCharacterFormula (t : DiagonalPoint) : ℂ :=
    (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 3 + t.coords 4)
  - ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        ((t.coords 3)⁻¹ + (t.coords 4)⁻¹)
  + ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        ((t.coords 3)⁻¹ ^ 2 * (t.coords 4)⁻¹ ^ 2)
  - (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 3 ^ 2 * t.coords 4 ^ 2)
  + ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        (t.coords 3 * t.coords 4)
  - (t.coords 0 + t.coords 1 + t.coords 2) *
        ((t.coords 3)⁻¹ * (t.coords 4)⁻¹)
  + ((t.coords 3)⁻¹ * (t.coords 4)⁻¹ ^ 2 +
        (t.coords 3)⁻¹ ^ 2 * (t.coords 4)⁻¹)
  - (t.coords 3 * t.coords 4 ^ 2 +
        t.coords 3 ^ 2 * t.coords 4)
  + (t.coords 3 ^ 3 * t.coords 4 ^ 3 -
        (t.coords 3)⁻¹ ^ 3 * (t.coords 4)⁻¹ ^ 3)

theorem target_character_torus_expanded (t : DiagonalPoint) :
    FiniteVirtualGroupRepresentation.character target (torusPoint t) =
      targetCharacterFormula t := by
  simp only [target, FiniteVirtualGroupRepresentation.character,
    VirtualGroupSummand.character, Int.cast_one, one_mul, Int.cast_neg,
    neg_one_mul, actualDual_character]
  rw [Q_character_torus, Q_character_inv_torus,
    Uc_character_torus, Uc_character_inv_torus,
    Dc_character_torus, Dc_character_inv_torus,
    L_character_torus, L_character_inv_torus,
    Ec_character_torus, Ec_character_inv_torus]
  simp [targetCharacterFormula]
  field_simp [t.coord_ne_zero 3, t.coord_ne_zero 4]
  all_goals ring

theorem colorTripletValue_torus (t : DiagonalPoint) :
    ColorNeutralBranch.colorTripletValue t.toAlgebraicTorusPoint =
      t.coords 0 + t.coords 1 + t.coords 2 := by
  rw [ColorNeutralBranch.colorTripletValue]
  simp [ColorNeutralBranch.DiagonalPoint.toAlgebraicTorusPoint,
    ColorNeutralBranch.DiagonalPoint.coordUnit]
  simpa [mul_inv_rev] using t.coord2_eq_inv_colorProduct.symm

theorem colorAntiTripletValue_torus (t : DiagonalPoint) :
    ColorNeutralBranch.colorAntiTripletValue t.toAlgebraicTorusPoint =
      (t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹ := by
  rw [ColorNeutralBranch.colorAntiTripletValue]
  simp [ColorNeutralBranch.DiagonalPoint.toAlgebraicTorusPoint,
    ColorNeutralBranch.DiagonalPoint.coordUnit]
  have h := congrArg Inv.inv t.coord2_eq_inv_colorProduct
  simp at h
  rw [h]

theorem canonical_target_eval_expanded (t : DiagonalPoint) :
    ColorNeutralBranch.diagonalLaurentEval
        ColorNeutralBranch.colorNeutralSMCharacter t =
      targetCharacterFormula t := by
  unfold ColorNeutralBranch.diagonalLaurentEval
  rw [ColorNeutralBranch.colorNeutralSMCharacter_eval,
    ColorNeutralBranch.qCharacter_eval,
    ColorNeutralBranch.upCharacter_eval,
    ColorNeutralBranch.downCharacter_eval,
    ColorNeutralBranch.leptonCharacter_eval,
    ColorNeutralBranch.electronCharacter_eval,
    colorTripletValue_torus, colorAntiTripletValue_torus]
  simp [ColorNeutralBranch.DiagonalPoint.toAlgebraicTorusPoint,
    ColorNeutralBranch.DiagonalPoint.coordUnit, targetCharacterFormula]
  ring

theorem target_character_torus (t : DiagonalPoint) :
    FiniteVirtualGroupRepresentation.character target (torusPoint t) =
      ColorNeutralBranch.diagonalLaurentEval
        ColorNeutralBranch.colorNeutralSMCharacter t := by
  rw [target_character_torus_expanded, canonical_target_eval_expanded]

theorem restrictVirtual_character_on_torus
    (chi : VirtualRestriction.FiniteVirtualSU6Representation)
    (t : DiagonalPoint) :
    FiniteVirtualGroupRepresentation.character
        (restrictVirtual embedding chi) (torusPoint t) =
      ColorNeutralBranch.restrictedCharacter chi t := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp only [restrictVirtual, FiniteVirtualGroupRepresentation.character,
        VirtualGroupSummand.character, restrictSummand, restrictActual,
        ColorNeutralBranch.restrictedCharacter]
      change
        (s.coeff : ℂ) * s.rep.rho.character (embedding (torusPoint t)) +
            FiniteVirtualGroupRepresentation.character
              (restrictVirtual embedding ss) (torusPoint t) =
          (s.coeff : ℂ) * s.rep.rho.character t.toDiagonal.toSU6 +
            ColorNeutralBranch.restrictedCharacter ss t
      rw [embedding_torusPoint, ih]

/-- No finite virtual `SU(6)` representation restricts to the actual
one-generation color-neutral Standard Model target character. -/
theorem no_colorNeutralSMTarget_characterEquivalent_restriction :
    ¬ ∃ chi : VirtualRestriction.FiniteVirtualSU6Representation,
      FiniteVirtualGroupRepresentation.CharacterEquivalent
        (restrictVirtual embedding chi) target := by
  intro h
  rcases h with ⟨chi, hchi⟩
  apply ColorNeutralBranch.no_colorNeutralSM_uplift
  refine ⟨chi, fun t => ?_⟩
  calc
    ColorNeutralBranch.restrictedCharacter chi t =
        FiniteVirtualGroupRepresentation.character
          (restrictVirtual embedding chi) (torusPoint t) :=
      (restrictVirtual_character_on_torus chi t).symm
    _ = FiniteVirtualGroupRepresentation.character target (torusPoint t) :=
      hchi (torusPoint t)
    _ = ColorNeutralBranch.diagonalLaurentEval
          ColorNeutralBranch.colorNeutralSMCharacter t :=
      target_character_torus t

end


end ColorNeutralSMTarget
end GUT

import GUT.SU6.SelectionRules.FlippedBranch.FlippedSMGroup
import Mathlib.RepresentationTheory.Character

open Math

/-!
# The physical flipped Standard Model target

This file constructs the one-generation chiral target as an actual finite
virtual representation of the concrete group `U(3) x SU(2)`.  The five
particle representations are

* `Q  = 3 tensor 2`,
* `Uc = 3* tensor det^-1`,
* `Dc = 3* tensor det`,
* `L  = 2 tensor det^-1`,
* `Ec = det^2`.

Subtracting the dual of each representation gives the chiral character.  Its
trace on the lifted flipped torus is proved equal to the canonical normalized
Laurent target, closing the concrete target side of the restriction bridge.
-/

namespace GUT
namespace FlippedSMTarget

open FlippedSMGroup
open PhysicalRestrictionBridge
open scoped TensorProduct

noncomputable section

abbrev ColorStd := Fin 3 -> ℂ
abbrev WeakStd := Fin 2 -> ℂ

/-- The defining `U(3)` representation, inflated to the product group. -/
def colorRho : Representation ℂ Group ColorStd where
  toFun g := Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul
    (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
    (h.1 : Matrix (Fin 3) (Fin 3) ℂ)

/-- The defining `SU(2)` representation, inflated to the product group. -/
def weakRho : Representation ℂ Group WeakStd where
  toFun g := Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul
    (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
    (h.2 : Matrix (Fin 2) (Fin 2) ℂ)

def detValue (n : ℤ) (g : Group) : ℂ :=
  Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) ^ n

/-- The one-dimensional representation `det^n` of the `U(3)` factor. -/
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
    colorRho.character g =
      Matrix.trace (g.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  change LinearMap.trace ℂ ColorStd
    (Matrix.toLin' (g.1 : Matrix (Fin 3) (Fin 3) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

theorem weakRho_character (g : Group) :
    weakRho.character g =
      Matrix.trace (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  change LinearMap.trace ℂ WeakStd
    (Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

theorem colorRho_character_torus (t : EmbeddedFlippedTorus) :
    colorRho.character (torusPoint t) =
      t.coords 0 + t.coords 1 + t.coords 2 := by
  rw [colorRho_character]
  simp [torusPoint, colorPoint, colorMatrix, Matrix.trace_diagonal,
    Fin.sum_univ_three, colorIndex]

theorem weakRho_character_torus (t : EmbeddedFlippedTorus) :
    weakRho.character (torusPoint t) = t.coords 3 + t.coords 4 := by
  rw [weakRho_character]
  simp [torusPoint, weakPoint, weakMatrix, Matrix.trace_diagonal,
    Fin.sum_univ_two, weakIndex]

theorem colorRho_character_inv_torus (t : EmbeddedFlippedTorus) :
    colorRho.character (torusPoint t)⁻¹ =
      (t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹ := by
  rw [colorRho_character]
  simp [torusPoint, colorPoint, colorMatrix, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.trace_diagonal, Fin.sum_univ_three, colorIndex, star_coord_eq_inv]

theorem weakRho_character_inv_torus (t : EmbeddedFlippedTorus) :
    weakRho.character (torusPoint t)⁻¹ = t.coords 3 + t.coords 4 := by
  rw [weakRho_character]
  change Matrix.trace (star (weakMatrix t)) = _
  simp [weakMatrix, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.trace_diagonal,
    Fin.sum_univ_two, weakIndex, star_coord_eq_inv]
  have h3 : (t.coords 3)⁻¹ = t.coords 4 :=
    (eq_inv_of_mul_eq_one_right t.weak_relation).symm
  have h4 : (t.coords 4)⁻¹ = t.coords 3 :=
    (eq_inv_of_mul_eq_one_left t.weak_relation).symm
  rw [h3, h4, add_comm]

theorem detValue_torus (n : ℤ) (t : EmbeddedFlippedTorus) :
    detValue n (torusPoint t) =
      (t.coords 0 * t.coords 1 * t.coords 2) ^ n := by
  simp [detValue, torusPoint, colorPoint, colorMatrix,
    Matrix.det_diagonal, Fin.prod_univ_three, colorIndex]

theorem detValue_inv_torus (n : ℤ) (t : EmbeddedFlippedTorus) :
    detValue n (torusPoint t)⁻¹ =
      (t.coords 0 * t.coords 1 * t.coords 2) ^ (-n) := by
  rw [show (torusPoint t)⁻¹ = ((colorPoint t)⁻¹, (weakPoint t)⁻¹) by rfl]
  simp only [detValue, Matrix.UnitaryGroup.inv_val]
  change Matrix.det (star (colorMatrix t)) ^ n = _
  rw [show star (colorMatrix t) =
      Matrix.diagonal (fun i => star (t.coords (colorIndex i))) by
    simp [colorMatrix, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]]
  simp [Matrix.det_diagonal, Fin.prod_univ_three, colorIndex,
    star_coord_eq_inv, zpow_neg, mul_inv_rev]
  have hbase :
      (t.coords 2)⁻¹ * ((t.coords 1)⁻¹ * (t.coords 0)⁻¹) =
        (t.coords 0 * t.coords 1 * t.coords 2)⁻¹ := by
    simp [mul_inv_rev, mul_comm]
  rw [hbase, inv_zpow']
  exact zpow_neg _ _

/-- Package the contragredient of an actual finite-dimensional representation. -/
def actualDual (R : ActualGroupRepresentation Group) :
    ActualGroupRepresentation Group where
  V := Module.Dual ℂ R.V
  rho := R.rho.dual

theorem actualDual_character (R : ActualGroupRepresentation Group) (g : Group) :
    (actualDual R).character g = R.character g⁻¹ := by
  exact Representation.char_dual R.rho g

/-- Quark doublet `(3,2)`. -/
def Q : ActualGroupRepresentation Group where
  V := ColorStd ⊗[ℂ] WeakStd
  rho := colorRho.tprod weakRho

/-- Up antiquark `3* tensor det^-1`. -/
def Uc : ActualGroupRepresentation Group where
  V := Module.Dual ℂ ColorStd ⊗[ℂ] ℂ
  rho := colorRho.dual.tprod (detRho (-1))

/-- Down antiquark `3* tensor det`. -/
def Dc : ActualGroupRepresentation Group where
  V := Module.Dual ℂ ColorStd ⊗[ℂ] ℂ
  rho := colorRho.dual.tprod (detRho 1)

/-- Lepton doublet `2 tensor det^-1`. -/
def L : ActualGroupRepresentation Group where
  V := WeakStd ⊗[ℂ] ℂ
  rho := weakRho.tprod (detRho (-1))

/-- Charged antilepton `det^2`. -/
def Ec : ActualGroupRepresentation Group where
  V := ℂ
  rho := detRho 2

/-- One physical generation, represented as the sum of `R - R*` for five fields. -/
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

theorem Q_character_torus (t : EmbeddedFlippedTorus) :
    Q.character (torusPoint t) =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 3 + t.coords 4) := by
  change (colorRho.tprod weakRho).character (torusPoint t) = _
  rw [tprod_character, colorRho_character_torus, weakRho_character_torus]

theorem Q_character_inv_torus (t : EmbeddedFlippedTorus) :
    Q.character (torusPoint t)⁻¹ =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        (t.coords 3 + t.coords 4) := by
  change (colorRho.tprod weakRho).character (torusPoint t)⁻¹ = _
  rw [tprod_character, colorRho_character_inv_torus,
    weakRho_character_inv_torus]

theorem Uc_character_torus (t : EmbeddedFlippedTorus) :
    Uc.character (torusPoint t) =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        (t.coords 0 * t.coords 1 * t.coords 2)⁻¹ := by
  change (colorRho.dual.tprod (detRho (-1))).character (torusPoint t) = _
  rw [tprod_character, Representation.char_dual,
    colorRho_character_inv_torus, detRho_character, detValue_torus]
  simp

theorem Uc_character_inv_torus (t : EmbeddedFlippedTorus) :
    Uc.character (torusPoint t)⁻¹ =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 0 * t.coords 1 * t.coords 2) := by
  change (colorRho.dual.tprod (detRho (-1))).character (torusPoint t)⁻¹ = _
  rw [tprod_character, Representation.char_dual]
  simp only [inv_inv]
  rw [colorRho_character_torus, detRho_character, detValue_inv_torus]
  simp

theorem Dc_character_torus (t : EmbeddedFlippedTorus) :
    Dc.character (torusPoint t) =
      ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
        (t.coords 0 * t.coords 1 * t.coords 2) := by
  change (colorRho.dual.tprod (detRho 1)).character (torusPoint t) = _
  rw [tprod_character, Representation.char_dual,
    colorRho_character_inv_torus, detRho_character, detValue_torus]
  simp

theorem Dc_character_inv_torus (t : EmbeddedFlippedTorus) :
    Dc.character (torusPoint t)⁻¹ =
      (t.coords 0 + t.coords 1 + t.coords 2) *
        (t.coords 0 * t.coords 1 * t.coords 2)⁻¹ := by
  change (colorRho.dual.tprod (detRho 1)).character (torusPoint t)⁻¹ = _
  rw [tprod_character, Representation.char_dual]
  simp only [inv_inv]
  rw [colorRho_character_torus, detRho_character, detValue_inv_torus]
  simp

theorem L_character_torus (t : EmbeddedFlippedTorus) :
    L.character (torusPoint t) =
      (t.coords 3 + t.coords 4) *
        (t.coords 0 * t.coords 1 * t.coords 2)⁻¹ := by
  change (weakRho.tprod (detRho (-1))).character (torusPoint t) = _
  rw [tprod_character, weakRho_character_torus,
    detRho_character, detValue_torus]
  simp

theorem L_character_inv_torus (t : EmbeddedFlippedTorus) :
    L.character (torusPoint t)⁻¹ =
      (t.coords 3 + t.coords 4) *
        (t.coords 0 * t.coords 1 * t.coords 2) := by
  change (weakRho.tprod (detRho (-1))).character (torusPoint t)⁻¹ = _
  rw [tprod_character, weakRho_character_inv_torus,
    detRho_character, detValue_inv_torus]
  simp

theorem Ec_character_torus (t : EmbeddedFlippedTorus) :
    Ec.character (torusPoint t) =
      (t.coords 0 * t.coords 1 * t.coords 2) ^ (2 : ℤ) := by
  change (detRho 2).character (torusPoint t) = _
  rw [detRho_character, detValue_torus]

theorem Ec_character_inv_torus (t : EmbeddedFlippedTorus) :
    Ec.character (torusPoint t)⁻¹ =
      (t.coords 0 * t.coords 1 * t.coords 2) ^ (-2 : ℤ) := by
  change (detRho 2).character (torusPoint t)⁻¹ = _
  rw [detRho_character, detValue_inv_torus]

theorem target_character_torus_expanded (t : EmbeddedFlippedTorus) :
    FiniteVirtualGroupRepresentation.character target (torusPoint t) =
      (t.coords 0 + t.coords 1 + t.coords 2) * (t.coords 3 + t.coords 4)
      - ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
          (t.coords 3 + t.coords 4)
      + ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ +
            (t.coords 0 * t.coords 1 * t.coords 2))
      - (t.coords 0 + t.coords 1 + t.coords 2) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ +
            (t.coords 0 * t.coords 1 * t.coords 2))
      + (t.coords 3 + t.coords 4) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ -
            (t.coords 0 * t.coords 1 * t.coords 2))
      + ((t.coords 0 * t.coords 1 * t.coords 2) ^ (2 : ℤ) -
          (t.coords 0 * t.coords 1 * t.coords 2) ^ (-2 : ℤ)) := by
  simp only [target, FiniteVirtualGroupRepresentation.character,
    VirtualGroupSummand.character, Int.cast_one, one_mul, Int.cast_neg,
    neg_one_mul, actualDual_character]
  rw [Q_character_torus, Q_character_inv_torus,
    Uc_character_torus, Uc_character_inv_torus,
    Dc_character_torus, Dc_character_inv_torus,
    L_character_torus, L_character_inv_torus,
    Ec_character_torus, Ec_character_inv_torus]
  ring

theorem legacy_colorTriplet_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.colorTriplet x =
      (x.z1 : ℂ) + x.z2 + x.z3 := by
  simp [Flipped.colorTriplet, Flipped.z1, Flipped.z2, Flipped.z3,
    Flipped.Poly.eval_add, Flipped.Poly.eval_mon]

theorem legacy_colorAntiTriplet_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.colorAntiTriplet x =
      (x.z1 : ℂ)⁻¹ + (x.z2 : ℂ)⁻¹ + (x.z3 : ℂ)⁻¹ := by
  simp [Flipped.colorAntiTriplet, Flipped.invZ1, Flipped.invZ2,
    Flipped.invZ3, Flipped.Poly.eval_add, Flipped.Poly.eval_mon]

theorem legacy_weakDoublet_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.weakDoublet x =
      (x.z4 : ℂ) + (x.z4 : ℂ)⁻¹ := by
  simp [Flipped.weakDoublet, Flipped.z4, Flipped.z5,
    Flipped.Poly.eval_add, Flipped.Poly.eval_mon]

theorem legacy_z6_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.z6 x =
      ((x.z1 : ℂ) * x.z2 * x.z3)⁻¹ := by
  simp [Flipped.z6, Flipped.Poly.eval_mon, mul_inv_rev]
  ring

theorem legacy_invZ6_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.invZ6 x =
      (x.z1 : ℂ) * x.z2 * x.z3 := by
  simp [Flipped.invZ6, Flipped.Poly.eval_mon]

theorem legacy_flippedSMCharacterExplicit_eval
    (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Poly.eval Flipped.flippedSMCharacterExplicit x =
      ((x.z1 : ℂ) + x.z2 + x.z3) * (x.z4 + (x.z4 : ℂ)⁻¹)
      - ((x.z1 : ℂ)⁻¹ + (x.z2 : ℂ)⁻¹ + (x.z3 : ℂ)⁻¹) *
          (x.z4 + (x.z4 : ℂ)⁻¹)
      + ((x.z1 : ℂ)⁻¹ + (x.z2 : ℂ)⁻¹ + (x.z3 : ℂ)⁻¹) *
          (((x.z1 : ℂ) * x.z2 * x.z3)⁻¹ +
            ((x.z1 : ℂ) * x.z2 * x.z3))
      - ((x.z1 : ℂ) + x.z2 + x.z3) *
          (((x.z1 : ℂ) * x.z2 * x.z3)⁻¹ +
            ((x.z1 : ℂ) * x.z2 * x.z3))
      + (x.z4 + (x.z4 : ℂ)⁻¹) *
          (((x.z1 : ℂ) * x.z2 * x.z3)⁻¹ -
            ((x.z1 : ℂ) * x.z2 * x.z3))
      + (((x.z1 : ℂ) * x.z2 * x.z3) ^ (2 : ℤ) -
          ((x.z1 : ℂ) * x.z2 * x.z3) ^ (-2 : ℤ)) := by
  simp only [Flipped.flippedSMCharacterExplicit, Flipped.Poly.eval_add,
    Flipped.Poly.eval_sub, Flipped.Poly.eval_mul,
    legacy_colorTriplet_eval, legacy_colorAntiTriplet_eval,
    legacy_weakDoublet_eval, legacy_z6_eval, legacy_invZ6_eval]
  norm_num [zpow_ofNat, zpow_negSucc]
  ring

theorem canonical_target_eval_expanded (t : EmbeddedFlippedTorus) :
    NormalizedVirtualRestriction.diagonalLaurentEval
        Flipped.Normalized.flippedSMCharacter t =
      (t.coords 0 + t.coords 1 + t.coords 2) * (t.coords 3 + t.coords 4)
      - ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
          (t.coords 3 + t.coords 4)
      + ((t.coords 0)⁻¹ + (t.coords 1)⁻¹ + (t.coords 2)⁻¹) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ +
            (t.coords 0 * t.coords 1 * t.coords 2))
      - (t.coords 0 + t.coords 1 + t.coords 2) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ +
            (t.coords 0 * t.coords 1 * t.coords 2))
      + (t.coords 3 + t.coords 4) *
          ((t.coords 0 * t.coords 1 * t.coords 2)⁻¹ -
            (t.coords 0 * t.coords 1 * t.coords 2))
      + ((t.coords 0 * t.coords 1 * t.coords 2) ^ (2 : ℤ) -
          (t.coords 0 * t.coords 1 * t.coords 2) ^ (-2 : ℤ)) := by
  unfold NormalizedVirtualRestriction.diagonalLaurentEval
  change Flipped.Normalized.eval
    Flipped.Normalized.flippedSMCharacterExplicit _ = _
  rw [← Flipped.Normalized.legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit]
  change Flipped.Normalized.eval
    (Flipped.Normalized.ofListPoly Flipped.flippedSMCharacterExplicit) _ = _
  rw [Flipped.Normalized.eval_ofListPoly,
    legacy_flippedSMCharacterExplicit_eval]
  simp [FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint,
    FlippedTorus.FlippedDiagonalSU6Point.coordUnit]
  have hweak : (t.coords 3)⁻¹ = t.coords 4 :=
    (eq_inv_of_mul_eq_one_right t.weak_relation).symm
  rw [hweak]

/-- The actual physical target has exactly the canonical Laurent character. -/
theorem target_character_torus (t : EmbeddedFlippedTorus) :
    FiniteVirtualGroupRepresentation.character target (torusPoint t) =
      NormalizedVirtualRestriction.diagonalLaurentEval
        Flipped.Normalized.flippedSMCharacter t := by
  rw [target_character_torus_expanded, canonical_target_eval_expanded]

/-- No finite virtual `SU(6)` representation restricts to the physical target character. -/
theorem no_flippedSMTarget_characterEquivalent_restriction :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      FiniteVirtualGroupRepresentation.CharacterEquivalent
        (restrictVirtual embedding chi) target :=
  PhysicalRestrictionBridge.no_flippedSMTarget_characterEquivalent_restriction
    flippedTorusLift target target_character_torus

/-- Function-image form of the concrete physical no-uplift theorem. -/
theorem flippedSMTarget_character_not_mem_restrictionImage :
    FiniteVirtualGroupRepresentation.character target ∉
      Set.range (fun chi : FiniteVirtualSU6Representation =>
        FiniteVirtualGroupRepresentation.character
          (restrictVirtual embedding chi)) :=
  PhysicalRestrictionBridge.flippedSMTarget_character_not_mem_restrictionImage
    flippedTorusLift target target_character_torus

end

end FlippedSMTarget
end GUT

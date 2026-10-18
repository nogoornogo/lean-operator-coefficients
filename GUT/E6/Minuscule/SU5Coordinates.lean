import Math.LieGroups.E6.Minuscule.D5Blocks
import GUT.SU5.Representations.UnitaryMatter

open Math

/-!
# Signed SU(5) coordinates of the minuscule E6 matrices

The A4 chain is oriented as [5,4,3,2]. This file compares concrete generator
matrices; it does not assert a compact-group inclusion or global E6 identification.
-/

set_option autoImplicit false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open scoped Matrix

abbrev Pair := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev Index := Fin 2 ⊕ Fin 5 ⊕ (Fin 2 × Fin 5) ⊕ Pair

def node : Fin 4 → Fin 6 := ![5, 4, 3, 2]

def coordinate : Index → Fin 27
  | .inl i => ![0, 20] i
  | .inr (.inl i) => ![12, 15, 17, 19, 22] i
  | .inr (.inr (.inl (k, i))) => ![![7, 5, 3, 2, 1], ![26, 25, 24, 23, 21]] k i
  | .inr (.inr (.inr p)) =>
      ![![0, 4, 6, 8, 10], ![0, 0, 9, 11, 13], ![0, 0, 0, 14, 16],
        ![0, 0, 0, 0, 18], ![0, 0, 0, 0, 0]] p.val.1 p.val.2

def sign : Index → ℤ
  | .inr (.inr (.inl (_, i))) => ![1, -1, 1, -1, 1] i
  | _ => 1

theorem coordinate_bijective : Function.Bijective coordinate := by
  decide +kernel

theorem sign_sq (a : Index) : sign a * sign a = 1 := by
  revert a
  decide +kernel

def modelGrade : Index → ℤ
  | .inl i => ![4, 1] i
  | .inr (.inl _) => -2
  | .inr (.inr (.inl (k, _))) => ![1, -2] k
  | .inr (.inr (.inr _)) => 1

theorem coordinate_grade (a : Index) : grade (coordinate a) = modelGrade a := by
  decide +kernel +revert

section Matrices

variable {R : Type*} [CommRing R]

/-- The Leibniz action on an increasing two-fold exterior basis. -/
def wedgeMatrix (X : Matrix (Fin 5) (Fin 5) R) : Matrix Pair Pair R := fun a b =>
  X a.val.1 b.val.1 * (if a.val.2 = b.val.2 then 1 else 0) +
    (if a.val.1 = b.val.1 then 1 else 0) * X a.val.2 b.val.2 -
    X a.val.1 b.val.2 * (if a.val.2 = b.val.1 then 1 else 0) -
    (if a.val.1 = b.val.2 then 1 else 0) * X a.val.2 b.val.1

/-- Two trivial lines, a five, two dual fives, and an exterior square. -/
def blockMatrix (X : Matrix (Fin 5) (Fin 5) R) : Matrix Index Index R
  | .inr (.inl a), .inr (.inl b) => X a b
  | .inr (.inr (.inl (k, a))), .inr (.inr (.inl (l, b))) =>
      if k = l then -X b a else 0
  | .inr (.inr (.inr a)), .inr (.inr (.inr b)) => wedgeMatrix X a b
  | _, _ => 0

theorem wedgeMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (X : Matrix (Fin 5) (Fin 5) R) (a b : Pair) :
    wedgeMatrix (X.map f) a b = f (wedgeMatrix X a b) := by
  dsimp only [wedgeMatrix, Matrix.map_apply]
  simp only [map_add, map_sub, map_mul, apply_ite f, map_one, map_zero]

theorem blockMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (X : Matrix (Fin 5) (Fin 5) R) (a b : Index) :
    blockMatrix (X.map f) a b = f (blockMatrix X a b) := by
  rcases a with a | a | ⟨k, a⟩ | a <;>
    rcases b with b | b | ⟨l, b⟩ | b <;>
    simp only [blockMatrix, Matrix.map_apply, map_zero, map_neg, apply_ite f,
      wedgeMatrix_map]

end Matrices

def fundamentalGenerator (k : Fin 3) (i : Fin 4) : Matrix (Fin 5) (Fin 5) ℤ :=
  ![Matrix.single i.castSucc i.succ 1, Matrix.single i.succ i.castSucc 1,
    Matrix.single i.castSucc i.castSucc 1 - Matrix.single i.succ i.succ 1] k

def integralGenerator (k : Fin 3) (i : Fin 4) : Matrix (Fin 27) (Fin 27) ℤ :=
  ![TauCeti.E6Minuscule.raisingMatrix (node i),
    TauCeti.E6Minuscule.loweringMatrix (node i),
    TauCeti.E6Minuscule.cartanGeneratorMatrix (node i)] k

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem integral_generator_comparison (k : Fin 3) (i : Fin 4) (a b : Index) :
    sign a * integralGenerator k i (coordinate a) (coordinate b) * sign b =
      blockMatrix (fundamentalGenerator k i) a b := by
  revert k i a b
  dsimp only [integralGenerator, fundamentalGenerator, blockMatrix, wedgeMatrix]
  decide +kernel

noncomputable section

def coordinateEquiv : Index ≃ Fin 27 := Equiv.ofBijective coordinate coordinate_bijective

@[simp] theorem coordinateEquiv_apply (a : Index) : coordinateEquiv a = coordinate a := rfl

theorem sign_sq_complex (a : Index) : (sign a : ℂ) * (sign a : ℂ) = 1 := by
  exact_mod_cast sign_sq a

/-- An explicit signed permutation, not a basis chosen by dimension. -/
def signedCoordinates : (Fin 27 → ℂ) ≃ₗ[ℂ] (Index → ℂ) where
  toFun x a := (sign a : ℂ) * x (coordinateEquiv a)
  invFun y j := (sign (coordinateEquiv.symm j) : ℂ) * y (coordinateEquiv.symm j)
  left_inv x := by
    funext j
    simp only [Equiv.apply_symm_apply, ← mul_assoc, sign_sq_complex, one_mul]
  right_inv y := by
    funext a
    simp only [Equiv.symm_apply_apply, ← mul_assoc, sign_sq_complex, one_mul]
  map_add' x y := by ext a; exact mul_add _ _ _
  map_smul' z x := by ext a; exact mul_left_comm _ _ _

theorem signedCoordinates_hermitian (x y : Fin 27 → ℂ) :
    (∑ a : Index, star (signedCoordinates x a) * signedCoordinates y a) =
      ∑ j : Fin 27, star (x j) * y j := by
  change (∑ a : Index, star ((sign a : ℂ) * x (coordinateEquiv a)) *
    ((sign a : ℂ) * y (coordinateEquiv a))) = _
  simp only [star_mul, star_intCast]
  calc
    _ = ∑ a : Index, star (x (coordinateEquiv a)) * y (coordinateEquiv a) := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ((sign a : ℂ) * (sign a : ℂ)) *
            (star (x (coordinateEquiv a)) * y (coordinateEquiv a)) := by ring
        _ = _ := by rw [sign_sq_complex, one_mul]
    _ = _ := coordinateEquiv.sum_comp (fun j => star (x j) * y j)

def complexGenerator (k : Fin 3) (i : Fin 4) : Matrix27 :=
  TauCeti.matrixIntCastLieHom ℂ (integralGenerator k i)

theorem complex_generator_comparison (k : Fin 3) (i : Fin 4) (a b : Index) :
    (sign a : ℂ) * complexGenerator k i (coordinate a) (coordinate b) * (sign b : ℂ) =
      blockMatrix ((fundamentalGenerator k i).map (Int.castRingHom ℂ)) a b := by
  rw [blockMatrix_map]
  simp only [complexGenerator, TauCeti.matrixIntCastLieHom_apply]
  simpa only [map_mul, Int.coe_castRingHom] using
    congrArg (Int.castRingHom ℂ) (integral_generator_comparison k i a b)

theorem generator_intertwining (k : Fin 3) (i : Fin 4) (v : Fin 27 → ℂ) :
    signedCoordinates (complexGenerator k i *ᵥ v) =
      blockMatrix ((fundamentalGenerator k i).map (Int.castRingHom ℂ)) *ᵥ
        signedCoordinates v := by
  funext a
  change (sign a : ℂ) * (∑ j, complexGenerator k i (coordinate a) j * v j) = _
  rw [← coordinateEquiv.sum_comp (fun j => complexGenerator k i (coordinate a) j * v j),
    Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro b _
  rw [← complex_generator_comparison]
  change _ = ((sign a : ℂ) * _ * (sign b : ℂ)) * ((sign b : ℂ) * v (coordinate b))
  rw [mul_assoc ((sign a : ℂ) * _), ← mul_assoc (sign b : ℂ), sign_sq_complex, one_mul]
  exact (mul_assoc _ _ _).symm

end

end GUT.E6.Minuscule.SU5Coordinates

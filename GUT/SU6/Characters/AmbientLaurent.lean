import GUT.SU6.Characters.ActualRestriction
import GUT.SU6.Characters.AmbientWeightLattice
import GUT.SU6.Characters.SignedWeylTransposition
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open Math

/-!
# Faithful Laurent evaluation on the full diagonal SU(6) torus

This file evaluates the canonical rank-five exponent lattice from
`AmbientWeightLattice` on `(Complex.units)^5`.  Restricting to five independent
circle coordinates gives actual determinant-one diagonal `SU(6)` matrices.
Multivariable Fourier independence proves that evaluation on this compact
maximal torus is faithful.
-/

open scoped BigOperators

namespace GUT
namespace AmbientLaurent

open AmbientWeightLattice

noncomputable section

abbrev TorusVec := I5 -> ℂˣ
abbrev Poly := AmbientWeightLattice.Character

namespace Exponent

def evalUnit (e : Exponent) (x : TorusVec) : ℂˣ :=
  ∏ i, x i ^ e i

def eval (e : Exponent) (x : TorusVec) : ℂ :=
  (evalUnit e x : ℂ)

end Exponent

/-- Evaluation of a normalized finite Laurent character. -/
def eval (p : Poly) (x : TorusVec) : ℂ :=
  p.sum fun e c => (c : ℂ) * Exponent.eval e x

theorem eval_zero (x : TorusVec) :
    eval (0 : Poly) x = 0 := by
  simp [eval]

theorem eval_add (p q : Poly) (x : TorusVec) :
    eval (p + q) x = eval p x + eval q x := by
  rw [eval, eval, eval, Finsupp.sum_add_index]
  · intro e _he
    simp
  · intro e _he a b
    rw [Int.cast_add]
    ring

def zscale (n : ℤ) (p : Poly) : Poly :=
  Finsupp.mapRange (fun c : ℤ => n * c) (by simp) p

@[simp]
theorem zscale_apply (n : ℤ) (p : Poly) (e : Exponent) :
    zscale n p e = n * p e := by
  simp [zscale]

theorem eval_zscale (n : ℤ) (p : Poly) (x : TorusVec) :
    eval (zscale n p) x = (n : ℂ) * eval p x := by
  rw [eval, zscale, Finsupp.sum_mapRange_index]
  · calc
      p.sum (fun e c => ((n * c : ℤ) : ℂ) * Exponent.eval e x) =
          p.sum (fun e c =>
            (n : ℂ) * ((c : ℂ) * Exponent.eval e x)) := by
        apply Finsupp.sum_congr
        intro e _he
        rw [Int.cast_mul]
        ring
      _ = (n : ℂ) *
          p.sum (fun e c => (c : ℂ) * Exponent.eval e x) := by
        simpa using
          (Finsupp.mul_sum (n : ℂ) p
            (f := fun e c => (c : ℂ) * Exponent.eval e x)).symm
  · intro e
    simp

def torusVecOfUnitAddTorus (x : UnitAddTorus I5) : TorusVec :=
  fun i => Circle.toUnits (AddCircle.toCircle (x i))

namespace Fourier

def exponentMonoidHom
    (e : Exponent) : Multiplicative (UnitAddTorus I5) →* ℂ where
  toFun x := UnitAddTorus.mFourier e (Multiplicative.toAdd x)
  map_one' := by
    simp [UnitAddTorus.mFourier]
  map_mul' := by
    intro x y
    simp [UnitAddTorus.mFourier, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]

theorem mFourier_injective :
    Function.Injective (UnitAddTorus.mFourier (d := I5)) := by
  intro m n h
  have hLp :
      UnitAddTorus.mFourierLp (d := I5) 2 m =
        UnitAddTorus.mFourierLp (d := I5) 2 n := by
    dsimp [UnitAddTorus.mFourierLp]
    rw [h]
  exact (UnitAddTorus.orthonormal_mFourier (d := I5)).linearIndependent.injective hLp

theorem exponentMonoidHom_injective :
    Function.Injective exponentMonoidHom := by
  intro e f h
  apply mFourier_injective
  ext x
  have hx := congrArg
    (fun phi : Multiplicative (UnitAddTorus I5) →* ℂ =>
      phi (Multiplicative.ofAdd x)) h
  change
    UnitAddTorus.mFourier e
        (Multiplicative.toAdd (Multiplicative.ofAdd x)) =
      UnitAddTorus.mFourier f
        (Multiplicative.toAdd (Multiplicative.ofAdd x)) at hx
  simpa using hx

theorem linearIndependent_exponentMonoidHom :
    LinearIndependent ℂ
      (fun e : Exponent =>
        (exponentMonoidHom e :
          Multiplicative (UnitAddTorus I5) -> ℂ)) := by
  exact (linearIndependent_monoidHom
      (Multiplicative (UnitAddTorus I5)) ℂ).comp
    exponentMonoidHom exponentMonoidHom_injective

def toComplex (p : Poly) : Exponent →₀ ℂ :=
  Finsupp.mapRange (fun n : ℤ => (n : ℂ)) (by simp) p

@[simp]
theorem toComplex_apply (p : Poly) (e : Exponent) :
    toComplex p e = (p e : ℂ) := by
  simp [toComplex]

def evalUnitAddTorus (p : Poly) (x : UnitAddTorus I5) : ℂ :=
  p.sum fun e c => (c : ℂ) * UnitAddTorus.mFourier e x

theorem evalUnitAddTorus_eq_linearCombination (p : Poly) :
    Finsupp.linearCombination ℂ
        (fun e : Exponent =>
          (exponentMonoidHom e :
            Multiplicative (UnitAddTorus I5) -> ℂ))
        (toComplex p) =
      fun x => evalUnitAddTorus p (Multiplicative.toAdd x) := by
  ext x
  rw [Finsupp.linearCombination_apply, toComplex,
    Finsupp.sum_mapRange_index]
  · simp only [evalUnitAddTorus, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro e _he
    rfl
  · intro e
    simp

theorem evalUnitAddTorus_faithful :
    ∀ p q : Poly,
      (∀ x : UnitAddTorus I5,
        evalUnitAddTorus p x = evalUnitAddTorus q x) -> p = q := by
  intro p q h
  have hlin :
      Finsupp.linearCombination ℂ
          (fun e : Exponent =>
            (exponentMonoidHom e :
              Multiplicative (UnitAddTorus I5) -> ℂ))
          (toComplex p) =
        Finsupp.linearCombination ℂ
          (fun e : Exponent =>
            (exponentMonoidHom e :
              Multiplicative (UnitAddTorus I5) -> ℂ))
          (toComplex q) := by
    rw [evalUnitAddTorus_eq_linearCombination p,
      evalUnitAddTorus_eq_linearCombination q]
    funext x
    exact h (Multiplicative.toAdd x)
  have hC : toComplex p = toComplex q :=
    linearIndependent_exponentMonoidHom.finsuppLinearCombination_injective hlin
  ext e
  exact Int.cast_injective (α := ℂ) (by
    simpa [toComplex_apply] using
      congrArg (fun r : Exponent →₀ ℂ => r e) hC)

end Fourier

theorem Exponent.eval_torusVecOfUnitAddTorus
    (e : Exponent) (x : UnitAddTorus I5) :
    Exponent.eval e (torusVecOfUnitAddTorus x) =
      UnitAddTorus.mFourier e x := by
  simp [Exponent.eval, Exponent.evalUnit, torusVecOfUnitAddTorus,
    UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_zsmul]

theorem eval_torusVecOfUnitAddTorus
    (p : Poly) (x : UnitAddTorus I5) :
    eval p (torusVecOfUnitAddTorus x) =
      Fourier.evalUnitAddTorus p x := by
  rw [eval, Fourier.evalUnitAddTorus]
  apply Finsupp.sum_congr
  intro e _he
  rw [Exponent.eval_torusVecOfUnitAddTorus]

abbrev DiagonalPoint := ActualRestriction.DiagonalSU6Point

namespace DiagonalPoint

theorem det_product (t : DiagonalPoint) :
    ∏ i, t.coords i = 1 := by
  have hdet : (Matrix.diagonal t.coords).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp t.mem).2
  simpa [Matrix.det_diagonal] using hdet

theorem coord_ne_zero (t : DiagonalPoint) (i : I6) :
    t.coords i ≠ 0 := by
  have hprod : (∏ j, t.coords j) ≠ 0 := by
    rw [t.det_product]
    norm_num
  rw [Finset.prod_ne_zero_iff] at hprod
  exact hprod i (Finset.mem_univ i)

theorem coord_mul_star (t : DiagonalPoint) (i : I6) :
    t.coords i * star (t.coords i) = 1 := by
  have hmem :
      Matrix.diagonal t.coords ∈ Matrix.unitaryGroup I6 ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup t.mem
  have hunit := Matrix.mem_unitaryGroup_iff.mp hmem
  rw [Matrix.star_eq_conjTranspose] at hunit
  have hstar :
      Matrix.conjTranspose (Matrix.diagonal t.coords) =
        Matrix.diagonal (fun j => star (t.coords j)) := by
    ext j k
    by_cases h : j = k
    · simp [Matrix.conjTranspose_apply, h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hstar, Matrix.diagonal_mul_diagonal] at hunit
  have hii := congrArg (fun M : Matrix I6 I6 ℂ => M i i) hunit
  simpa using hii

theorem norm_coord (t : DiagonalPoint) (i : I6) :
    ‖t.coords i‖ = 1 := by
  have h := t.coord_mul_star i
  rw [Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq] at h
  have hreal : ‖t.coords i‖ ^ 2 = (1 : ℝ) := by
    exact_mod_cast h
  nlinarith [norm_nonneg (t.coords i)]

def coordUnit (t : DiagonalPoint) (i : I6) : ℂˣ :=
  Units.mk0 (t.coords i) (t.coord_ne_zero i)

theorem prod_coordUnit (t : DiagonalPoint) :
    ∏ i, t.coordUnit i = 1 := by
  apply Units.ext
  simpa [coordUnit] using t.det_product

def toTorusVec (t : DiagonalPoint) : TorusVec :=
  fun i => t.coordUnit i.castSucc

/-- The actual diagonal-torus action of a coordinate transposition. -/
def swap (a b : I6) (h : a ≠ b) (t : DiagonalPoint) : DiagonalPoint where
  coords := t.coords ∘ SignedWeylTransposition.transposition a b
  mem := by
    let g : ActualRestriction.SU6 :=
      SignedWeylTransposition.signedTranspositionSU a b h *
        t.toSU6 *
        (SignedWeylTransposition.signedTranspositionSU a b h)⁻¹
    have hg :
        ((g : ActualRestriction.SU6) : Matrix I6 I6 ℂ) =
          Matrix.diagonal
            (t.coords ∘ SignedWeylTransposition.transposition a b) := by
      change
        ((SignedWeylTransposition.signedTranspositionSU a b h :
              Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) *
            Matrix.diagonal t.coords *
            (((SignedWeylTransposition.signedTranspositionSU a b h)⁻¹ :
              Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) =
          Matrix.diagonal
            (t.coords ∘ SignedWeylTransposition.transposition a b)
      exact SignedWeylTransposition.signedTranspositionSU_conj_diagonal
        a b h t.coords
    rw [← hg]
    exact SetLike.coe_mem g

theorem toSU6_swap_eq_conj
    (a b : I6) (h : a ≠ b) (t : DiagonalPoint) :
    (swap a b h t).toSU6 =
      SignedWeylTransposition.signedTranspositionSU a b h *
        t.toSU6 *
        (SignedWeylTransposition.signedTranspositionSU a b h)⁻¹ := by
  apply Subtype.ext
  change
    Matrix.diagonal
        (t.coords ∘ SignedWeylTransposition.transposition a b) =
      ((SignedWeylTransposition.signedTranspositionSU a b h :
            Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) *
        Matrix.diagonal t.coords *
        (((SignedWeylTransposition.signedTranspositionSU a b h)⁻¹ :
          Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ)
  exact
    (SignedWeylTransposition.signedTranspositionSU_conj_diagonal
      a b h t.coords).symm

theorem coordUnit_swap
    (a b : I6) (h : a ≠ b) (t : DiagonalPoint) (i : I6) :
    (swap a b h t).coordUnit i =
      t.coordUnit (SignedWeylTransposition.transposition a b i) := by
  apply Units.ext
  rfl

def unitAddTorusCoord (x : UnitAddTorus I5) (i : I5) : Circle :=
  AddCircle.toCircle (x i)

def coordsOfUnitAddTorus (x : UnitAddTorus I5) : I6 -> ℂ :=
  ![(unitAddTorusCoord x 0 : ℂ),
    (unitAddTorusCoord x 1 : ℂ),
    (unitAddTorusCoord x 2 : ℂ),
    (unitAddTorusCoord x 3 : ℂ),
    (unitAddTorusCoord x 4 : ℂ),
    ((((unitAddTorusCoord x 0) *
        (unitAddTorusCoord x 1) *
        (unitAddTorusCoord x 2) *
        (unitAddTorusCoord x 3) *
        (unitAddTorusCoord x 4))⁻¹ : Circle) : ℂ)]

theorem circle_star_eq_inv (z : Circle) :
    star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
  rw [Complex.star_def]
  exact (Circle.coe_inv_eq_conj z).symm

theorem circle_det_identity (a b c d e : Circle) :
    (a : ℂ) * (b : ℂ) * (c : ℂ) * (d : ℂ) * (e : ℂ) *
        ((((a * b * c * d * e)⁻¹ : Circle) : ℂ)) = 1 := by
  change ((a * b * c * d * e * (a * b * c * d * e)⁻¹ : Circle) : ℂ) = 1
  simp

theorem star_coordsOfUnitAddTorus_mul
    (x : UnitAddTorus I5) (i : I6) :
    star (coordsOfUnitAddTorus x i) * coordsOfUnitAddTorus x i = 1 := by
  fin_cases i <;>
    simp [coordsOfUnitAddTorus, unitAddTorusCoord,
      circle_star_eq_inv, mul_assoc, mul_left_comm, mul_comm]

theorem diagonal_coordsOfUnitAddTorus_mem_unitaryGroup
    (x : UnitAddTorus I5) :
    Matrix.diagonal (coordsOfUnitAddTorus x) ∈
      Matrix.unitaryGroup I6 ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have hi := star_coordsOfUnitAddTorus_mul x i
    rw [mul_comm] at hi
    exact hi
  · simp [h]

theorem determinant_coordsOfUnitAddTorus
    (x : UnitAddTorus I5) :
    (Matrix.diagonal (coordsOfUnitAddTorus x) :
      Matrix I6 I6 ℂ).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_six]
  simpa [coordsOfUnitAddTorus, unitAddTorusCoord] using
    circle_det_identity
      (unitAddTorusCoord x 0) (unitAddTorusCoord x 1)
      (unitAddTorusCoord x 2) (unitAddTorusCoord x 3)
      (unitAddTorusCoord x 4)

def ofUnitAddTorus (x : UnitAddTorus I5) : DiagonalPoint where
  coords := coordsOfUnitAddTorus x
  mem := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨diagonal_coordsOfUnitAddTorus_mem_unitaryGroup x,
      determinant_coordsOfUnitAddTorus x⟩

theorem toTorusVec_ofUnitAddTorus (x : UnitAddTorus I5) :
    (ofUnitAddTorus x).toTorusVec = torusVecOfUnitAddTorus x := by
  funext i
  fin_cases i <;>
    apply Units.ext <;>
    simp [ofUnitAddTorus, toTorusVec, coordUnit,
      coordsOfUnitAddTorus, unitAddTorusCoord,
      torusVecOfUnitAddTorus]

end DiagonalPoint

namespace Exponent

/-- Evaluation using all six coordinates.  The sixth raw exponent is zero,
so this equals the rank-five evaluator but exposes determinant-one
normalization algebraically. -/
def evalFullUnit (e : Exponent) (t : DiagonalPoint) : ℂˣ :=
  ∏ i, t.coordUnit i ^ rawCoord e i

theorem eval_eq_evalFullUnit (e : Exponent) (t : DiagonalPoint) :
    Exponent.eval e t.toTorusVec = (evalFullUnit e t : ℂ) := by
  have hprod :
      (∏ i : I6, t.coordUnit i ^ rawCoord e i) =
        ∏ i : I5, t.coordUnit i.castSucc ^ e i := by
    rw [Fin.prod_univ_castSucc]
    rw [rawCoord_last]
    simp
  exact congrArg Units.val hprod.symm

theorem evalFullUnit_permute_transposition
    (a b : I6) (h : a ≠ b) (e : Exponent) (t : DiagonalPoint) :
    evalFullUnit
        (permuteExponent
          (SignedWeylTransposition.transposition a b) e) t =
      evalFullUnit e (DiagonalPoint.swap a b h t) := by
  calc
    evalFullUnit
        (permuteExponent
          (SignedWeylTransposition.transposition a b) e) t =
        ∏ i,
          t.coordUnit
              (SignedWeylTransposition.transposition a b i) ^
            rawCoord e i := by
      exact prod_zpow_permuteExponent t.coordUnit t.prod_coordUnit
        (SignedWeylTransposition.transposition a b) e
    _ = evalFullUnit e (DiagonalPoint.swap a b h t) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [DiagonalPoint.coordUnit_swap]

theorem eval_permuteExponent_transposition
    (a b : I6) (h : a ≠ b) (e : Exponent) (t : DiagonalPoint) :
    Exponent.eval
        (permuteExponent
          (SignedWeylTransposition.transposition a b) e)
        t.toTorusVec =
      Exponent.eval e (DiagonalPoint.swap a b h t).toTorusVec := by
  rw [eval_eq_evalFullUnit, eval_eq_evalFullUnit]
  exact congrArg Units.val
    (evalFullUnit_permute_transposition a b h e t)

end Exponent

def diagonalEval (p : Poly) (t : DiagonalPoint) : ℂ :=
  eval p t.toTorusVec

theorem diagonalEval_permute_transposition
    (a b : I6) (h : a ≠ b) (p : Poly) (t : DiagonalPoint) :
    diagonalEval
        (AmbientWeightLattice.permuteCharacter
          (SignedWeylTransposition.transposition a b) p) t =
      diagonalEval p (DiagonalPoint.swap a b h t) := by
  unfold diagonalEval eval AmbientWeightLattice.permuteCharacter
  rw [Finsupp.sum_mapDomain_index_inj
    (permuteExponent_injective
      (SignedWeylTransposition.transposition a b))]
  apply Finsupp.sum_congr
  intro e _he
  rw [Exponent.eval_permuteExponent_transposition a b h]

theorem restrictedCharacter_swap_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ ActualRestriction.SU6 V)
    (a b : I6) (h : a ≠ b) (t : DiagonalPoint) :
    ActualRestriction.restrictedCharacter rho (DiagonalPoint.swap a b h t) =
      ActualRestriction.restrictedCharacter rho t := by
  rw [ActualRestriction.restrictedCharacter,
    ActualRestriction.restrictedCharacter,
    DiagonalPoint.toSU6_swap_eq_conj]
  exact MathlibBridge.su6_representation_character_conj rho t.toSU6
    (SignedWeylTransposition.signedTranspositionSU a b h)

theorem diagonalEval_faithful :
    ∀ p q : Poly,
      (∀ t : DiagonalPoint, diagonalEval p t = diagonalEval q t) ->
        p = q := by
  intro p q h
  apply Fourier.evalUnitAddTorus_faithful
  intro x
  have hx := h (DiagonalPoint.ofUnitAddTorus x)
  simpa [diagonalEval, DiagonalPoint.toTorusVec_ofUnitAddTorus,
    eval_torusVecOfUnitAddTorus] using hx

end
end AmbientLaurent
end GUT

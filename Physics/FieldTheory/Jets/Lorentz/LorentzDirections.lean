import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Math.Algebra.Jets.JetDirections
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! The actual SL(2,ℂ) action M A M† in Pauli coordinates, signature (+---).
Only the algebraic spin action is used; no topological cover theorem is assumed. -/
namespace Physics.LorentzDirections
set_option autoImplicit false
noncomputable section
open Matrix Complex

abbrev Group := WeylSpinor.Group
abbrev Coordinates := Fin 4 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def pauli : Coordinates →ₗ[ℂ] Mat where
  toFun v := !![v 0 + v 3, v 1 - I * v 2; v 1 + I * v 2, v 0 - v 3]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

def fromPauli : Mat →ₗ[ℂ] Coordinates where
  toFun a := ![(a 0 0 + a 1 1) / 2, (a 0 1 + a 1 0) / 2,
    -I * (a 1 0 - a 0 1) / 2, (a 0 0 - a 1 1) / 2]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

def pauliEquiv : Coordinates ≃ₗ[ℂ] Mat :=
  { pauli with
    invFun := fromPauli
    left_inv := by
      intro v
      ext i
      fin_cases i <;> simp [pauli, fromPauli]
      ring_nf
      all_goals simp [I_sq]
    right_inv := by
      intro a
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauli, fromPauli] <;> ring_nf <;> simp [I_sq] <;> ring }

def matrixAction : Representation ℂ Group Mat where
  toFun g :=
    { toFun a := (g : Mat) * a * (g : Mat)ᴴ
      map_add' a b := by simp [mul_add, add_mul]
      map_smul' c a := by simp }
  map_one' := by ext a i j; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    change ((g * h : Group) : Mat) * a * (((g * h : Group) : Mat))ᴴ =
      (g : Mat) * ((h : Mat) * a * (h : Mat)ᴴ) * (g : Mat)ᴴ
    simp only [Matrix.SpecialLinearGroup.coe_mul, conjTranspose_mul, mul_assoc]

@[simp] theorem matrixAction_apply (g : Group) (a : Mat) :
    matrixAction g a = (g : Mat) * a * (g : Mat)ᴴ := rfl

def vector : Representation ℂ Group Coordinates :=
  pauliEquiv.symm.conjRingEquiv.toMonoidHom.comp matrixAction

def basisEquiv : Math.JetDirections.Direction (Fin 4) ≃ₗ[ℂ] Coordinates :=
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 4)

def dualEquiv : Module.Dual ℂ Coordinates ≃ₗ[ℂ] Math.JetDirections.Direction (Fin 4) :=
  (Pi.basisFun ℂ (Fin 4)).dualBasis.repr

def direction : Representation ℂ Group (Math.JetDirections.Direction (Fin 4)) :=
  dualEquiv.conjRingEquiv.toMonoidHom.comp vector.dual

theorem direction_single (g : Group) (i j : Fin 4) :
    (direction g (Finsupp.single i 1)) j = (vector g⁻¹ (Pi.single j 1)) i := by
  change dualEquiv (vector.dual g (dualEquiv.symm (Finsupp.single i 1))) j = _
  rw [show dualEquiv.symm (Finsupp.single i 1) = (Pi.basisFun ℂ (Fin 4)).dualBasis i from
    (LinearEquiv.symm_apply_eq _).mpr (Module.Basis.repr_self _ _).symm]
  simp [dualEquiv, Module.Basis.dualBasis_repr, Representation.dual_apply,
    Module.Dual.transpose_apply]

theorem pauli_vector (g : Group) (v : Coordinates) :
    pauli (vector g v) = (g : Mat) * pauli v * (g : Mat)ᴴ := by
  change pauliEquiv (pauliEquiv.symm (matrixAction g (pauliEquiv v))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

def quadratic (v : Coordinates) : ℂ := v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

theorem det_pauli (v : Coordinates) : Matrix.det (pauli v) = quadratic v := by
  simp only [pauli, LinearMap.coe_mk, AddHom.coe_mk, Matrix.det_fin_two]
  dsimp [quadratic]
  ring_nf
  simp [I_sq]
  ring

theorem quadratic_invariant (g : Group) (v : Coordinates) : quadratic (vector g v) = quadratic v := by
  rw [← det_pauli, pauli_vector, Matrix.det_mul, Matrix.det_mul,
    Matrix.SpecialLinearGroup.det_coe, Matrix.det_conjTranspose,
    Matrix.SpecialLinearGroup.det_coe, star_one, one_mul, mul_one, det_pauli]

def wave : Math.JetDirections.Symbols (Fin 4) :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2 -
    MvPolynomial.X 2 ^ 2 - MvPolynomial.X 3 ^ 2

theorem eval_linearForm (v : Math.JetDirections.Direction (Fin 4)) (x : Coordinates) :
    MvPolynomial.eval x (Math.JetDirections.linearForm v) = ∑ i, v i * x i := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, Finsupp.add_apply, add_mul,
      Finset.sum_add_distrib]
  | single i c => simp [Math.JetDirections.linearForm_single, Finsupp.single_apply]

theorem eval_symbolMap_X (g : Group) (i : Fin 4) (x : Coordinates) :
    MvPolynomial.eval x (Math.JetDirections.symbolMap (direction g) (MvPolynomial.X i)) =
      (vector g⁻¹ x) i := by
  rw [Math.JetDirections.symbolMap_X, eval_linearForm]
  simp only [direction_single]
  have hx : x = ∑ j, x j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hx, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem wave_invariant (g : Group) : Math.JetDirections.symbolMap (direction g) wave = wave := by
  apply MvPolynomial.funext
  intro x
  simp only [wave, map_sub, map_pow, eval_symbolMap_X, MvPolynomial.eval_X]
  exact quadratic_invariant g⁻¹ x

def outer (x y : WeylSpinor.Space) : Mat := Matrix.of (fun a b => x a * y b)

theorem left_right_matrix (g : Group) (x y : WeylSpinor.Space) :
    matrixAction g (outer x y) = outer (WeylSpinor.left g x) (WeylSpinor.right g y) := by
  rw [matrixAction_apply]
  ext a b
  have hl : WeylSpinor.left g x = (g : Mat).mulVec x := rfl
  rw [hl, WeylSpinor.right_apply]
  simp only [outer, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply]
  simp only [Fin.sum_univ_two]
  ring

theorem pauli_real_hermitian (v : Fin 4 → ℝ) : (pauli (fun i => (v i : ℂ)))ᴴ =
    pauli (fun i => (v i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, conjTranspose_apply, sub_eq_add_neg]

theorem preserves_hermitian (g : Group) (a : Mat) (ha : aᴴ = a) :
    (matrixAction g a)ᴴ = matrixAction g a := by
  change ((g : Mat) * a * (g : Mat)ᴴ)ᴴ = (g : Mat) * a * (g : Mat)ᴴ
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, ha, mul_assoc]

theorem pauli_conjugate (v : Coordinates) : pauli (fun i => star (v i)) = (pauli v)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, conjTranspose_apply, sub_eq_add_neg]

theorem vector_preserves_real (g : Group) (v : Fin 4 → ℝ) :
    (fun i => star (vector g (fun j => (v j : ℂ)) i)) = vector g (fun j => (v j : ℂ)) := by
  apply pauliEquiv.injective
  change pauli (fun i => star (vector g (fun j => (v j : ℂ)) i)) =
    pauli (vector g (fun j => (v j : ℂ)))
  rw [pauli_conjugate, pauli_vector]
  simpa only [pauli_vector, matrixAction_apply] using
    preserves_hermitian g _ (pauli_real_hermitian v)

end
end Physics.LorentzDirections

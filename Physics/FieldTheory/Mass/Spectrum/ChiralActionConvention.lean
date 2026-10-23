import Mathlib.Algebra.Star.Module
import Mathlib.Tactic

/-! Explicit chiral mass and canonical time-kinetic conventions in a
noncommutative star algebra. Differentiated odd components and the total
 derivative are formal inputs; no boundary-value calculus is inferred. -/
namespace Physics.ChiralActionConvention
set_option autoImplicit false
noncomputable section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

def bracket (s n : Fin 2 → R) : R := s 0*n 1-s 1*n 0

def rightConj (n : Fin 2 → R) : Fin 2 → R := ![-star (n 1),star (n 0)]
def barredLR (s n : Fin 2 → R) : R :=
  star (s 0)*rightConj n 0 + star (s 1)*rightConj n 1

def leftDirac (s : Fin 2 → R) : Fin 4 → R := ![s 0,s 1,0,0]
def rightDirac (n : Fin 2 → R) : Fin 4 → R :=
  ![0,0,rightConj n 0,rightConj n 1]
def gammaZero : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]

def diracBarProduct (s n : Fin 2 → R) : R :=
  ∑ a, ∑ b, gammaZero a b • (star (leftDirac s a)*rightDirac n b)

omit [StarModule ℂ R] in
theorem dirac_bar_product (s n : Fin 2 → R) : diracBarProduct s n = barredLR s n := by
  simp [diracBarProduct, leftDirac, rightDirac, gammaZero, barredLR, Fin.sum_univ_succ]

def majoranaDirac (s : Fin 2 → R) : Fin 4 → R := leftDirac s+rightDirac s

def majoranaBarRight (s n : Fin 2 → R) : R :=
  ∑ a, ∑ b, gammaZero a b • (star (majoranaDirac s a)*rightDirac n b)

omit [StarModule ℂ R] in
theorem majorana_bar_right (s n : Fin 2 → R) : majoranaBarRight s n = barredLR s n := by
  simp [majoranaBarRight, majoranaDirac, leftDirac, rightDirac, gammaZero,
    barredLR, Fin.sum_univ_succ]

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem right_conj_inverse (n : Fin 2 → R) :
    ![star (rightConj n 1),-star (rightConj n 0)] = n := by
  ext i
  fin_cases i <;> simp [rightConj]

/- Reversing the order under Hermitian conjugation is essential. -/
omit [Algebra ℂ R] [StarModule ℂ R] in
theorem barred_lr (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    barredLR s n = star (bracket s n) := by
  simp only [barredLR, rightConj, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_neg, bracket, star_sub, star_mul]
  rw [h0,h1]
  abel

/- The holomorphic part is the Hermitian conjugate of the displayed barred vertex. -/
theorem conjugate_vertex (y z : ℂ) (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    star ((-(y*star z)) • barredLR s n) =
      (-(star y*z)) • bracket s n := by
  rw [barred_lr s n h0 h1]
  simp

def kineticLeft (n dn : Fin 2 → R) : R := star (n 0)*dn 0+star (n 1)*dn 1
def kineticRight (n dn : Fin 2 → R) : R :=
  star (rightConj n 0)*rightConj dn 0 + star (rightConj n 1)*rightConj dn 1
/- Formal derivative of n_0*star(n_0)+n_1*star(n_1), by Leibniz. -/
def totalDerivative (n dn : Fin 2 → R) : R :=
  dn 0*star (n 0)+n 0*star (dn 0)+dn 1*star (n 1)+n 1*star (dn 1)

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem kinetic_mod_derivative (n dn : Fin 2 → R)
    (h0 : dn 0*star (n 0) = -(star (n 0)*dn 0))
    (h1 : dn 1*star (n 1) = -(star (n 1)*dn 1)) :
    kineticRight n dn = kineticLeft n dn+totalDerivative n dn := by
  simp [kineticRight, rightConj, kineticLeft, totalDerivative, h0,h1]
  abel

/- Chiral kinetic matrix after charge conjugation and integration by parts. -/
def flipMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![A 1 1,-A 0 1;-A 1 0,A 0 0]

def kineticMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) (n dn : Fin 2 → R) : R :=
  ∑ i, ∑ j, A i j • (star (n i)*dn j)

def matrixDerivative (B : Matrix (Fin 2) (Fin 2) ℂ) (n dn : Fin 2 → R) : R :=
  ∑ i, ∑ j, B j i • (dn i*star (n j)+n i*star (dn j))

omit [StarModule ℂ R] in
theorem kinetic_matrix_mod_derivative (A : Matrix (Fin 2) (Fin 2) ℂ)
    (n dn : Fin 2 → R)
    (h : ∀ i j, dn i*star (n j) = -(star (n j)*dn i)) :
    kineticMatrix A (rightConj n) (rightConj dn) =
      kineticMatrix (flipMatrix A) n dn+matrixDerivative (flipMatrix A) n dn := by
  simp [kineticMatrix, matrixDerivative, flipMatrix, rightConj, Fin.sum_univ_succ, h]
  module

/- The canonical Majorana kinetic half compensates its two chiral blocks;
there is no corresponding vertex half. -/
omit [StarModule ℂ R] in
theorem majorana_kinetic (A : Matrix (Fin 2) (Fin 2) ℂ) (n dn : Fin 2 → R)
    (h : ∀ i j, dn i*star (n j) = -(star (n j)*dn i)) :
    (1/2 : ℂ) • (kineticMatrix (flipMatrix A) n dn+
      kineticMatrix A (rightConj n) (rightConj dn)) =
      kineticMatrix (flipMatrix A) n dn+(1/2 : ℂ) • matrixDerivative (flipMatrix A) n dn := by
  rw [kinetic_matrix_mod_derivative A n dn h]
  module

def pauli (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0,1;1,0],!![0,-Complex.I;Complex.I,0],!![1,0;0,-1]] i

theorem flip_time : flipMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipMatrix]

theorem flip_space (i : Fin 3) : flipMatrix (pauli i) = -pauli i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [flipMatrix, pauli]

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem canonical_norm_form (n : Fin 2 → ℂ) :
    star (rightConj n 0)*rightConj n 0+star (rightConj n 1)*rightConj n 1 =
      star (n 0)*n 0+star (n 1)*n 1 := by
  simp [rightConj]
  ring

end
end Physics.ChiralActionConvention

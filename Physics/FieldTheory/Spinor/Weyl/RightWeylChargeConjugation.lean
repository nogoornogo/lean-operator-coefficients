import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Physics.StandardModel.Gauge.Tensors.SMEpsilonTensor
import Mathlib.Tactic

/-! An explicit Euclidean four-component bilinear convention.
The right subspace is the first block, and its CP bilinear is epsilon.
The chirality orientation is stated explicitly rather than inferred from C. -/
namespace Physics.RightWeylChargeConjugation
set_option autoImplicit false
noncomputable section
open Matrix SMEpsilonTensor

abbrev Dirac := Fin 4 → ℂ

def charge : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,1,0,0; -1,0,0,0; 0,0,0,-1; 0,0,1,0]

def gammaTwo : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

def gammaFour : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

def gammaOne : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,Complex.I; 0,0,Complex.I,0;
    0,-Complex.I,0,0; -Complex.I,0,0,0]

def gammaThree : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,Complex.I,0; 0,0,0,-Complex.I;
    -Complex.I,0,0,0; 0,Complex.I,0,0]

def gamma (mu : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![gammaOne, gammaTwo, gammaThree, gammaFour] mu

def chirality : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

def rightProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]

def embedRight (s : WeylSpinor.Space) : Dirac := ![s 0, s 1, 0, 0]

/-- Transpose, not Hermitian conjugation: complex bilinearity is essential. -/
def diquark (q r : Dirac) : ℂ := ∑ i, ∑ j, q i * (charge * rightProjector) i j * r j

theorem charge_eq : charge = gammaTwo * gammaFour := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [charge, gammaTwo, gammaFour, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gamma_hermitian (mu : Fin 4) : (gamma mu).conjTranspose = gamma mu := by
  fin_cases mu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, gammaOne, gammaTwo, gammaThree, gammaFour,
      Matrix.conjTranspose_apply]

set_option maxHeartbeats 800000 in
theorem gamma_clifford (mu nu : Fin 4) :
    gamma mu * gamma nu + gamma nu * gamma mu =
      if mu = nu then (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0 := by
  fin_cases mu <;> fin_cases nu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, gammaOne, gammaTwo, gammaThree, gammaFour,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- This fixes the gamma-five orientation of this adapter. -/
theorem chirality_orientation :
    chirality = -(gammaOne * gammaTwo * gammaThree * gammaFour) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [chirality, gammaOne, gammaTwo, gammaThree, gammaFour,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem charge_gamma (mu : Fin 4) :
    charge * gamma mu * charge.conjTranspose = -(gamma mu).transpose := by
  fin_cases mu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [charge, gamma, gammaOne, gammaTwo, gammaThree, gammaFour,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem charge_transpose : charge.transpose = -charge := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [charge]

theorem charge_conjTranspose : charge.conjTranspose = -charge := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [charge, Matrix.conjTranspose_apply]

theorem projector_eq : rightProjector = (1 / 2 : ℂ) • (1 + chirality) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [rightProjector, chirality]

theorem projector_idempotent : rightProjector * rightProjector = rightProjector := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rightProjector, Matrix.mul_apply, Fin.sum_univ_succ]

theorem projector_embedRight (s : WeylSpinor.Space) :
    rightProjector.mulVec (embedRight s) = embedRight s := by
  ext i; fin_cases i <;>
    simp [rightProjector, embedRight, Matrix.mulVec]

theorem right_diquark (s t : WeylSpinor.Space) :
    diquark (embedRight s) (embedRight t) = eps2 s t := by
  simp [diquark, embedRight, charge, rightProjector, Matrix.mul_apply,
    Fin.sum_univ_succ, eps2]
  ring

theorem three_right_diquarks (s t u v w x : WeylSpinor.Space) :
    diquark (embedRight s) (embedRight t) *
      diquark (embedRight u) (embedRight v) *
      diquark (embedRight w) (embedRight x) =
        eps2 s t * eps2 u v * eps2 w x := by
  simp only [right_diquark]

end
end Physics.RightWeylChargeConjugation

import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureMixed

/-! Ordered chiral block-current identities in signature (+---). Formal
barred/raised components are specified explicitly; no analytic dagger is assumed. -/
namespace Physics.MinkowskiWeylCurrent
set_option autoImplicit false
noncomputable section
open Matrix Complex
abbrev Block := Bool × Fin 2
abbrev sigma := DerivativeLiteratureMixed.sigma
def eta (i : Fin 4) : ℂ := if i = 0 then 1 else -1
def barSigma (i : Fin 4) : LorentzDirections.Mat := eta i • sigma i
def gamma (i : Fin 4) : Matrix Block Block ℂ := fun p q =>
  if p.1 = q.1 then 0 else if p.1 then barSigma i p.2 q.2 else sigma i p.2 q.2
def projector (right : Bool) : Matrix Block Block ℂ := fun p q =>
  if p = q ∧ p.1 = right then 1 else 0

theorem right_projector (i : Fin 4) (a b : Fin 2) :
    (gamma i * projector true) (false,a) (true,b) = sigma i a b := by
  simp [gamma, projector, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases b <;> simp

private theorem clifford_0 (j : Fin 4) : gamma 0 * gamma j + gamma j * gamma 0 =
    (if (0 : Fin 4) = j then 2 * eta 0 else 0) • (1 : Matrix Block Block ℂ) := by
  ext ⟨c,a⟩ ⟨d,b⟩
  fin_cases j <;> cases c <;> cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [gamma, eta, barSigma, sigma, DerivativeLiteratureMixed.sigma,
      LorentzDirections.pauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem clifford_1 (j : Fin 4) : gamma 1 * gamma j + gamma j * gamma 1 =
    (if (1 : Fin 4) = j then 2 * eta 1 else 0) • (1 : Matrix Block Block ℂ) := by
  ext ⟨c,a⟩ ⟨d,b⟩
  fin_cases j <;> cases c <;> cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [gamma, eta, barSigma, sigma, DerivativeLiteratureMixed.sigma,
      LorentzDirections.pauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem clifford_2 (j : Fin 4) : gamma 2 * gamma j + gamma j * gamma 2 =
    (if (2 : Fin 4) = j then 2 * eta 2 else 0) • (1 : Matrix Block Block ℂ) := by
  ext ⟨c,a⟩ ⟨d,b⟩
  fin_cases j <;> cases c <;> cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [gamma, eta, barSigma, sigma, DerivativeLiteratureMixed.sigma,
      LorentzDirections.pauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem clifford_3 (j : Fin 4) : gamma 3 * gamma j + gamma j * gamma 3 =
    (if (3 : Fin 4) = j then 2 * eta 3 else 0) • (1 : Matrix Block Block ℂ) := by
  ext ⟨c,a⟩ ⟨d,b⟩
  fin_cases j <;> cases c <;> cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [gamma, eta, barSigma, sigma, DerivativeLiteratureMixed.sigma,
      LorentzDirections.pauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

theorem clifford (i j : Fin 4) : gamma i * gamma j + gamma j * gamma i =
    (if i = j then 2 * eta i else 0) • (1 : Matrix Block Block ℂ) := by
  fin_cases i
  · exact clifford_0 j
  · exact clifford_1 j
  · exact clifford_2 j
  · exact clifford_3 j

variable {R : Type*} [Ring R] [Algebra ℂ R]
def spinor (chi etaDagger : Fin 2 → R) : Block → R :=
  fun p => if p.1 then etaDagger p.2 else chi p.2
def barred (etaSpinor chiDagger : Fin 2 → R) : Block → R :=
  fun p => if p.1 then chiDagger p.2 else etaSpinor p.2
def ordered (i : Fin 4) (x y : Fin 2 → R) : R :=
  ∑ a : Fin 2, ∑ b : Fin 2, sigma i a b • (x a * y b)
def rightBlock (i : Fin 4) (chi etaDagger etaSpinor chiDagger : Fin 2 → R) : R :=
  ∑ p : Block, ∑ q : Block,
    (gamma i * projector true) p q •
      (barred etaSpinor chiDagger p * spinor chi etaDagger q)

theorem right_block_dictionary (i : Fin 4) (chi etaDagger etaSpinor chiDagger : Fin 2 → R) :
    rightBlock i chi etaDagger etaSpinor chiDagger = ordered i etaSpinor etaDagger := by
  simp [rightBlock, ordered, gamma, projector, barred, spinor, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

def raise (x : Fin 2 → R) : Fin 2 → R := ![x 1, -x 0]
def reversedBar (i : Fin 4) (x y : Fin 2 → R) : R :=
  ∑ a : Fin 2, ∑ b : Fin 2, barSigma i a b • (raise y a * raise x b)

theorem anticommuting_reverse (i : Fin 4) (x y : Fin 2 → R)
    (h : ∀ a b, x a * y b = -(y b * x a)) :
    ordered i x y = -reversedBar i x y := by
  fin_cases i <;>
    simp [ordered, reversedBar, raise, barSigma, eta, sigma, DerivativeLiteratureMixed.sigma, LorentzDirections.pauli,
      Fin.sum_univ_two, h, neg_smul, smul_neg]
  <;> module

theorem literal_current (i : Fin 4) :
    ordered i (DerivativeLiteratureMixed.psi false) (DerivativeLiteratureMixed.psi true) =
      DerivativeLiteratureMixed.current i := rfl

theorem literal_reversal (i : Fin 4) :
    DerivativeLiteratureMixed.current i =
      -reversedBar i (DerivativeLiteratureMixed.psi false) (DerivativeLiteratureMixed.psi true) := by
  apply anticommuting_reverse
  intro a b
  exact DerivativeLiteratureMixed.odd_swap _ _

end
end Physics.MinkowskiWeylCurrent

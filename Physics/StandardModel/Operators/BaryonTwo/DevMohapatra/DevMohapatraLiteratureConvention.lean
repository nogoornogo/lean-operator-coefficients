import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraSignedConvention
import Physics.FieldTheory.Mass.Spectrum.ChiralActionConvention

/-! Fixed matrix dictionaries from 1404.1003v4 and FERMILAB-PUB-80-061-THY.
Adoption by 1504.07196v2 and canonical physical mass normalization are inputs,
not inferred from shared authorship. Only derivative-free tree algebra is used. -/
namespace Physics.DevMohapatraLiteratureConvention
set_option autoImplicit false
noncomputable section
open DevMohapatraTreeLevel RightWeylChargeConjugation
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Dev Appendix B.3: gamma0 off diagonal, gamma2 with sigma2 in upper block. -/
def devGammaZero : Matrix (Fin 4) (Fin 4) ℂ := gammaFour
def devGammaTwo : Matrix (Fin 4) (Fin 4) ℂ := -Complex.I • gammaTwo
def devCharge : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.I • (devGammaZero * devGammaTwo)

/-- Mohapatra Appendix A: spatial upper block -i sigma2, C = gamma2 gamma4. -/
def mohapatraGammaTwo : Matrix (Fin 4) (Fin 4) ℂ := -gammaTwo
def mohapatraCharge : Matrix (Fin 4) (Fin 4) ℂ := mohapatraGammaTwo * gammaFour

theorem devCharge_eq : devCharge = -charge := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [devCharge, devGammaZero, devGammaTwo, gammaTwo, gammaFour, charge,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem mohapatraCharge_eq : mohapatraCharge = -charge := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mohapatraCharge, mohapatraGammaTwo, gammaTwo, gammaFour, charge,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Inverse of both literature matrices in these explicitly supplied bases. -/
def literatureInverse : Matrix (Fin 4) (Fin 4) ℂ := charge

theorem dev_inverse : literatureInverse * devCharge = 1 ∧
    devCharge * literatureInverse = 1 := by
  rw [devCharge_eq]
  exact ⟨DevMohapatraSignedConvention.inverse_right,
    DevMohapatraSignedConvention.inverse_left⟩

theorem mohapatra_inverse : literatureInverse * mohapatraCharge = 1 ∧
    mohapatraCharge * literatureInverse = 1 := by
  rw [mohapatraCharge_eq]
  exact ⟨DevMohapatraSignedConvention.inverse_right,
    DevMohapatraSignedConvention.inverse_left⟩

/-- Lower right-chiral block of the literature dictionary, not repo upper block. -/
def rightComponents (x : Fin 2 → V) : Fin 4 → A V :=
  ![0, 0, ExteriorAlgebra.ι ℂ (x 0), ExteriorAlgebra.ι ℂ (x 1)]
def rightPair (x y : Fin 2 → V) : A V :=
  ∑ i, ∑ j, literatureInverse i j • (rightComponents x i * rightComponents y j)

theorem rightPair_eq (x y : Fin 2 → V) : rightPair x y = -pair x y := by
  simp [rightPair, literatureInverse, charge, rightComponents, pair,
    Fin.sum_univ_succ, sub_eq_add_neg]
  abel

theorem rightPair_transport (x y : Fin 2 → V) :
    rightPair x y = DevMohapatraSignedConvention.inversePair x y := by
  rw [rightPair_eq, DevMohapatraSignedConvention.inversePair_eq]

theorem source_mass (M : ℂ) (n : Fin 2 → V) :
    (M / 2) • rightPair n n = -M •
      (ExteriorAlgebra.ι ℂ (n 0) * ExteriorAlgebra.ι ℂ (n 1)) := by
  rw [rightPair_transport]
  exact DevMohapatraSignedConvention.source_mass M n

theorem source_vertex (z : ℂ) (x y : Fin 2 → V) :
    z • rightPair x y = (-z) • pair x y := by
  rw [rightPair_transport]
  exact DevMohapatraSignedConvention.source_vertex z x y

def downCurrent (d s : Fin 3 → Fin 2 → V) (a : Fin 3) : A V :=
  ∑ b, ∑ c, SMEpsilonTensor.eps3 (SMEpsilonTensor.colorBasis a)
    (SMEpsilonTensor.colorBasis b) (SMEpsilonTensor.colorBasis c) • rightPair (d b) (s c)

theorem downCurrent_transport (d s : Fin 3 → Fin 2 → V) (a : Fin 3) :
    downCurrent d s a = DevMohapatraSignedConvention.inverseDownCurrent d s a := by
  simp only [downCurrent, rightPair_transport, DevMohapatraSignedConvention.inverseDownCurrent]

def operator (u d s : Fin 3 → Fin 2 → V) : A V :=
  ∑ a, ∑ b, rightPair (u a) (u b) * (downCurrent d s a * downCurrent d s b)

theorem operator_transport (u d s : Fin 3 → Fin 2 → V) :
    operator u d s = DevMohapatraSignedConvention.inverseOperator u d s := by
  simp only [operator, rightPair_transport, downCurrent_transport,
    DevMohapatraSignedConvention.inverseOperator]

/-- Both vertices and target use the transported lower-block inverse-C pairing. -/
def coefficient (m M lam b : ℂ) : ℂ := -treePrefactor m M lam b

theorem generated_literature (m M lam b : ℂ) (u d s : Fin 3 → Fin 2 → V) :
    generated m M (-lam) (-b) u d s = coefficient m M lam b • operator u d s := by
  rw [operator_transport]
  exact DevMohapatraSignedConvention.generated_inverse m M lam b u d s

theorem scalar_mass_sign (m M lam b : ℂ) :
    coefficient (-m) M lam b = coefficient m M lam b := by
  simp [coefficient, treePrefactor]

theorem ordered_flavors (m M lam z : ℂ) :
    coefficient m M lam (2 * z) = 4 * coefficient m M lam z := by
  rw [coefficient, treePrefactor_down_rescaling]
  norm_num [coefficient]

theorem paper_comparison (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0) :
    coefficient m M lam z = -(8 * (Real.pi : ℂ) ^ 2) * paperPrefactor m M lam z := by
  rw [coefficient, prefactor_comparison m M lam z hm hM]
  ring

theorem ordered_paper_comparison (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0) :
    coefficient m M lam (2 * z) =
      -(32 * (Real.pi : ℂ) ^ 2) * paperPrefactor m M lam z := by
  rw [ordered_flavors, paper_comparison m M lam z hm hM]
  ring

end
end Physics.DevMohapatraLiteratureConvention

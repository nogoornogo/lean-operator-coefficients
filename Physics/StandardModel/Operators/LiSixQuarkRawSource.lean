import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.SixQuarkFlavorCoordinates

/-! Unprojected literal sources in repository slot order. Their coordinate
identities are polynomial epsilon identities on arbitrary vectors, not values
in a closed table of basis probes. -/
namespace GUT.LiSixQuarkRawSource
noncomputable section
open SixQuarkInvariant SMEpsilonTensor

/-- The four color diagrams after the fixed paper-to-repository relabelling. -/
def colorPermutation (k : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![1,4,0,3,5,2], ![1,5,2,3,4,0],
    ![1,3,0,4,5,2], ![1,3,2,4,5,0]] : Fin 4 → Fin 6 → Fin 6) k
  invFun := (![![2,0,5,3,1,4], ![5,0,2,3,4,1],
    ![2,0,5,1,3,4], ![5,0,2,1,3,4]] : Fin 4 → Fin 6 → Fin 6) k
  left_inv i := by fin_cases k <;> fin_cases i <;> rfl
  right_inv i := by fin_cases k <;> fin_cases i <;> rfl

def spinPermutation : Equiv.Perm (Fin 6) where
  toFun := ![1,5,0,3,2,4]
  invFun := ![2,0,4,3,5,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def colorKind (k : Fin 11) : Fin 4 := match k with
  | 1 | 3 | 6 => 1
  | 5 => 2
  | 8 => 3
  | _ => 0

def rawColor (k : Fin 4) : SixColorInvariant.Coefficient :=
  (SixColorInvariant.pairing 0).domDomCongr (colorPermutation k)
def rawSpin : SixWeylMultilinear.Coefficient :=
  (SixWeylMultilinear.pairing 0).domDomCongr spinPermutation

def colorCoordinates (k : Fin 4) : Fin 5 → ℂ :=
  (![![0,0,1,0,0], ![1,-1,1,1,-1], ![0,1,0,0,0], ![-1,1,0,-1,0]] :
    Fin 4 → Fin 5 → ℂ) k
def spinCoordinates : Fin 5 → ℂ := ![1,1,0,1,1]

private theorem rawColor_reconstruct_0 :
    rawColor 0 = SixColorInvariant.reconstruct (colorCoordinates 0) := by
  ext v
  simp [rawColor, colorPermutation, colorCoordinates, SixColorInvariant.pairing_apply,
    SixColorInvariant.reconstruct_apply, SixColorInvariant.pairingValue,
    MultilinearMap.domDomCongr_apply, Fin.sum_univ_succ, eps3]
  ring

private theorem rawColor_reconstruct_1 :
    rawColor 1 = SixColorInvariant.reconstruct (colorCoordinates 1) := by
  ext v
  simp [rawColor, colorPermutation, colorCoordinates, SixColorInvariant.pairing_apply,
    SixColorInvariant.reconstruct_apply, SixColorInvariant.pairingValue,
    MultilinearMap.domDomCongr_apply, Fin.sum_univ_succ, eps3]
  ring

private theorem rawColor_reconstruct_2 :
    rawColor 2 = SixColorInvariant.reconstruct (colorCoordinates 2) := by
  ext v
  simp [rawColor, colorPermutation, colorCoordinates, SixColorInvariant.pairing_apply,
    SixColorInvariant.reconstruct_apply, SixColorInvariant.pairingValue,
    MultilinearMap.domDomCongr_apply, Fin.sum_univ_succ, eps3]
  ring

private theorem rawColor_reconstruct_3 :
    rawColor 3 = SixColorInvariant.reconstruct (colorCoordinates 3) := by
  ext v
  simp [rawColor, colorPermutation, colorCoordinates, SixColorInvariant.pairing_apply,
    SixColorInvariant.reconstruct_apply, SixColorInvariant.pairingValue,
    MultilinearMap.domDomCongr_apply, Fin.sum_univ_succ, eps3]
  ring

theorem rawColor_reconstruct (k : Fin 4) :
    rawColor k = SixColorInvariant.reconstruct (colorCoordinates k) := by
  fin_cases k
  · exact rawColor_reconstruct_0
  · exact rawColor_reconstruct_1
  · exact rawColor_reconstruct_2
  · exact rawColor_reconstruct_3

theorem rawSpin_reconstruct : rawSpin = SixWeylMultilinear.reconstruct spinCoordinates := by
  ext v
  simp [rawSpin, spinPermutation, spinCoordinates, SixWeylMultilinear.reconstruct,
    SixWeylMultilinear.pairing_apply, SixWeylMultilinear.pairingValue,
    SixWeylInvariant.pairingValue, MultilinearMap.domDomCongr_apply,
    Fin.sum_univ_succ, eps2]
  ring

/-- Reconstruction commutes with a product of arbitrary color and spin vectors. -/
theorem reconstruct_outer (a b : Fin 5 → ℂ) :
    SixQuarkInvariant.reconstruct (fun p q => a p * b q) =
      combine (SixColorInvariant.reconstruct a) (SixWeylMultilinear.reconstruct b) := by
  apply pure_ext
  intro v s
  simp only [SixQuarkInvariant.reconstruct_apply, combine_apply,
    SixColorInvariant.reconstruct_apply, SixWeylMultilinear.reconstruct,
    SixWeylMultilinear.pairing_apply, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

def rawCoefficient (k : Fin 11) : Coefficient := combine (rawColor (colorKind k)) rawSpin

def rawCoordinates (k : Fin 11) : Fin 5 → Fin 5 → ℂ :=
  fun p q => colorCoordinates (colorKind k) p * spinCoordinates q

theorem rawCoefficient_reconstruct (k : Fin 11) :
    rawCoefficient k = SixQuarkInvariant.reconstruct (rawCoordinates k) := by
  rw [rawCoefficient, rawColor_reconstruct, rawSpin_reconstruct]
  exact (reconstruct_outer _ _).symm

end
end GUT.LiSixQuarkRawSource

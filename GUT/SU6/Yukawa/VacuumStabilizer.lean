import GUT.SU6.SelectionRules.Models.StandardSMUVStabilizer

open Physics

/-! Actual coordinate-fixing elements preserve the existing scalar vacuum. -/
set_option autoImplicit false
namespace GUT.SU6YukawaStabilizer
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer

theorem inverse_sixth (g : ActualRestriction.SU6)
    (hg : FundamentalRepresentation.rho g sixth = sixth) :
    FundamentalRepresentation.rho g⁻¹ sixth = sixth := by
  calc
    _ = FundamentalRepresentation.rho g⁻¹ (FundamentalRepresentation.rho g sixth) :=
      congrArg (FundamentalRepresentation.rho g⁻¹) hg.symm
    _ = _ := Representation.inv_self_apply _ _ _

theorem heavyVector_covariant (g : ActualRestriction.SU6)
    (hl : ∀ v : Six, FundamentalRepresentation.rho g v 5 = v 5)
    (hs : FundamentalRepresentation.rho g sixth = sixth) (x : UV) :
    heavyVector (uvRho g x) = FundamentalRepresentation.rho g (heavyVector x) := by
  change contract (exteriorCoordinates (ConcreteSU6Representations.exteriorTwo.rho g x.1.1)) +
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho g x.1.2) sixth • sixth = _
  rw [exteriorCoordinates_action, contract_covariant g hl,
    dualCoordinates_action, inverse_sixth g hs]
  simp only [heavyVector, map_add, map_smul, hs]

theorem mass_fixed (H : Type*) [CommGroup H] (g : ActualRestriction.SU6)
    (hl : ∀ v : Six, FundamentalRepresentation.rho g v 5 = v 5)
    (hs : FundamentalRepresentation.rho g sixth = sixth) (x y : UV) :
    (StandardSMUVMass.mass H).form (uvRho g x) (uvRho g y) =
      (StandardSMUVMass.mass H).form x y := by
  rw [mass_formula, mass_formula, heavyVector_covariant g hl hs, heavyVector_covariant g hl hs]
  change dualCoordinates (ConcreteSU6Representations.antifundamental.rho g y.2)
      (FundamentalRepresentation.rho g (heavyVector x)) +
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho g x.2)
      (FundamentalRepresentation.rho g (heavyVector y)) = _
  rw [dualCoordinates_action, dualCoordinates_action,
    Representation.inv_self_apply, Representation.inv_self_apply]

theorem vacuum_fixed (H : Type*) [CommGroup H] (g : ActualRestriction.SU6)
    (hl : ∀ v : Six, FundamentalRepresentation.rho g v 5 = v 5)
    (hs : FundamentalRepresentation.rho g sixth = sixth) :
    StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H :=
  (vacuum_fixed_iff H g).mpr (mass_fixed H g hl hs)

def phase (k : Fin 4) (i : Fin 6) : ℂ :=
  if i.val = k.val then Complex.I else if i.val = 4 then -Complex.I else 1

def phaseElement (k : Fin 4) : ActualRestriction.SU6 :=
  ⟨Matrix.diagonal (phase k), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      have h : ∀ i, phase k i * star (phase k i) = 1 := by
        intro i
        simp only [phase]
        split_ifs <;> norm_num [Complex.star_def]
      convert Matrix.diagonal_one (n := Fin 6) (α := ℂ) using 1
      congr 1
      funext i
      exact h i
    · rw [Matrix.det_diagonal]
      fin_cases k <;> norm_num [phase, Fin.prod_univ_succ, Complex.I_mul_I]⟩

theorem phase_action (k : Fin 4) (v : Six) (i : Fin 6) :
    FundamentalRepresentation.rho (phaseElement k) v i = phase k i * v i := by
  simp [FundamentalRepresentation.rho, phaseElement, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal]

theorem phase_last (k : Fin 4) (v : Six) :
    FundamentalRepresentation.rho (phaseElement k) v 5 = v 5 := by
  rw [phase_action]
  have h : ¬ 5 = k.val := by omega
  simp [phase, h]

theorem phase_sixth (k : Fin 4) :
    FundamentalRepresentation.rho (phaseElement k) sixth = sixth := by
  funext i
  rw [phase_action]
  fin_cases i <;> simp [sixth]
  have h : ¬ 5 = k.val := by omega
  simp [phase, h]

theorem phase_vacuum (H : Type*) [CommGroup H] (k : Fin 4) :
    StandardSMUVYukawa.scalar.rho (phaseElement k) (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H :=
  vacuum_fixed H (phaseElement k) (phase_last k) (phase_sixth k)

def swapElement (k : Fin 4) : ActualRestriction.SU6 :=
  SignedWeylTransposition.signedTranspositionSU 0 ⟨k.val + 1, by omega⟩ (by
    intro h
    have := congrArg Fin.val h
    simp at this)

theorem swap_action (k : Fin 4) (v : Six) (i : Fin 6) :
    FundamentalRepresentation.rho (swapElement k) v i =
      SignedWeylTransposition.signAt 0 i * v (Equiv.swap 0 ⟨k.val + 1, by omega⟩ i) := by
  simp [FundamentalRepresentation.rho, swapElement,
    SignedWeylTransposition.signedTranspositionSU, SignedWeylTransposition.signedMatrix,
    SignedWeylTransposition.signMatrix, SignedWeylTransposition.permutationMatrix,
    SignedWeylTransposition.transposition, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal, Matrix.permMatrix_mulVec]

theorem swap_last (k : Fin 4) (v : Six) :
    FundamentalRepresentation.rho (swapElement k) v 5 = v 5 := by
  rw [swap_action]
  have h : (5 : Fin 6) ≠ ⟨k.val + 1, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  simp [SignedWeylTransposition.signAt, Equiv.swap_apply_of_ne_of_ne, h]

theorem swap_sixth (k : Fin 4) :
    FundamentalRepresentation.rho (swapElement k) sixth = sixth := by
  funext i
  rw [swap_action]
  fin_cases k <;> fin_cases i <;>
    norm_num [SignedWeylTransposition.signAt, sixth, Equiv.swap_apply_def, Fin.ext_iff]

theorem swap_vacuum (H : Type*) [CommGroup H] (k : Fin 4) :
    StandardSMUVYukawa.scalar.rho (swapElement k) (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H :=
  vacuum_fixed H (swapElement k) (swap_last k) (swap_sixth k)

theorem evaluation_fixed (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (g : ActualRestriction.SU6)
    (hg : StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H) (x y : UV) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H) (uvRho g x) (uvRho g y) =
      Y.toLinearMap (StandardSMUVYukawa.vacuum H) x y := by
  simpa only [hg] using Y.invariant g (StandardSMUVYukawa.vacuum H) x y

theorem evaluation_phase (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (k : Fin 4) (x y : UV) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H)
        (uvRho (phaseElement k) x) (uvRho (phaseElement k) y) =
      Y.toLinearMap (StandardSMUVYukawa.vacuum H) x y :=
  evaluation_fixed H Y _ (phase_vacuum H k) x y

theorem evaluation_swap (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (k : Fin 4) (x y : UV) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H)
        (uvRho (swapElement k) x) (uvRho (swapElement k) y) =
      Y.toLinearMap (StandardSMUVYukawa.vacuum H) x y :=
  evaluation_fixed H Y _ (swap_vacuum H k) x y

end
end GUT.SU6YukawaStabilizer

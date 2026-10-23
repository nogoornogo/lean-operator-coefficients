import GUT.SU6.Yukawa.VacuumStabilizer
import GUT.SU6.Yukawa.StabilizerWeights
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Basis.Prod

open Physics

open Math

/-! Coordinate bases for the actual analytic matter representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6YukawaBasis
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6YukawaStabilizer SU6YukawaWeights

def exteriorBasis : Module.Basis (ExteriorSquareCoordinates.Pair 6) ℂ
    ConcreteSU6Representations.exteriorTwo.V :=
  ExteriorSquareCoordinates.basis.map exteriorCoordinates.symm.toLinearEquiv

def dualBasis : Module.Basis (Fin 6) ℂ ConcreteSU6Representations.antifundamental.V :=
  (Pi.basisFun ℂ (Fin 6)).dualBasis.map dualCoordinates.symm.toLinearEquiv

def basis : Module.Basis Label ℂ UV := (exteriorBasis.prod dualBasis).prod dualBasis

theorem exteriorBasis_coordinates (p : ExteriorSquareCoordinates.Pair 6) :
    exteriorCoordinates (exteriorBasis p) = ExteriorSquareCoordinates.basis p := by
  simp [exteriorBasis]

theorem dualBasis_coordinates (i : Fin 6) (v : Six) :
    dualCoordinates (dualBasis i) v = v i := by
  simp [dualBasis]

theorem phase_character (k : Fin 4) (i : Fin 6) :
    phase k i = character (fundamental k i) := by
  simp only [phase, fundamental]
  split_ifs
  · change Complex.I = Complex.I ^ 1; simp
  · change -Complex.I = Complex.I ^ 3; norm_num [pow_succ, Complex.I_mul_I]
  · change (1 : ℂ) = Complex.I ^ 0; simp

theorem phase_single (k : Fin 4) (i : Fin 6) :
    FundamentalRepresentation.rho (phaseElement k) (Pi.single i 1) =
      phase k i • Pi.single i 1 := by
  funext j
  rw [phase_action]
  by_cases h : i = j
  · subst j; simp
  · simp [Pi.single_eq_of_ne (Ne.symm h)]

theorem exterior_phase (k : Fin 4) (p : ExteriorSquareCoordinates.Pair 6) :
    ConcreteSU6Representations.exteriorTwo.rho (phaseElement k) (exteriorBasis p) =
      character (fundamental k p.val.1 + fundamental k p.val.2) • exteriorBasis p := by
  apply exteriorCoordinates.toLinearEquiv.injective
  change exteriorCoordinates
      (ConcreteSU6Representations.exteriorTwo.rho (phaseElement k) (exteriorBasis p)) =
    exteriorCoordinates (_ • exteriorBasis p)
  rw [exteriorCoordinates_action]
  simp only [map_smul, exteriorBasis_coordinates, ExteriorSquareCoordinates.basis_apply,
    exteriorPower.map_apply_ιMulti]
  rw [character_add, ← phase_character, ← phase_character]
  have he : (FundamentalRepresentation.rho (phaseElement k)) ∘
      ![Pi.single p.val.1 1, Pi.single p.val.2 1] =
      ![phase k p.val.1 • Pi.single p.val.1 1, phase k p.val.2 • Pi.single p.val.2 1] := by
    funext j
    fin_cases j <;> simp [phase_single]
  rw [he]
  convert (exteriorPower.ιMulti ℂ 2).map_smul_univ
    ![phase k p.val.1, phase k p.val.2] ![Pi.single p.val.1 1, Pi.single p.val.2 1] using 1
  · congr 1; funext j; fin_cases j <;> rfl
  · simp [Fin.prod_univ_two]

theorem dual_phase (k : Fin 4) (i : Fin 6) :
    ConcreteSU6Representations.antifundamental.rho (phaseElement k) (dualBasis i) =
      character (-fundamental k i) • dualBasis i := by
  apply dualCoordinates.toLinearEquiv.injective
  change dualCoordinates
      (ConcreteSU6Representations.antifundamental.rho (phaseElement k) (dualBasis i)) =
    dualCoordinates (_ • dualBasis i)
  apply LinearMap.ext
  intro v
  rw [dualCoordinates_action]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, dualBasis_coordinates]
  have hh := congrArg (fun z : Six => z i)
    (Representation.self_inv_apply FundamentalRepresentation.rho (phaseElement k) v)
  rw [phase_action] at hh
  calc
    _ = 1 * (FundamentalRepresentation.rho (phaseElement k)⁻¹ v) i := (one_mul _).symm
    _ = (character (-fundamental k i) * phase k i) *
        (FundamentalRepresentation.rho (phaseElement k)⁻¹ v) i := by
      rw [phase_character, character_neg]
    _ = _ := by rw [mul_assoc, hh]

theorem basis_phase (k : Fin 4) (i : Label) :
    uvRho (phaseElement k) (basis i) = character (weight k i) • basis i := by
  rcases i with (p | i) | i
  · change ((_, _), _) = ((_, _), _)
    simp [basis, Module.Basis.prod_apply, weight, exterior_phase]
  · change ((_, _), _) = ((_, _), _)
    simp [basis, Module.Basis.prod_apply, weight, dual_phase]
  · change ((_, _), _) = ((_, _), _)
    simp [basis, Module.Basis.prod_apply, weight, dual_phase]

theorem entry_zero_of (B : LinearMap.BilinForm ℂ UV)
    (hB : ∀ (k : Fin 4) (x y : UV),
      B (uvRho (phaseElement k) x) (uvRho (phaseElement k) y) = B x y)
    (i j : Label) (hij : ¬ allowed i j) : B (basis i) (basis j) = 0 := by
  have hn : ¬ ∀ k : Fin 4, character (weight k i) * character (weight k j) = 1 :=
    fun h => hij ((allowed_iff i j).mp h)
  obtain ⟨k, hk⟩ := not_forall.mp hn
  have he := hB k (basis i) (basis j)
  rw [basis_phase, basis_phase] at he
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at he
  have hz : (character (weight k i) * character (weight k j) - 1) *
      B (basis i) (basis j) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hk)

theorem evaluation_entry_zero (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (i j : Label) (hij : ¬ allowed i j) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H) (basis i) (basis j) = 0 :=
  entry_zero_of _ (evaluation_phase H Y) i j hij

theorem swap_single_zero (k : Fin 4) :
    FundamentalRepresentation.rho (swapElement k) (Pi.single 0 1) =
      Pi.single (⟨k.val + 1, by omega⟩ : Fin 6) 1 := by
  funext i
  rw [swap_action]
  fin_cases k <;> fin_cases i <;>
    norm_num [SignedWeylTransposition.signAt, Equiv.swap_apply_def, Fin.ext_iff, Pi.single_apply]

theorem swap_single_five (k : Fin 4) :
    FundamentalRepresentation.rho (swapElement k) (Pi.single 5 1) = Pi.single 5 1 := by
  have he : (Pi.single 5 1 : Six) = sixth := by
    funext i; fin_cases i <;> norm_num [sixth, Pi.single_apply, Fin.ext_iff]
  rw [he]
  exact swap_sixth k

theorem exterior_swap (k : Fin 4) :
    ConcreteSU6Representations.exteriorTwo.rho (swapElement k) (exteriorBasis (wedgeFive 0)) =
      exteriorBasis (wedgeFive ⟨k.val + 1, by omega⟩) := by
  apply exteriorCoordinates.toLinearEquiv.injective
  change exteriorCoordinates
      (ConcreteSU6Representations.exteriorTwo.rho (swapElement k) (exteriorBasis (wedgeFive 0))) =
    exteriorCoordinates (exteriorBasis (wedgeFive ⟨k.val + 1, by omega⟩))
  rw [exteriorCoordinates_action]
  simp only [exteriorBasis_coordinates, ExteriorSquareCoordinates.basis_apply,
    exteriorPower.map_apply_ιMulti, wedgeFive]
  congr 1
  funext j
  fin_cases j
  · exact swap_single_zero k
  · exact swap_single_five k

theorem dual_swap (k : Fin 4) :
    ConcreteSU6Representations.antifundamental.rho (swapElement k) (dualBasis 0) =
      dualBasis ⟨k.val + 1, by omega⟩ := by
  apply dualCoordinates.toLinearEquiv.injective
  change dualCoordinates
      (ConcreteSU6Representations.antifundamental.rho (swapElement k) (dualBasis 0)) =
    dualCoordinates (dualBasis ⟨k.val + 1, by omega⟩)
  apply LinearMap.ext
  intro v
  rw [dualCoordinates_action, dualBasis_coordinates, dualBasis_coordinates]
  have hh := congrArg (fun z : Six => z ⟨k.val + 1, by omega⟩)
    (Representation.self_inv_apply FundamentalRepresentation.rho (swapElement k) v)
  rw [swap_action] at hh
  have hn : (⟨k.val + 1, by omega⟩ : Fin 6) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simpa only [SignedWeylTransposition.signAt, ite_eq_right_iff.mpr (fun h => False.elim (hn h)),
    Equiv.swap_apply_right, one_mul] using hh

theorem exteriorLabel_swap (k : Fin 4) :
    uvRho (swapElement k) (basis (exteriorLabel 0)) =
      basis (exteriorLabel ⟨k.val + 1, by omega⟩) := by
  change ((_, _), _) = ((_, _), _)
  simp [basis, exteriorLabel, Module.Basis.prod_apply, exterior_swap]

theorem dualLabel_swap (k : Fin 4) (c : Bool) :
    uvRho (swapElement k) (basis (dualLabel c 0)) =
      basis (dualLabel c ⟨k.val + 1, by omega⟩) := by
  cases c <;> change ((_, _), _) = ((_, _), _)
  all_goals simp [basis, dualLabel, Module.Basis.prod_apply, dual_swap]

theorem channel_eq (B : LinearMap.BilinForm ℂ UV)
    (hB : ∀ (k : Fin 4) (x y : UV),
      B (uvRho (swapElement k) x) (uvRho (swapElement k) y) = B x y)
    (a : Fin 5) (c : Bool) :
    B (basis (exteriorLabel a)) (basis (dualLabel c a.castSucc)) =
      B (basis (exteriorLabel 0)) (basis (dualLabel c 0)) := by
  by_cases ha : a = 0
  · subst a; rfl
  · let k : Fin 4 := ⟨a.val - 1, by have := a.isLt; omega⟩
    have he : (⟨k.val + 1, by omega⟩ : Fin 5) = a := by
      apply Fin.ext
      have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
      dsimp [k]
      omega
    have h := hB k (basis (exteriorLabel 0)) (basis (dualLabel c 0))
    rw [exteriorLabel_swap, dualLabel_swap] at h
    change B (basis (exteriorLabel ⟨k.val + 1, by omega⟩))
      (basis (dualLabel c (⟨k.val + 1, by omega⟩ : Fin 5).castSucc)) = _ at h
    rw [he] at h
    exact h

theorem eq_of_entries (B C : LinearMap.BilinForm ℂ UV)
    (hBs : B.IsSymm) (hCs : C.IsSymm)
    (hBp : ∀ (k : Fin 4) (x y : UV),
      B (uvRho (phaseElement k) x) (uvRho (phaseElement k) y) = B x y)
    (hCp : ∀ (k : Fin 4) (x y : UV),
      C (uvRho (phaseElement k) x) (uvRho (phaseElement k) y) = C x y)
    (hBt : ∀ (k : Fin 4) (x y : UV),
      B (uvRho (swapElement k) x) (uvRho (swapElement k) y) = B x y)
    (hCt : ∀ (k : Fin 4) (x y : UV),
      C (uvRho (swapElement k) x) (uvRho (swapElement k) y) = C x y)
    (hc : ∀ c : Bool, B (basis (exteriorLabel 0)) (basis (dualLabel c 0)) =
      C (basis (exteriorLabel 0)) (basis (dualLabel c 0)))
    (hs : ∀ c d : Bool, B (basis (dualLabel c 5)) (basis (dualLabel d 5)) =
      C (basis (dualLabel c 5)) (basis (dualLabel d 5))) : B = C := by
  apply basis.ext
  intro i
  apply basis.ext
  intro j
  change B (basis i) (basis j) = C (basis i) (basis j)
  by_cases hij : allowed i j
  · rcases allowed_cases i j hij with ⟨a, c, rfl, rfl⟩ | ⟨a, c, rfl, rfl⟩ | ⟨c, d, rfl, rfl⟩
    · rw [channel_eq B hBt, channel_eq C hCt]
      exact hc c
    · rw [hBs.eq, hCs.eq, channel_eq B hBt, channel_eq C hCt]
      exact hc c
    · exact hs c d
  · rw [entry_zero_of B hBp i j hij, entry_zero_of C hCp i j hij]

end
end GUT.SU6YukawaBasis

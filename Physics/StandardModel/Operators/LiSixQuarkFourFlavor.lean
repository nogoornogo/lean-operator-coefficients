import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge

open Math

/-! A trivial-residual witness with U = C and D = C^4.
The determinant flavor tensor restores Fermi alternation to the added local line. -/
namespace GUT.LiSixQuarkFourFlavor
set_option autoImplicit false
set_option maxRecDepth 5000
noncomputable section
open Representation SixQuarkFlavorCoordinates SixQuarkFlavorResidualHom
open SixQuarkSpeciesQuotient LiSixQuarkExtension
open scoped TensorProduct

abbrev U := ℂ
abbrev D := Fin 4 → ℂ
abbrev V := SixQuarkTypedFlavor.SlotFlavor U D
abbrev up := Representation.trivial ℂ Unit U
abbrev down := Representation.trivial ℂ Unit D

def determinantPerm : Fin 24 → Fin 4 → Fin 4 := ![![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,2,3,1],![0,3,1,2],![0,3,2,1],![1,0,2,3],![1,0,3,2],![1,2,0,3],![1,2,3,0],![1,3,0,2],![1,3,2,0],![2,0,1,3],![2,0,3,1],![2,1,0,3],![2,1,3,0],![2,3,0,1],![2,3,1,0],![3,0,1,2],![3,0,2,1],![3,1,0,2],![3,1,2,0],![3,2,0,1],![3,2,1,0]]
def determinantSign : Fin 24 → ℂ := ![1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1]

def flavorValue (t : ∀ i, V i) : ℂ :=
  (show ℂ from t 0) * (show ℂ from t 2) * ∑ j : Fin 24, determinantSign j *
    ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
      (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))

set_option maxHeartbeats 1000000 in
def flavor : MultilinearMap ℂ V ℂ :=
  MultilinearMap.mk' flavorValue
    (by
      intro t i x y
      fin_cases i
      all_goals first
        | (have ha : ∀ j : Fin 4, (x + y) j = x j + y j := by intro j; rfl
           simp [flavorValue, Function.update, Fin.ext_iff, Fin.sum_univ_succ,
             determinantSign, determinantPerm, ha]
           ring)
        | (simp [flavorValue, Function.update, Fin.ext_iff, Fin.sum_univ_succ,
             determinantSign, determinantPerm]
           ring))
    (by
      intro t i z x
      fin_cases i
      all_goals first
        | (have ha : ∀ j : Fin 4, (z • x) j = z * x j := by intro j; rfl
           simp [flavorValue, Function.update, Fin.ext_iff, Fin.sum_univ_succ,
             determinantSign, determinantPerm, ha]
           ring)
        | (simp [flavorValue, Function.update, Fin.ext_iff, Fin.sum_univ_succ,
             determinantSign, determinantPerm, smul_eq_mul]
           ring))

set_option maxHeartbeats 1000000 in
theorem flavor_exchange (g : Fin 4) (t : ∀ i, V i) :
    flavor (exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t) =
      -localSign g * flavor t := by
  change flavorValue (exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t) =
    -localSign g * flavorValue t
  unfold flavorValue
  fin_cases g
  · change (show ℂ from t 2) * (show ℂ from t 0) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))) =
      (-(-1) : ℂ) * ((show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))))
    simp [mul_comm]
  · change (show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 3) (determinantPerm j 0) * (show D from t 1) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))) =
      (-1 : ℂ) * ((show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))))
    norm_num [Fin.sum_univ_succ, determinantSign, determinantPerm]
    ring
  · change (show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 4) (determinantPerm j 1) *
        (show D from t 3) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))) =
      (-1 : ℂ) * ((show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))))
    norm_num [Fin.sum_univ_succ, determinantSign, determinantPerm]
    ring
  · change (show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 5) (determinantPerm j 2) * (show D from t 4) (determinantPerm j 3))) =
      (-1 : ℂ) * ((show ℂ from t 0) * (show ℂ from t 2) * (∑ j : Fin 24, determinantSign j *
      ((show D from t 1) (determinantPerm j 0) * (show D from t 3) (determinantPerm j 1) *
        (show D from t 4) (determinantPerm j 2) * (show D from t 5) (determinantPerm j 3))))
    norm_num [Fin.sum_univ_succ, determinantSign, determinantPerm]
    ring

def hom : Hom (SixQuarkTypedFlavor.slotRepresentation U D up down) :=
  MultilinearInvariantHom.fromMultilinear _
    ⟨flavor.smulRight extra, by intro g t; rfl⟩

theorem hom_coordinates (t : ∀ i, V i) :
    homCoordinates (SixQuarkTypedFlavor.slotRepresentation U D up down) hom t =
      flavor t • extra := by
  change PiTensorProduct.lift (flavor.smulRight extra) (PiTensorProduct.tprod ℂ t) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

def admissibleHom : SixQuarkTypedFlavor.StatisticsHom U D up down := ⟨hom, by
  intro g t
  change transform (homCoordinates _ hom (exchangeFlavor g _ t)) g = -homCoordinates _ hom t
  rw [hom_coordinates, hom_coordinates, flavor_exchange]
  change SixQuarkPermutationCompleteness.targetAction g ((-localSign g * flavor t) • extra) = _
  rw [map_smul]
  change (-localSign g * flavor t) • transform extra g = _
  rw [extra_transform, smul_smul]
  fin_cases g <;> simp [localSign]⟩

def witness : ∀ i, V i
  | 0 => (1 : ℂ)
  | 1 => Pi.single 0 1
  | 2 => (1 : ℂ)
  | 3 => Pi.single 1 1
  | 4 => Pi.single 2 1
  | 5 => Pi.single 3 1

set_option maxRecDepth 20000 in
theorem flavor_witness : flavor witness = 1 := by
  change flavorValue witness = 1
  unfold flavorValue
  change (1 : ℂ) * 1 * (∑ j : Fin 24, determinantSign j *
    ((Pi.single 0 (1 : ℂ) : D) (determinantPerm j 0) *
      (Pi.single 1 (1 : ℂ) : D) (determinantPerm j 1) *
      (Pi.single 2 (1 : ℂ) : D) (determinantPerm j 2) *
      (Pi.single 3 (1 : ℂ) : D) (determinantPerm j 3))) = 1
  have he : ∀ j : Fin 24, determinantSign j *
    ((Pi.single 0 (1 : ℂ) : D) (determinantPerm j 0) *
      (Pi.single 1 (1 : ℂ) : D) (determinantPerm j 1) *
      (Pi.single 2 (1 : ℂ) : D) (determinantPerm j 2) *
      (Pi.single 3 (1 : ℂ) : D) (determinantPerm j 3)) = if j = 0 then 1 else 0 := by
    intro j
    fin_cases j <;> norm_num [determinantSign, determinantPerm, Pi.single_apply, Fin.ext_iff]
  simp only [he]
  simp

theorem hom_nonzero : admissibleHom ≠ 0 := by
  intro h
  have he := congrArg (fun k : SixQuarkTypedFlavor.StatisticsHom U D up down =>
    homCoordinates _ k.val witness) h
  change homCoordinates _ hom witness = 0 at he
  rw [hom_coordinates, flavor_witness, one_smul] at he
  exact extra_ne_zero he

theorem separating_probe_witness :
    extraProbe (homCoordinates _ hom witness) = 1 := by
  rw [hom_coordinates, flavor_witness, one_smul, extraProbe_extra]

def physical : DeltaBTwoModelInterface.ModelSector up down :=
  (DeltaBTwoFlavorBridge.sectorHomEquiv up down).symm admissibleHom

theorem physical_nonzero : physical ≠ 0 := by
  exact fun h => hom_nonzero
    ((DeltaBTwoFlavorBridge.sectorHomEquiv up down).symm.map_eq_zero_iff.mp h)

end
end GUT.LiSixQuarkFourFlavor

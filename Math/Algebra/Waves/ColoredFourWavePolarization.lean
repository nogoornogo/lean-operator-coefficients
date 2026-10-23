import Math.Algebra.Constructions.ColoredQuarticWords
import Math.Algebra.Waves.ColoredFourWaveEvaluation

/-! Ordered colored polarization; no group invariance is inferred from waves. -/
namespace Math.ColoredFourWavePolarization
set_option autoImplicit false
noncomputable section
open MvPolynomial ColoredQuarticWords FourWavePolarization
variable {S : Type*}

def assignments : Fin 24 → Fin 4 → Fin 4 := ![
  ![0,1,2,3],
  ![0,1,3,2],
  ![0,2,1,3],
  ![0,2,3,1],
  ![0,3,1,2],
  ![0,3,2,1],
  ![1,0,2,3],
  ![1,0,3,2],
  ![1,2,0,3],
  ![1,2,3,0],
  ![1,3,0,2],
  ![1,3,2,0],
  ![2,0,1,3],
  ![2,0,3,1],
  ![2,1,0,3],
  ![2,1,3,0],
  ![2,3,0,1],
  ![2,3,1,0],
  ![3,0,1,2],
  ![3,0,2,1],
  ![3,1,0,2],
  ![3,1,2,0],
  ![3,2,0,1],
  ![3,2,1,0]]
def inverses : Fin 24 → Fin 4 → Fin 4 := ![
  ![0,1,2,3],
  ![0,1,3,2],
  ![0,2,1,3],
  ![0,3,1,2],
  ![0,2,3,1],
  ![0,3,2,1],
  ![1,0,2,3],
  ![1,0,3,2],
  ![2,0,1,3],
  ![3,0,1,2],
  ![2,0,3,1],
  ![3,0,2,1],
  ![1,2,0,3],
  ![1,3,0,2],
  ![2,1,0,3],
  ![3,1,0,2],
  ![2,3,0,1],
  ![3,2,0,1],
  ![1,2,3,0],
  ![1,3,2,0],
  ![2,1,3,0],
  ![3,1,2,0],
  ![2,3,1,0],
  ![3,2,1,0]]

theorem inverse_left : ∀ p : Fin 24, ∀ i : Fin 4,
    inverses p (assignments p i) = i := by decide +kernel
theorem inverse_right : ∀ p : Fin 24, ∀ i : Fin 4,
    assignments p (inverses p i) = i := by decide +kernel

def permutation (p : Fin 24) : Fin 4 ≃ Fin 4 where
  toFun := assignments p
  invFun := inverses p
  left_inv := inverse_left p
  right_inv := inverse_right p

def orders : Fin 5 → Fin 4 → Fin 4 :=
  ![![3,3,3,3],![2,2,2,3],![2,2,3,3],![1,1,2,3],![0,1,2,3]]

def amplitudeProduct {R : Type*} [CommRing R] (v : S → Fin 4 → R)
    (a : Fin 4 → S) (p : Fin 24) : R :=
  v (a 0) (assignments p 0)*v (a 1) (assignments p 1)*
    v (a 2) (assignments p 2)*v (a 3) (assignments p 3)

theorem permanent_sum {R : Type*} [CommRing R] (a b c d : Fin 4 → R) :
    permanent a b c d = ∑ p : Fin 24,
      a (assignments p 0)*b (assignments p 1)*c (assignments p 2)*d (assignments p 3) := by
  simp [permanent,assignments,Fin.sum_univ_succ]
  ring

def moment {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (r : Fin 5) (i j l m : Fin 4) : R := match r with
  | 0 => permanent (v (a 0)) (v (a 1)) (v (a 2))
      (fun s => v (a 3) s*k s i*k s j*k s l*k s m)
  | 1 => permanent (v (a 0)) (v (a 1))
      (fun s => v (a 2) s*k s i*k s j*k s l) (fun s => v (a 3) s*k s m)
  | 2 => permanent (v (a 0)) (v (a 1))
      (fun s => v (a 2) s*k s i*k s j) (fun s => v (a 3) s*k s l*k s m)
  | 3 => permanent (v (a 0)) (fun s => v (a 1) s*k s i*k s j)
      (fun s => v (a 2) s*k s l) (fun s => v (a 3) s*k s m)
  | 4 => permanent (fun s => v (a 0) s*k s i) (fun s => v (a 1) s*k s j)
      (fun s => v (a 2) s*k s l) (fun s => v (a 3) s*k s m)

private theorem moment_expansion0 {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (i j l m : Fin 4) :
    moment k v a 0 i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders 0 0)) i*k (assignments p (orders 0 1)) j*
        k (assignments p (orders 0 2)) l*k (assignments p (orders 0 3)) m) := by
  rw [moment,permanent_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [amplitudeProduct,orders]
  ring

private theorem moment_expansion1 {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (i j l m : Fin 4) :
    moment k v a 1 i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders 1 0)) i*k (assignments p (orders 1 1)) j*
        k (assignments p (orders 1 2)) l*k (assignments p (orders 1 3)) m) := by
  rw [moment,permanent_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [amplitudeProduct,orders]
  ring

private theorem moment_expansion2 {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (i j l m : Fin 4) :
    moment k v a 2 i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders 2 0)) i*k (assignments p (orders 2 1)) j*
        k (assignments p (orders 2 2)) l*k (assignments p (orders 2 3)) m) := by
  rw [moment,permanent_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [amplitudeProduct,orders]
  ring

private theorem moment_expansion3 {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (i j l m : Fin 4) :
    moment k v a 3 i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders 3 0)) i*k (assignments p (orders 3 1)) j*
        k (assignments p (orders 3 2)) l*k (assignments p (orders 3 3)) m) := by
  rw [moment,permanent_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [amplitudeProduct,orders]
  ring

private theorem moment_expansion4 {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (i j l m : Fin 4) :
    moment k v a 4 i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders 4 0)) i*k (assignments p (orders 4 1)) j*
        k (assignments p (orders 4 2)) l*k (assignments p (orders 4 3)) m) := by
  rw [moment,permanent_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [amplitudeProduct,orders]
  ring

theorem moment_expansion {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (v : S → Fin 4 → R) (a : Fin 4 → S) (r : Fin 5) (i j l m : Fin 4) :
    moment k v a r i j l m = ∑ p : Fin 24, amplitudeProduct v a p*
      (k (assignments p (orders r 0)) i*k (assignments p (orders r 1)) j*
        k (assignments p (orders r 2)) l*k (assignments p (orders r 3)) m) := by
  fin_cases r
  · exact moment_expansion0 k v a i j l m
  · exact moment_expansion1 k v a i j l m
  · exact moment_expansion2 k v a i j l m
  · exact moment_expansion3 k v a i j l m
  · exact moment_expansion4 k v a i j l m

theorem sum_reorder {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin 2 → Fin 2 → Fin 24 → R) (m : Fin n → Fin 24 → R) :
    (∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin n, ∑ p : Fin 24, c x y p*m a p) =
      ∑ p : Fin 24, (∑ x : Fin 2, ∑ y : Fin 2, c x y p)*(∑ a : Fin n, m a p) := by
  calc
    _ = ∑ x : Fin 2, ∑ y : Fin 2, ∑ p : Fin 24, c x y p*(∑ a : Fin n, m a p) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ = ∑ x : Fin 2, ∑ p : Fin 24, ∑ y : Fin 2, c x y p*(∑ a : Fin n, m a p) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ p : Fin 24, ∑ x : Fin 2, ∑ y : Fin 2, c x y p*(∑ a : Fin n, m a p) :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]

variable (k : Fin 4 → Fin 4 → ℂ) (v : S → Fin 4 → ℂ)

theorem evaluation_field (s : S) :
    ColoredFourWaveEvaluation.evaluation k v (field s) = linear (v s) :=
  ColoredFourWaveEvaluation.field_value k v s

theorem evaluation_j1 (s : S) (i : Fin 4) :
    ColoredFourWaveEvaluation.evaluation k v (j1 s (E i)) =
      linear (fun t => v s t*k t i) := by
  simp only [j1,E,dirD_single,one_smul]
  rw [ColoredFourWaveEvaluation.derivative,evaluation_field,ColoredFourWaveEvaluation.d_linear]
  apply congrArg linear
  funext t
  ring

theorem evaluation_j2 (s : S) (i j : Fin 4) :
    ColoredFourWaveEvaluation.evaluation k v (j2 s (E i) (E j)) =
      linear (fun t => v s t*k t i*k t j) := by
  simp only [j2,E,dirD_single,one_smul]
  rw [ColoredFourWaveEvaluation.derivative,evaluation_j1,ColoredFourWaveEvaluation.d_linear]
  apply congrArg linear
  funext t
  ring

theorem evaluation_j3 (s : S) (i j l : Fin 4) :
    ColoredFourWaveEvaluation.evaluation k v (j3 s (E i) (E j) (E l)) =
      linear (fun t => v s t*k t i*k t j*k t l) := by
  simp only [j3,E,dirD_single,one_smul]
  rw [ColoredFourWaveEvaluation.derivative,evaluation_j2,ColoredFourWaveEvaluation.d_linear]
  apply congrArg linear
  funext t
  ring

theorem evaluation_j4 (s : S) (i j l m : Fin 4) :
    ColoredFourWaveEvaluation.evaluation k v (j4 s (E i) (E j) (E l) (E m)) =
      linear (fun t => v s t*k t i*k t j*k t l*k t m) := by
  simp only [j4,E,dirD_single,one_smul]
  rw [ColoredFourWaveEvaluation.derivative,evaluation_j3,ColoredFourWaveEvaluation.d_linear]
  apply congrArg linear
  funext t
  ring

theorem word_value (a : Fin 4 → S) (r : Fin 5) (i j l m : Fin 4) :
    ColoredFourWaveEvaluation.onJets k v (word a r (E i) (E j) (E l) (E m)) =
      moment k v a r i j l m := by
  change FourWaveEvaluation.coefficient
    (ColoredFourWaveEvaluation.evaluation k v (word a r (E i) (E j) (E l) (E m))) = _
  fin_cases r
  all_goals simp only [word,map_mul,evaluation_field,evaluation_j1,evaluation_j2,
    evaluation_j3,evaluation_j4,moment,coefficient_product]

end
end Math.ColoredFourWavePolarization

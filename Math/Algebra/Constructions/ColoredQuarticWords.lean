import Math.Algebra.Constructions.ScalarDegreeFour
import Math.Algebra.Jets.JetDirections

/-! Four independently labelled fields and the five derivative partitions.
There is no symmetry, equation or candidate-span hypothesis in this source. -/
namespace Math.ColoredQuarticWords
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {S : Type*}
abbrev A (S : Type*) := ScalarJetAlgebra.Algebra S (Fin 4)
abbrev Dir := Fin 4 →₀ ℂ
abbrev V (S : Type*) := ScalarJetAlgebra.grade (S := S) (I := Fin 4) 4 4
abbrev D := ScalarJetAlgebra.totalDerivative (S := S) (I := Fin 4)
def field (s : S) : A S := X (s,0)
abbrev E (i : Fin 4) : Dir := Finsupp.single i 1

def dirD : Dir →ₗ[ℂ] Derivation ℂ (A S) (A S) :=
  ∑ i : Fin 4, (Finsupp.lapply i).smulRight (D i)

theorem dirD_apply (u : Dir) (p : A S) : dirD u p = ∑ i : Fin 4, u i • D i p := by
  simp [dirD,Derivation.smul_apply]

@[simp] theorem dirD_single (i : Fin 4) (c : ℂ) :
    (dirD (Finsupp.single i c) : Derivation ℂ (A S) (A S)) = c • D i := by
  simp [dirD,Finsupp.single_apply]

theorem dirD_commute (u v : Dir) (p : A S) : dirD u (dirD v p) = dirD v (dirD u p) := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, (u i*v j) • D i (D j p) := by
      rw [dirD_apply]
      simp only [dirD_apply,map_sum,Derivation.map_smul,Finset.smul_sum,smul_smul]
    _ = ∑ j : Fin 4, ∑ i : Fin 4, (v j*u i) • D j (D i p) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [ScalarJetAlgebra.totalDerivative_commute,mul_comm]
    _ = _ := by
      rw [dirD_apply]
      simp only [dirD_apply,map_sum,Derivation.map_smul,Finset.smul_sum,smul_smul]

theorem dirD_grade (u : Dir) {n d : ℕ} {p : A S}
    (hp : p ∈ ScalarJetAlgebra.grade n d) : dirD u p ∈ ScalarJetAlgebra.grade n (d+1) := by
  rw [dirD_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (ScalarJetAlgebra.totalDerivative_mem i hp))

def j1 (s : S) (u : Dir) : A S := dirD u (field s)
def j2 (s : S) (u v : Dir) : A S := dirD u (j1 s v)
def j3 (s : S) (u v w : Dir) : A S := dirD u (j2 s v w)
def j4 (s : S) (u v w x : Dir) : A S := dirD u (j3 s v w x)

theorem j2_sym (s : S) (u v : Dir) : j2 s u v = j2 s v u :=
  dirD_commute u v (field s)
theorem j3_sym (s : S) (u v w : Dir) : j3 s u v w = j3 s v u w :=
  dirD_commute u v (j1 s w)
theorem j4_sym (s : S) (u v w x : Dir) : j4 s u v w x = j4 s v u w x :=
  dirD_commute u v (j2 s w x)

theorem field_grade (s : S) : field s ∈ ScalarJetAlgebra.grade 1 0 := by
  change (X (s,0) : A S).IsWeightedHomogeneous weight (1,0)
  simpa [weight,order] using isWeightedHomogeneous_X ℂ weight (s,(0 : Fin 4 →₀ ℕ))
theorem j1_grade (s : S) (u : Dir) : j1 s u ∈ ScalarJetAlgebra.grade 1 1 :=
  dirD_grade u (field_grade s)
theorem j2_grade (s : S) (u v : Dir) : j2 s u v ∈ ScalarJetAlgebra.grade 1 2 :=
  dirD_grade u (j1_grade s v)
theorem j3_grade (s : S) (u v w : Dir) : j3 s u v w ∈ ScalarJetAlgebra.grade 1 3 :=
  dirD_grade u (j2_grade s v w)
theorem j4_grade (s : S) (u v w x : Dir) : j4 s u v w x ∈ ScalarJetAlgebra.grade 1 4 :=
  dirD_grade u (j3_grade s v w x)

def word (a : Fin 4 → S) (r : Fin 5) (u v w x : Dir) : A S := match r with
  | 0 => field (a 0)*field (a 1)*field (a 2)*j4 (a 3) u v w x
  | 1 => field (a 0)*field (a 1)*j3 (a 2) u v w*j1 (a 3) x
  | 2 => field (a 0)*field (a 1)*j2 (a 2) u v*j2 (a 3) w x
  | 3 => field (a 0)*j2 (a 1) u v*j1 (a 2) w*j1 (a 3) x
  | 4 => j1 (a 0) u*j1 (a 1) v*j1 (a 2) w*j1 (a 3) x

theorem word_grade (a : Fin 4 → S) (r : Fin 5) (u v w x : Dir) :
    word a r u v w x ∈ V S := by
  fin_cases r
  · exact (((field_grade (a 0)).mul (field_grade (a 1))).mul
      (field_grade (a 2))).mul (j4_grade (a 3) u v w x)
  · exact (((field_grade (a 0)).mul (field_grade (a 1))).mul
      (j3_grade (a 2) u v w)).mul (j1_grade (a 3) x)
  · exact (((field_grade (a 0)).mul (field_grade (a 1))).mul
      (j2_grade (a 2) u v)).mul (j2_grade (a 3) w x)
  · exact (((field_grade (a 0)).mul (j2_grade (a 1) u v)).mul
      (j1_grade (a 2) w)).mul (j1_grade (a 3) x)
  · exact (((j1_grade (a 0) u).mul (j1_grade (a 1) v)).mul
      (j1_grade (a 2) w)).mul (j1_grade (a 3) x)

theorem word_add1 (a : Fin 4 → S) (r : Fin 5) (u y v w x : Dir) :
    word a r (u+y) v w x = word a r u v w x+word a r y v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add2 (a : Fin 4 → S) (r : Fin 5) (u v y w x : Dir) :
    word a r u (v+y) w x = word a r u v w x+word a r u y w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add3 (a : Fin 4 → S) (r : Fin 5) (u v w y x : Dir) :
    word a r u v (w+y) x = word a r u v w x+word a r u v y x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add4 (a : Fin 4 → S) (r : Fin 5) (u v w x y : Dir) :
    word a r u v w (x+y) = word a r u v w x+word a r u v w y := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add]
theorem word_smul1 (a : Fin 4 → S) (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word a r (c • u) v w x = c • word a r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul2 (a : Fin 4 → S) (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word a r u (c • v) w x = c • word a r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul3 (a : Fin 4 → S) (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word a r u v (c • w) x = c • word a r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul4 (a : Fin 4 → S) (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word a r u v w (c • x) = c • word a r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]

def tensor1 (f : A S →ₗ[ℂ] ℂ) (a : Fin 4 → S) (r : Fin 5) (u v w : Dir) : Dir →ₗ[ℂ] ℂ where
  toFun x := f (word a r u v w x)
  map_add' x y := by rw [word_add4,map_add]
  map_smul' c x := by rw [word_smul4,map_smul]; rfl

def tensor2 (f : A S →ₗ[ℂ] ℂ) (a : Fin 4 → S) (r : Fin 5) (u v : Dir) : Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun w := tensor1 f a r u v w
  map_add' w y := by
    apply LinearMap.ext; intro x
    change f (word a r u v (w+y) x) = f (word a r u v w x)+f (word a r u v y x)
    rw [word_add3,map_add]
  map_smul' c w := by
    apply LinearMap.ext; intro x
    change f (word a r u v (c • w) x) = c • f (word a r u v w x)
    rw [word_smul3,map_smul]

def tensor3 (f : A S →ₗ[ℂ] ℂ) (a : Fin 4 → S) (r : Fin 5) (u : Dir) :
    Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun v := tensor2 f a r u v
  map_add' v y := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word a r u (v+y) w x) = f (word a r u v w x)+f (word a r u y w x)
    rw [word_add2,map_add]
  map_smul' c v := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word a r u (c • v) w x) = c • f (word a r u v w x)
    rw [word_smul2,map_smul]

def tensor (f : A S →ₗ[ℂ] ℂ) (a : Fin 4 → S) (r : Fin 5) : Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun u := tensor3 f a r u
  map_add' u y := by
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word a r (u+y) v w x) = f (word a r u v w x)+f (word a r y v w x)
    rw [word_add1,map_add]
  map_smul' c u := by
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word a r (c • u) v w x) = c • f (word a r u v w x)
    rw [word_smul1,map_smul]

@[simp] theorem tensor_apply (f : A S →ₗ[ℂ] ℂ) (a : Fin 4 → S) (r : Fin 5) (u v w x : Dir) :
    tensor f a r u v w x = f (word a r u v w x) := rfl

theorem word_symmetric (a : Fin 4 → S) (r : Fin 4) (u v w x : Dir) :
    word a r.castSucc u v w x = word a r.castSucc v u w x := by
  fin_cases r
  · change word a 0 u v w x = word a 0 v u w x
    simp only [word,j4_sym (a 3) u v]
  · change word a 1 u v w x = word a 1 v u w x
    simp only [word,j3_sym (a 2) u v]
  · change word a 2 u v w x = word a 2 v u w x
    simp only [word,j2_sym (a 2) u v]
  · change word a 3 u v w x = word a 3 v u w x
    simp only [word,j2_sym (a 1) u v]

end
end Math.ColoredQuarticWords

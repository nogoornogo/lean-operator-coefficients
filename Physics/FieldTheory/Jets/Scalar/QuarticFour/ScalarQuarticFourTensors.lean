import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticContractions
import Physics.FieldTheory.Jets.Lorentz.LorentzRankFour
import Math.Algebra.Constructions.ScalarDegreeFour

/-! Polarized quartic words on the actual free scalar source. -/
namespace Physics.ScalarQuarticFourTensors
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM
abbrev Dir := JetDirections.Direction (Fin 4)
abbrev Tensor := LorentzRankFour.Tensor
abbrev V := ScalarJetAlgebra.grade (S := Unit) (I := Fin 4) 4 4
abbrev P := ScalarDerivativeInterface.scalar 0

def dirD : Dir →ₗ[ℂ] Derivation ℂ OffShell OffShell :=
  ∑ i : Fin 4, (Finsupp.lapply i).smulRight (D i)

theorem dirD_apply (u : Dir) (p : OffShell) : dirD u p = ∑ i : Fin 4, u i • D i p := by
  simp [dirD,Derivation.smul_apply]

@[simp] theorem dirD_single (i : Fin 4) (c : ℂ) : dirD (Finsupp.single i c) = c • D i := by
  simp [dirD,Finsupp.single_apply]

theorem dirD_covariant (g : LorentzDirections.Group) (u : Dir) (p : OffShell) :
    offAction g (dirD u p) = dirD (LorentzDirections.direction g u) (offAction g p) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [map_add,hu,hv]
  | single i c =>
    have he : Finsupp.single i c = c • Finsupp.single i (1 : ℂ) := by simp
    simp only [he,map_smul,Derivation.smul_apply,dirD_single,one_smul]
    congr 1
    rw [dirD_apply]
    exact derivative_covariance g i p

theorem dirD_commute (u v : Dir) (p : OffShell) : dirD u (dirD v p) = dirD v (dirD u p) := by
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

theorem dirD_grade (u : Dir) {n d : ℕ} {p : OffShell}
    (hp : p ∈ ScalarJetAlgebra.grade n d) : dirD u p ∈ ScalarJetAlgebra.grade n (d+1) := by
  rw [dirD_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (ScalarJetAlgebra.totalDerivative_mem i hp))

def j1 (u : Dir) : OffShell := dirD u field
def j2 (u v : Dir) : OffShell := dirD u (j1 v)
def j3 (u v w : Dir) : OffShell := dirD u (j2 v w)
def j4 (u v w x : Dir) : OffShell := dirD u (j3 v w x)

theorem j2_sym (u v : Dir) : j2 u v = j2 v u := dirD_commute u v field
theorem j3_sym (u v w : Dir) : j3 u v w = j3 v u w := dirD_commute u v (j1 w)
theorem j4_sym (u v w x : Dir) : j4 u v w x = j4 v u w x := dirD_commute u v (j2 w x)

theorem j1_covariant (g : LorentzDirections.Group) (u : Dir) :
    offAction g (j1 u) = j1 (LorentzDirections.direction g u) := by
  simp only [j1,dirD_covariant,field_invariant]
theorem j2_covariant (g : LorentzDirections.Group) (u v : Dir) :
    offAction g (j2 u v) = j2 (LorentzDirections.direction g u) (LorentzDirections.direction g v) := by
  simp only [j2,dirD_covariant,j1_covariant]
theorem j3_covariant (g : LorentzDirections.Group) (u v w : Dir) :
    offAction g (j3 u v w) = j3 (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) (LorentzDirections.direction g w) := by
  simp only [j3,dirD_covariant,j2_covariant]
theorem j4_covariant (g : LorentzDirections.Group) (u v w x : Dir) :
    offAction g (j4 u v w x) = j4 (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) (LorentzDirections.direction g w)
      (LorentzDirections.direction g x) := by
  simp only [j4,dirD_covariant,j3_covariant]

theorem stable : ∀ g, V ≤ V.comap (P.action g) := by
  intro g p hp
  exact JetFunctor.polynomialMap_homogeneous _
    (JetDirections.combined_order LorentzJetIBP.scalarField LorentzDirections.direction g) hp

def selected := P.select V stable

theorem j1_grade (u : Dir) : j1 u ∈ ScalarJetAlgebra.grade 1 1 :=
  dirD_grade u ScalarQuarticTwoCompleteness.field_grade
theorem j2_grade (u v : Dir) : j2 u v ∈ ScalarJetAlgebra.grade 1 2 :=
  dirD_grade u (j1_grade v)
theorem j3_grade (u v w : Dir) : j3 u v w ∈ ScalarJetAlgebra.grade 1 3 :=
  dirD_grade u (j2_grade v w)
theorem j4_grade (u v w x : Dir) : j4 u v w x ∈ ScalarJetAlgebra.grade 1 4 :=
  dirD_grade u (j3_grade v w x)

/-- The five derivative partitions; no spanning premise is included. -/
def word (r : Fin 5) (u v w x : Dir) : OffShell := match r with
  | 0 => field^3*j4 u v w x
  | 1 => field^2*j3 u v w*j1 x
  | 2 => field^2*j2 u v*j2 w x
  | 3 => field*j2 u v*j1 w*j1 x
  | 4 => j1 u*j1 v*j1 w*j1 x

theorem word_grade (r : Fin 5) (u v w x : Dir) : word r u v w x ∈ V := by
  open ScalarQuarticTwoCompleteness in
  fin_cases r
  · exact (field_power_grade 3).mul (j4_grade u v w x)
  · exact ((field_power_grade 2).mul (j3_grade u v w)).mul (j1_grade x)
  · exact ((field_power_grade 2).mul (j2_grade u v)).mul (j2_grade w x)
  · exact ((field_grade.mul (j2_grade u v)).mul (j1_grade w)).mul (j1_grade x)
  · exact (((j1_grade u).mul (j1_grade v)).mul (j1_grade w)).mul (j1_grade x)

theorem word_covariant (r : Fin 5) (g : LorentzDirections.Group) (u v w x : Dir) :
    offAction g (word r u v w x) = word r (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) (LorentzDirections.direction g w)
      (LorentzDirections.direction g x) := by
  fin_cases r <;> simp only [word,map_mul,map_pow,field_invariant,
    j1_covariant,j2_covariant,j3_covariant,j4_covariant]

theorem word_add1 (r : Fin 5) (u y v w x : Dir) :
    word r (u+y) v w x = word r u v w x+word r y v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add2 (r : Fin 5) (u v y w x : Dir) :
    word r u (v+y) w x = word r u v w x+word r u y w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add3 (r : Fin 5) (u v w y x : Dir) :
    word r u v (w+y) x = word r u v w x+word r u v y x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add,add_mul]
theorem word_add4 (r : Fin 5) (u v w x y : Dir) :
    word r u v w (x+y) = word r u v w x+word r u v w y := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_add,mul_add]
theorem word_smul1 (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word r (c • u) v w x = c • word r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul2 (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word r u (c • v) w x = c • word r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul3 (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word r u v (c • w) x = c • word r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]
theorem word_smul4 (r : Fin 5) (c : ℂ) (u v w x : Dir) :
    word r u v w (c • x) = c • word r u v w x := by
  fin_cases r <;> simp [word,j1,j2,j3,j4,map_smul,Derivation.smul_apply]

def tensor1 (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) (u v w : Dir) : Dir →ₗ[ℂ] ℂ where
  toFun x := f (word r u v w x)
  map_add' x y := by rw [word_add4,map_add]
  map_smul' c x := by rw [word_smul4,map_smul]; rfl

def tensor2 (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) (u v : Dir) : Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun w := tensor1 f r u v w
  map_add' w y := by
    apply LinearMap.ext; intro x
    change f (word r u v (w+y) x) = f (word r u v w x)+f (word r u v y x)
    rw [word_add3,map_add]
  map_smul' c w := by
    apply LinearMap.ext; intro x
    change f (word r u v (c • w) x) = c • f (word r u v w x)
    rw [word_smul3,map_smul]

def tensor3 (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) (u : Dir) :
    Dir →ₗ[ℂ] Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun v := tensor2 f r u v
  map_add' v y := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word r u (v+y) w x) = f (word r u v w x)+f (word r u y w x)
    rw [word_add2,map_add]
  map_smul' c v := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word r u (c • v) w x) = c • f (word r u v w x)
    rw [word_smul2,map_smul]

def tensor (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) : Tensor where
  toFun u := tensor3 f r u
  map_add' u y := by
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word r (u+y) v w x) = f (word r u v w x)+f (word r y v w x)
    rw [word_add1,map_add]
  map_smul' c u := by
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    change f (word r (c • u) v w x) = c • f (word r u v w x)
    rw [word_smul1,map_smul]

@[simp] theorem tensor_apply (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) (u v w x : Dir) :
    tensor f r u v w x = f (word r u v w x) := rfl

theorem tensor_symmetric (f : OffShell →ₗ[ℂ] ℂ) (r : Fin 5) (u v w x : Dir) :
    tensor f r u v w x = tensor f r v u w x := by
  simp only [tensor_apply]
  apply congrArg f
  fin_cases r
  · simp only [word,j4_sym u v]
  · simp only [word,j3_sym u v]
  · simp only [word,j2_sym u v]
  · simp only [word,j2_sym u v]
  · simp only [word]; ring

theorem tensor_invariant (f : OffShell →ₗ[ℂ] ℂ)
    (hInv : ∀ g p, p ∈ V → f (offAction g p) = f p) (r : Fin 5)
    (g : LorentzDirections.Group) (u v w x : Dir) :
    tensor f r (LorentzDirections.direction g u) (LorentzDirections.direction g v)
      (LorentzDirections.direction g w) (LorentzDirections.direction g x) = tensor f r u v w x := by
  simpa only [tensor_apply,word_covariant] using hInv g (word r u v w x) (word_grade r u v w x)

end
end Physics.ScalarQuarticFourTensors

import Math.Algebra.Jets.ScalarJetGrading
import Math.LinearAlgebra.Symmetric.PhyslibSymmetricDerivations
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! Functorial internal linear maps on unbounded jets in a specified field basis.
Generators are source vectors; coefficient functionals belong to the dual. -/
namespace Math.JetLinear
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra

abbrev Field (S : Type*) := S →₀ ℂ
abbrev Jet (S I : Type*) := Index S I →₀ ℂ

variable {S T U I : Type*}

def atOrder (α : I →₀ ℕ) : Field S →ₗ[ℂ] Jet S I :=
  Finsupp.lmapDomain ℂ ℂ (fun s => (s, α))

@[simp] theorem atOrder_single (α : I →₀ ℕ) (s : S) (c : ℂ) :
    atOrder α (Finsupp.single s c) = Finsupp.single (s, α) c := by
  simp [atOrder]

def map (f : Field S →ₗ[ℂ] Field T) : Jet S I →ₗ[ℂ] Jet T I :=
  Finsupp.linearCombination ℂ (fun j => atOrder j.2 (f (Finsupp.single j.1 1)))

@[simp] theorem map_single (f : Field S →ₗ[ℂ] Field T) (s : S) (α : I →₀ ℕ) (c : ℂ) :
    map f (Finsupp.single (s, α) c) = c • atOrder α (f (Finsupp.single s 1)) := by
  simp [map]

theorem map_atOrder (f : Field S →ₗ[ℂ] Field T) (α : I →₀ ℕ) (v : Field S) :
    map f (atOrder α v) = atOrder α (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c =>
    simp only [atOrder_single, map_single]
    rw [show Finsupp.single s c = c • Finsupp.single s (1 : ℂ) by simp,
      map_smul, map_smul]

@[simp] theorem map_id : map (I := I) (LinearMap.id : Field S →ₗ[ℂ] Field S) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j c
  obtain ⟨s, α⟩ := j
  simp

theorem map_comp (f : Field S →ₗ[ℂ] Field T) (g : Field T →ₗ[ℂ] Field U) :
    map (I := I) (g.comp f) = (map g).comp (map f) := by
  apply Finsupp.lhom_ext
  intro j c
  obtain ⟨s, α⟩ := j
  simp [map_atOrder]

def shift (i : I) : Jet S I →ₗ[ℂ] Jet S I :=
  Finsupp.lmapDomain ℂ ℂ (ScalarJetAlgebra.shift i)

@[simp] theorem shift_single (i : I) (j : Index S I) (c : ℂ) :
    shift i (Finsupp.single j c) = Finsupp.single (ScalarJetAlgebra.shift i j) c := by
  simp [shift]

theorem shift_atOrder (i : I) (α : I →₀ ℕ) (v : Field S) :
    shift i (atOrder α v) = atOrder (α + Finsupp.single i 1) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c => simp [ScalarJetAlgebra.shift]

theorem map_shift (f : Field S →ₗ[ℂ] Field T) (i : I) (v : Jet S I) :
    map f (shift i v) = shift i (map f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, α⟩ := j
    simp [ScalarJetAlgebra.shift, shift_atOrder]

theorem shift_commute (i j : I) :
    (shift (S := S) i).comp (shift j) = (shift j).comp (shift i) := by
  apply Finsupp.lhom_ext
  intro x c
  simp [ScalarJetAlgebra.shift, add_comm, add_left_comm]

def action {H : Type*} [Monoid H] (ρ : Representation ℂ H (Field S)) :
    Representation ℂ H (Jet S I) where
  toFun h := map (ρ h)
  map_one' := by rw [ρ.map_one]; exact map_id
  map_mul' h k := by rw [ρ.map_mul]; exact map_comp (ρ k) (ρ h)

def polynomialEquiv : SymmetricAlgebra ℂ (Jet S I) ≃ₐ[ℂ] Algebra S I :=
  SymmetricAlgebra.equivMvPolynomial (Finsupp.basisSingleOne)

@[simp] theorem polynomialEquiv_ι_single (j : Index S I) :
    polynomialEquiv (SymmetricAlgebra.ι ℂ (Jet S I) (Finsupp.single j 1)) =
      MvPolynomial.X j :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply (Finsupp.basisSingleOne) j

def linearForm : Jet S I →ₗ[ℂ] Algebra S I :=
  Finsupp.linearCombination ℂ MvPolynomial.X

theorem polynomialEquiv_ι (v : Jet S I) :
    polynomialEquiv (SymmetricAlgebra.ι ℂ (Jet S I) v) = linearForm v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    have hs : Finsupp.single j c = c • Finsupp.single j (1 : ℂ) := by simp
    simp only [hs, map_smul, polynomialEquiv_ι_single, linearForm,
      Finsupp.linearCombination_single, one_smul]

def polynomialMap (f : Field S →ₗ[ℂ] Field T) : Algebra S I →ₐ[ℂ] Algebra T I :=
  MvPolynomial.aeval (fun j => linearForm (map f (Finsupp.single j 1)))

@[simp] theorem polynomialMap_X (f : Field S →ₗ[ℂ] Field T) (j : Index S I) :
    polynomialMap f (MvPolynomial.X j) = linearForm (map f (Finsupp.single j 1)) := by
  simp [polynomialMap]

theorem polynomialMap_linearForm (f : Field S →ₗ[ℂ] Field T) (v : Jet S I) :
    polynomialMap f (linearForm v) = linearForm (map f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    have hs : Finsupp.single j c = c • Finsupp.single j (1 : ℂ) := by simp
    simp only [hs, map_smul, linearForm, Finsupp.linearCombination_single, one_smul,
      polynomialMap_X]

theorem polynomialMap_comp (f : Field S →ₗ[ℂ] Field T) (g : Field T →ₗ[ℂ] Field U) :
    polynomialMap (I := I) (g.comp f) = (polynomialMap g).comp (polynomialMap f) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [polynomialMap_X, AlgHom.comp_apply, polynomialMap_linearForm]
  exact congrArg linearForm (LinearMap.congr_fun (map_comp f g) _)

@[simp] theorem polynomialMap_id :
    polynomialMap (I := I) (LinearMap.id : Field S →ₗ[ℂ] Field S) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [linearForm]

theorem derivative_linearForm (i : I) (v : Jet S I) :
    totalDerivative i (linearForm v) = linearForm (shift i v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c => simp [linearForm]

theorem derivative_polynomialMap (f : Field S →ₗ[ℂ] Field T) (i : I) (p : Algebra S I) :
    totalDerivative i (polynomialMap f p) = polynomialMap f (totalDerivative i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, totalDerivative_mul, polynomialMap_X, derivative_linearForm,
      totalDerivative_X, map_add, hp, ← map_shift, shift_single]

theorem linearForm_atOrder_homogeneous (α : I →₀ ℕ) (v : Field S) :
    (linearForm (atOrder α v)).IsWeightedHomogeneous weight (1, order α) := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ weight (1, order α)
  | add v w hv hw => simpa only [map_add] using hv.add hw
  | single s c =>
    simp only [atOrder_single, linearForm, Finsupp.linearCombination_single]
    exact (MvPolynomial.weightedHomogeneousSubmodule ℂ weight (1, order α)).smul_mem c
      (MvPolynomial.isWeightedHomogeneous_X ℂ weight (s, α))

theorem polynomialMap_X_homogeneous (f : Field S →ₗ[ℂ] Field T) (j : Index S I) :
    (polynomialMap f (MvPolynomial.X j)).IsWeightedHomogeneous weight (weight j) := by
  obtain ⟨s, α⟩ := j
  rw [polynomialMap_X]
  simpa only [map_single, one_smul, weight] using
    linearForm_atOrder_homogeneous α (f (Finsupp.single s 1))

theorem polynomialMap_homogeneous (f : Field S →ₗ[ℂ] Field T)
    {g : ℕ × ℕ} {p : Algebra S I} (hp : p.IsWeightedHomogeneous weight g) :
    (polynomialMap f p).IsWeightedHomogeneous weight g := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ weight g
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial a c ha =>
    rw [polynomialMap, MvPolynomial.aeval_monomial]
    have h := MvPolynomial.IsWeightedHomogeneous.prod a.support
      (fun j => linearForm (map f (Finsupp.single j 1)) ^ a j)
      (fun j => a j • weight j) (fun j _ => by
        simpa only [polynomialMap_X] using (polynomialMap_X_homogeneous f j).pow (a j))
    have hw : (∑ j ∈ a.support, a j • weight j) = g := ha
    rw [hw] at h
    exact h.C_mul c

def gradeMap (f : Field S →ₗ[ℂ] Field T) (n d : ℕ) :
    grade (S := S) (I := I) n d →ₗ[ℂ] grade (S := T) (I := I) n d where
  toFun p := ⟨polynomialMap f p.val, polynomialMap_homogeneous f p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def polynomialAction {H : Type*} [Monoid H] (ρ : Representation ℂ H (Field S)) :
    Representation ℂ H (Algebra S I) where
  toFun h := (polynomialMap (ρ h)).toLinearMap
  map_one' := by
    rw [ρ.map_one]
    change (polynomialMap LinearMap.id).toLinearMap = LinearMap.id
    rw [polynomialMap_id]; rfl
  map_mul' h k := by
    rw [ρ.map_mul]
    change (polynomialMap ((ρ h).comp (ρ k))).toLinearMap = _
    rw [polynomialMap_comp]; rfl

theorem action_atOrder_zero {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (Field S)) (h : H) (v : Field S) :
    action (I := I) ρ h (atOrder 0 v) = atOrder 0 (ρ h v) := map_atOrder (ρ h) 0 v

def symmetricGrade (n d : ℕ) : Submodule ℂ (SymmetricAlgebra ℂ (Jet S I)) :=
  (grade n d).comap polynomialEquiv.toLinearMap

def gradeEquiv (n d : ℕ) : symmetricGrade (S := S) (I := I) n d ≃ₗ[ℂ]
    grade (S := S) (I := I) n d where
  toFun p := ⟨polynomialEquiv p.val, p.property⟩
  invFun p := ⟨polynomialEquiv.symm p.val, by
    change polynomialEquiv (polynomialEquiv.symm p.val) ∈ grade n d
    rw [AlgEquiv.apply_symm_apply]; exact p.property⟩
  left_inv p := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv p := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

instance symmetricGrade_finiteDimensional [Finite S] [Finite I] (n d : ℕ) :
    FiniteDimensional ℂ (symmetricGrade (S := S) (I := I) n d) :=
  FiniteDimensional.of_injective (gradeEquiv n d).toLinearMap (gradeEquiv n d).injective

def gradeAction {H : Type*} [Monoid H] (ρ : Representation ℂ H (Field S)) (n d : ℕ) :
    Representation ℂ H (grade (S := S) (I := I) n d) where
  toFun h := gradeMap (ρ h) n d
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialMap (ρ 1) p.val = p.val
    rw [ρ.map_one]
    change polynomialMap LinearMap.id p.val = p.val
    rw [polynomialMap_id]; rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialMap (ρ (h * k)) p.val =
      polynomialMap (ρ h) (polynomialMap (ρ k) p.val)
    rw [ρ.map_mul]
    change polynomialMap ((ρ h).comp (ρ k)) p.val = _
    rw [polynomialMap_comp]; rfl

theorem derivative_gradeMap (f : Field S →ₗ[ℂ] Field T) (i : I) (n d : ℕ)
    (p : grade (S := S) (I := I) n d) :
    derivative i n d (gradeMap f n d p) =
      gradeMap f n (d + 1) (derivative i n d p) :=
  Subtype.ext (derivative_polynomialMap f i p.val)

theorem polynomialEquiv_derivative (i : I) (p : SymmetricAlgebra ℂ (Jet S I)) :
    polynomialEquiv (PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear (shift i) p) =
      totalDerivative i (polynomialEquiv p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι v => simp only [PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_ι,
      polynomialEquiv_ι, derivative_linearForm]
  | mul p q hp hq =>
    simp only [PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_mul, map_add,
      map_mul, totalDerivative_mul, hp, hq]
    ring
  | add p q hp hq => simp only [map_add, hp, hq]

theorem polynomialEquiv_map (f : Field S →ₗ[ℂ] Field T)
    (p : SymmetricAlgebra ℂ (Jet S I)) :
    polynomialEquiv (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι ℂ (Jet T I)).comp (map f)) p) =
      polynomialMap f (polynomialEquiv p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι v => simp [polynomialEquiv_ι, polynomialMap_linearForm]
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

def shear (t : ℂ) : Field (Fin 2) →ₗ[ℂ] Field (Fin 2) :=
  LinearMap.id + t • (Finsupp.lsingle 0).comp (Finsupp.lapply 1)

@[simp] theorem shear_zero (t : ℂ) : shear t (Finsupp.single 0 1) = Finsupp.single 0 1 := by
  simp [shear]

@[simp] theorem shear_one (t : ℂ) :
    shear t (Finsupp.single 1 1) = Finsupp.single 1 1 + t • Finsupp.single 0 1 := by
  simp [shear]

theorem shear_polynomial (t : ℂ) (α : I →₀ ℕ) :
    polynomialMap (shear t) (MvPolynomial.X (1, α)) =
      MvPolynomial.X (1, α) + t • MvPolynomial.X (0, α) := by
  simp [polynomialMap_X, linearForm]

theorem shear_inverse (t : ℂ) : (shear (-t)).comp (shear t) = LinearMap.id := by
  ext v s
  simp [shear]

end
end Math.JetLinear

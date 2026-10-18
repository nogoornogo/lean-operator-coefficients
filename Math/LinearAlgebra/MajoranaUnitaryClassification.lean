import Math.LinearAlgebra.UnitaryMajoranaBlocks
import Math.LinearAlgebra.MajoranaPhaseNormalization
import Mathlib.LinearAlgebra.Matrix.Reindex
import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport

/-! Full unitary classification of specified diagonal Majorana coefficients,
indexed by their absolute values, and algebraic residual-Hom transport. -/
namespace Math.MajoranaUnitaryClassification
set_option autoImplicit false
noncomputable section
open Matrix UnitaryDiagonalCongruence
variable {I N : Type*} [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]

def reindexUnitary (e : N ≃ I) (U : unitaryGroup I ℂ) : unitaryGroup N ℂ :=
  ⟨U.val.submatrix e e, by
    rw [mem_unitaryGroup_iff]
    have hs : star (U.val.submatrix e e) = (star U.val).submatrix e e := rfl
    rw [hs, submatrix_mul_equiv, U.property.2, submatrix_one_equiv]⟩

def reindexEquiv (c : I → ℂ) (e : N ≃ I) : subgroup c ≃* subgroup (c ∘ e) where
  toFun U := ⟨reindexUnitary e U.val, by
    change Preserves (c ∘ e) (reindexUnitary e U.val).val
    rw [entry_iff]
    intro i j
    exact (entry_iff c U.val).mp U.property (e i) (e j)⟩
  invFun U := ⟨reindexUnitary e.symm U.val, by
    change Preserves c (reindexUnitary e.symm U.val).val
    rw [entry_iff]
    intro i j
    simpa [reindexUnitary] using (entry_iff (c ∘ e) U.val).mp U.property (e.symm i) (e.symm j)⟩
  left_inv U := by apply Subtype.ext; apply Subtype.ext; ext i j; simp [reindexUnitary]
  right_inv U := by apply Subtype.ext; apply Subtype.ext; ext i j; simp [reindexUnitary]
  map_mul' U V := by
    apply Subtype.ext; apply Subtype.ext
    exact (submatrix_mul_equiv U.val.val V.val.val e e e).symm

def Mass (c : I → ℂ) := {r : ℝ // r ∈ Finset.univ.image (fun i => ‖c i‖)}

instance massFintype (c : I → ℂ) : Fintype (Mass c) := by
  classical
  unfold Mass
  infer_instance
instance massDecidableEq (c : I → ℂ) : DecidableEq (Mass c) := Classical.decEq _

def Fiber (c : I → ℂ) (r : Mass c) := {i : I // ‖c i‖ = r.val}

instance fiberFintype (c : I → ℂ) (r : Mass c) : Fintype (Fiber c r) := by
  classical
  unfold Fiber
  infer_instance
instance fiberDecidableEq (c : I → ℂ) (r : Mass c) : DecidableEq (Fiber c r) := Classical.decEq _

def indexEquiv (c : I → ℂ) : (Σ r : Mass c, Fiber c r) ≃ I where
  toFun x := x.2.val
  invFun i := ⟨⟨‖c i‖, by
    classical
    simp⟩, ⟨i, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    change ‖c i‖ = r at hi
    subst r
    rfl
  right_inv _ := rfl

omit [DecidableEq I] in
theorem mass_normSq_injective (c : I → ℂ) :
    Function.Injective (fun r : Mass c => Complex.normSq (r.val : ℂ)) := by
  intro r s h
  apply Subtype.ext
  have hr : 0 ≤ r.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp r.property
    rw [← hi]; exact norm_nonneg _
  have hs : 0 ≤ s.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
    rw [← hi]; exact norm_nonneg _
  simp only [Complex.normSq_ofReal] at h
  have hz : (r.val - s.val) * (r.val + s.val) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · exact sub_eq_zero.mp hz
  · linarith

/-- Complete product coordinates, with no supplied partition or normalizer premise. -/
def localClassification (c : I → ℂ) : subgroup c ≃*
    (∀ r : Mass c, subgroup (fun _ : Fiber c r => (r.val : ℂ))) := by
  let e := (MajoranaPhaseNormalization.normalizationEquiv c).trans
    (reindexEquiv (fun i => (‖c i‖ : ℂ)) (indexEquiv c))
  have he : (fun i => (‖c i‖ : ℂ)) ∘ indexEquiv c =
      (fun x : Σ r : Mass c, Fiber c r => (x.1.val : ℂ)) := by
    funext x
    exact congrArg Complex.ofReal x.2.property
  let f : subgroup (fun x : Σ r : Mass c, Fiber c r => (x.1.val : ℂ)) ≃*
      (∀ r : Mass c, subgroup (fun _ : Fiber c r => (r.val : ℂ))) :=
    UnitaryMajoranaBlocks.productEquiv (J := Fiber c) (fun r : Mass c => (r.val : ℂ))
      (mass_normSq_injective c)
  have g : subgroup ((fun i => (‖c i‖ : ℂ)) ∘ indexEquiv c) ≃*
      subgroup (fun x : Σ r : Mass c, Fiber c r => (x.1.val : ℂ)) :=
    MulEquiv.subgroupCongr (congrArg subgroup he)
  exact (e.trans g).trans f

def zeroEquiv (r : ℂ) (hr : r = 0) : subgroup (fun _ : N => r) ≃* unitaryGroup N ℂ := by
  subst r
  exact
    { toFun := fun U => U.val
      invFun := fun U => ⟨U, by change Preserves (fun _ => 0) U.val; simp [Preserves]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

abbrev Coordinates (c : I → ℂ) :=
  (∀ r : {r : Mass c // r.val = 0}, unitaryGroup (Fiber c r.val) ℂ) ×
  (∀ r : {r : Mass c // r.val ≠ 0}, orthogonalGroup (Fiber c r.val) ℝ)

def splitEquiv (c : I → ℂ) :
    (∀ r : Mass c, subgroup (fun _ : Fiber c r => (r.val : ℂ))) ≃* Coordinates c := by
  classical
  exact
    { toFun := fun U =>
        (fun r => zeroEquiv (r.val.val : ℂ) (by simp [r.property]) (U r.val),
         fun r => constantEquiv (r.val.val : ℂ) (Complex.ofReal_ne_zero.mpr r.property) (U r.val))
      invFun := fun U r => if hr : r.val = 0 then
          (zeroEquiv (r.val : ℂ) (by simp [hr])).symm (U.1 ⟨r, hr⟩)
        else (constantEquiv (r.val : ℂ) (Complex.ofReal_ne_zero.mpr hr)).symm (U.2 ⟨r, hr⟩)
      left_inv := by
        intro U; funext r
        by_cases hr : r.val = 0 <;> simp [hr]
      right_inv := by
        intro U
        apply Prod.ext
        · funext r; simp [r.property]
        · funext r; simp [r.property]
      map_mul' := by
        intro U V
        apply Prod.ext
        · funext r; exact (zeroEquiv (r.val.val : ℂ) (by simp [r.property])).map_mul _ _
        · funext r
          exact (constantEquiv (r.val.val : ℂ) (Complex.ofReal_ne_zero.mpr r.property)).map_mul _ _ }

/-- The full answer: U on zero fibers, O on positive absolute-value fibers. -/
def classification (c : I → ℂ) : subgroup c ≃* Coordinates c :=
  (localClassification c).trans (splitEquiv c)

def residualHomEquiv {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) V) (b : Representation ℂ (subgroup c) W) :
    Representation.IntertwiningMap
      (a.comp (classification c).symm.toMonoidHom)
      (b.comp (classification c).symm.toMonoidHom) ≃ₗ[ℂ]
        Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv (classification c).symm.toMonoidHom
    (classification c).symm.surjective a b

theorem residual_nonzero_iff {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) V) (b : Representation ℂ (subgroup c) W) :
    (∃ f : Representation.IntertwiningMap
      (a.comp (classification c).symm.toMonoidHom)
      (b.comp (classification c).symm.toMonoidHom), f ≠ 0) ↔
        ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff (classification c).symm.toMonoidHom
    (classification c).symm.surjective a b

/-- Opposite coefficient phases do not split an equal-absolute-value block. -/
theorem opposite_phase_mixing :
    ∃ U : subgroup (![1, -1] : Fin 2 → ℂ), U.val 0 1 ≠ 0 := by
  let U : unitaryGroup (Fin 2) ℂ := ⟨!![0, Complex.I; Complex.I, 0], by
    rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]⟩
  have hU : Preserves (![1, -1] : Fin 2 → ℂ) U.val := by
    rw [entry_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [U]
  exact ⟨⟨U, hU⟩, by simp [U]⟩

end
end Math.MajoranaUnitaryClassification

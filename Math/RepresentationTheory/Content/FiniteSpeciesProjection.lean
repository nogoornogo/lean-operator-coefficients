import Math.RepresentationTheory.Exterior.FiniteSpeciesExterior

/-! Species-support projectors on independently specified exterior coefficients.
The predicate is permutation-stable; it is not a contraction ansatz. -/
namespace Math.FiniteSpeciesProjection
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s))
  (P : (Fin 4 → S) → Prop) [DecidablePred P]

def cutMultilinear (f : Coefficient r 4) :
    MultilinearMap ℂ (fun _ : Fin 4 => ∀ s, V s) ℂ :=
  ∑ labels : Fin 4 → S, if P labels then
    (restrict r f labels).compLinearMap (fun i => LinearMap.proj (labels i)) else 0

theorem cutMultilinear_pure (f : Coefficient r 4) (labels : Fin 4 → S)
    (v : ∀ i, V (labels i)) :
    cutMultilinear r P f (fun i => Pi.single (labels i) (v i)) =
      if P labels then restrict r f labels v else 0 := by
  classical
  rw [cutMultilinear, sum_apply, Finset.sum_eq_single labels]
  · by_cases h : P labels <;> simp [h, MultilinearMap.compLinearMap_apply]
  · intro t _ ht
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ labels i := by
      by_contra hn
      exact ht (funext (fun i => by simpa using not_exists.mp hn i))
    by_cases hp : P t
    · simp only [hp, ite_true, MultilinearMap.compLinearMap_apply, LinearMap.proj_apply]
      apply MultilinearMap.map_coord_zero _ i
      exact Pi.single_eq_of_ne hi _
    · simp [hp]
  · simp

def cutAlternating (f : Coefficient r 4) : (∀ s, V s) [⋀^Fin 4]→ₗ[ℂ] ℂ :=
  (1 / 24 : ℂ) • (cutMultilinear r P f).alternatization

variable (hp : ∀ labels (p : Equiv.Perm (Fin 4)), P (labels ∘ p) ↔ P labels)

include hp in
theorem cutAlternating_pure (f : Coefficient r 4) (labels : Fin 4 → S)
    (v : ∀ i, V (labels i)) :
    cutAlternating r P f (fun i => Pi.single (labels i) (v i)) =
      if P labels then restrict r f labels v else 0 := by
  classical
  simp only [cutAlternating, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  have ht (p : Equiv.Perm (Fin 4)) :
      Equiv.Perm.sign p • cutMultilinear r P f
        (fun i => Pi.single (labels (p i)) (v (p i))) =
        if P labels then restrict r f labels v else 0 := by
    have hh := cutMultilinear_pure r P f (labels ∘ p) (fun i => v (p i))
    simp only [Function.comp_apply] at hh
    rw [hh]
    by_cases h : P labels
    · rw [ite_eq_left ((hp labels p).mpr h), ite_eq_left h]
      exact restrict_perm r f labels v p
    · rw [ite_eq_right (by simpa [hp labels p] using h), ite_eq_right h, smul_zero]
  simp_rw [ht]
  norm_num [Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  split_ifs <;> ring

def project (f : Coefficient r 4) : Coefficient r 4 where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (cutAlternating r P f)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    have expand (w : Fin 4 → ∀ s, V s) : cutAlternating r P f w =
        ∑ labels : Fin 4 → S,
          if P labels then restrict r f labels (fun i => w i (labels i)) else 0 := by
      calc
        _ = cutAlternating r P f (fun i => ∑ s, Pi.single s (w i s)) := by
          simp only [LinearMap.sum_single_apply]
        _ = _ := by
          exact ((cutAlternating r P f).toMultilinearMap.map_sum
            (fun i s => Pi.single s (w i s))).trans
              (Finset.sum_congr rfl (fun labels _ => cutAlternating_pure r P hp f labels _))
    rw [expand, expand]
    apply Finset.sum_congr rfl
    intro labels _
    split_ifs
    · exact restrict_invariant r f labels g _
    · rfl

theorem restrict_project (f : Coefficient r 4) (labels : Fin 4 → S) :
    restrict r (project r P hp f) labels = if P labels then restrict r f labels else 0 := by
  ext v
  rw [restrict_apply]
  change exteriorPower.alternatingMapLinearEquiv (cutAlternating r P f)
    (exteriorPower.ιMulti ℂ 4 (fun i => Pi.single (labels i) (v i))) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, cutAlternating_pure r P hp]
  split_ifs <;> rfl

def supportSpace : Submodule ℂ (Coefficient r 4) where
  carrier := {f | ∀ labels, ¬ P labels → restrict r f labels = 0}
  zero_mem' := by intro labels _; rfl
  add_mem' := by
    intro f g hf hg labels hn
    ext v
    change restrict r f labels v + restrict r g labels v = 0
    rw [hf labels hn, hg labels hn]; simp
  smul_mem' := by
    intro z f hf labels hn
    ext v
    change z • restrict r f labels v = 0
    rw [hf labels hn]; simp

def projectLinear : Coefficient r 4 →ₗ[ℂ] Coefficient r 4 where
  toFun := project r P hp
  map_add' f g := by
    apply pure_ext r
    intro labels
    rw [restrict_add, restrict_project, restrict_project, restrict_project]
    split_ifs
    · rfl
    · simp
  map_smul' z f := by
    apply pure_ext r
    intro labels
    rw [restrict_smul, restrict_project, restrict_project]
    split_ifs
    · exact restrict_smul r z f labels
    · simp

theorem project_mem (f : Coefficient r 4) : project r P hp f ∈ supportSpace r P := by
  intro labels hn
  rw [restrict_project, ite_eq_right hn]

theorem project_eq_self (f : supportSpace r P) : project r P hp f.val = f.val := by
  apply pure_ext r
  intro labels
  rw [restrict_project]
  split_ifs with h
  · rfl
  · exact (f.property labels h).symm

/-- A single permutation orbit is determined by its canonical ordered restriction. -/
theorem pattern_ext (pattern : Fin 4 → S)
    (orbit : ∀ labels, P labels → ∃ p : Equiv.Perm (Fin 4), labels ∘ p = pattern)
    (f g : supportSpace r P) (h : restrict r f.val pattern = restrict r g.val pattern) : f = g := by
  apply Subtype.ext
  apply pure_ext r
  intro labels
  by_cases hl : P labels
  · obtain ⟨p,hp⟩ := orbit labels hl
    ext v
    let w : Fin 4 → ∀ s, V s := fun i => Pi.single (labels i) (v i)
    have hw : w ∘ p = fun i => Pi.single (pattern i) ((w (p i)) (pattern i)) := by
      funext i
      have hi := congrFun hp i
      dsimp only [Function.comp_apply] at hi
      simp only [w, Function.comp_apply]
      rw [← hi, Pi.single_eq_same]
    calc
      restrict r f.val labels v = Equiv.Perm.sign p • evaluation r f.val (w ∘ p) :=
        (evaluation r f.val).map_congr_perm w p
      _ = Equiv.Perm.sign p • restrict r f.val pattern (fun i => w (p i) (pattern i)) := by
        rw [hw]; rfl
      _ = Equiv.Perm.sign p • restrict r g.val pattern (fun i => w (p i) (pattern i)) := by rw [h]
      _ = Equiv.Perm.sign p • evaluation r g.val (w ∘ p) := by rw [hw]; rfl
      _ = restrict r g.val labels v := ((evaluation r g.val).map_congr_perm w p).symm
  · rw [f.property labels hl, g.property labels hl]

section Partition
variable {I : Type*} [Fintype I] [DecidableEq I]
  (ps : I → (Fin 4 → S) → Prop) [∀ i, DecidablePred (ps i)]
  (stable : ∀ i labels (p : Equiv.Perm (Fin 4)), ps i (labels ∘ p) ↔ ps i labels)
  (disjoint : ∀ i j, i ≠ j → ∀ labels, ps i labels → ¬ ps j labels)

def partitionSpace : Submodule ℂ (Coefficient r 4) := supportSpace r (fun labels => ∃ i, ps i labels)

def split (f : partitionSpace r ps) : ∀ i, supportSpace r (ps i) :=
  fun i => ⟨project r (ps i) (stable i) f.val, project_mem r (ps i) (stable i) f.val⟩

def join (f : ∀ i, supportSpace r (ps i)) : partitionSpace r ps :=
  ⟨∑ i, (f i).val, by
    intro labels hn
    ext v
    change (∑ i, (f i).val) (exteriorPower.ιMulti ℂ 4
      (fun i => Pi.single (labels i) (v i))) = 0
    simp only [IntertwiningMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact DFunLike.congr_fun ((f i).property labels (fun hi => hn ⟨i, hi⟩)) v⟩

omit [DecidableEq I] in
include disjoint in
theorem split_join (f : ∀ i, supportSpace r (ps i)) : split r ps stable (join r ps f) = f := by
  funext i
  apply Subtype.ext
  apply pure_ext r
  intro labels
  rw [show (split r ps stable (join r ps f) i).val =
      project r (ps i) (stable i) (∑ j, (f j).val) from rfl, restrict_project]
  by_cases hi : ps i labels
  · rw [ite_eq_left hi]
    ext v
    change (∑ j, (f j).val) (exteriorPower.ιMulti ℂ 4
      (fun i => Pi.single (labels i) (v i))) = _
    rw [IntertwiningMap.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro j _ hji
      exact DFunLike.congr_fun ((f j).property labels
        (disjoint i j (Ne.symm hji) labels hi)) v
    · simp
  · rw [ite_eq_right hi, (f i).property labels hi]

omit [DecidableEq I] in
include disjoint in
theorem join_split (f : partitionSpace r ps) : join r ps (split r ps stable f) = f := by
  apply Subtype.ext
  apply pure_ext r
  intro labels
  ext v
  change (∑ i, project r (ps i) (stable i) f.val)
    (exteriorPower.ιMulti ℂ 4 (fun i => Pi.single (labels i) (v i))) = _
  rw [IntertwiningMap.sum_apply]
  change (∑ i, restrict r (project r (ps i) (stable i) f.val) labels v) = _
  simp_rw [restrict_project]
  by_cases hh : ∃ i, ps i labels
  · obtain ⟨i, hi⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi]
    · intro j _ hji
      rw [ite_eq_right (disjoint i j (Ne.symm hji) labels hi)]; rfl
    · simp
  · have hz := f.property labels hh
    rw [hz]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hi => hh ⟨i,hi⟩)]; rfl

def partitionEquiv : partitionSpace r ps ≃ₗ[ℂ] (∀ i, supportSpace r (ps i)) where
  toFun := split r ps stable
  invFun := join r ps
  left_inv := join_split r ps stable disjoint
  right_inv := split_join r ps stable disjoint
  map_add' f g := by
    funext i
    apply Subtype.ext
    exact (projectLinear r (ps i) (stable i)).map_add f.val g.val
  map_smul' z f := by
    funext i
    apply Subtype.ext
    exact (projectLinear r (ps i) (stable i)).map_smul z f.val

end Partition
/-- Nonzero vectors in a product decomposition occur in one component.
The proof is kept abstract so concrete coefficient spaces need not unfold. -/
theorem nonzero_iff_pi {A J : Type*} [AddCommGroup A] [Module ℂ A]
    {B : J → Type*} [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
    (e : A ≃ₗ[ℂ] (∀ j, B j)) :
    (∃ a : A, a ≠ 0) ↔ ∃ j, ∃ b : B j, b ≠ 0 := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    have hn : e a ≠ 0 := by
      intro hz
      exact ha (e.injective (hz.trans e.map_zero.symm))
    by_contra hh
    apply hn
    funext j
    by_contra hj
    exact hh ⟨j, e a j, hj⟩
  · rintro ⟨j, b, hb⟩
    let v : ∀ i, B i := Pi.single j b
    refine ⟨e.symm v, ?_⟩
    intro hz
    have hv : v = 0 := by simpa using congrArg e hz
    have hi := congrFun hv j
    exact hb (by simpa [v] using hi)

end
end Math.FiniteSpeciesProjection

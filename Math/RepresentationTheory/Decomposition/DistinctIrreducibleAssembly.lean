import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Subrepresentation

/-! Nonzero maps from distinct finite-dimensional irreducibles have independent images. -/
namespace Math.DistinctIrreducibleAssembly
set_option autoImplicit false
noncomputable section
open Representation
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, FiniteDimensional ℂ (A i)]
  {B : Type*} [AddCommGroup B] [Module ℂ B]
  (a : ∀ i, Representation ℂ G (A i)) (b : Representation ℂ G B)
  [∀ i, IsIrreducible (a i)]

def assemble (f : ∀ i, IntertwiningMap (a i) b) : IntertwiningMap (FiniteBlockHom.action a) b where
  toLinearMap := ∑ i, (f i).toLinearMap.comp (LinearMap.proj i)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.proj_apply,FiniteBlockHom.action_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => (f i).isIntertwining _ _ g (x i))

omit [DecidableEq I] [∀ i, FiniteDimensional ℂ (A i)] [∀ i, IsIrreducible (a i)] in
@[simp] theorem assemble_apply (f : ∀ i, IntertwiningMap (a i) b) (x : ∀ i, A i) :
    assemble a b f x = ∑ i, f i (x i) := by
  simp [assemble]

omit [∀ i, FiniteDimensional ℂ (A i)] [∀ i, IsIrreducible (a i)] in
@[simp] theorem assemble_single (f : ∀ i, IntertwiningMap (a i) b) (i : I) (x : A i) :
    assemble a b f (Pi.single i x) = f i x := by
  rw [assemble_apply]
  calc
    _ = f i ((Pi.single i x) i) := Finset.sum_eq_single i
      (by intro j hj hji; rw [Pi.single_eq_of_ne hji,map_zero])
      (by intro hh; exact (hh (Finset.mem_univ i)).elim)
    _ = _ := by rw [Pi.single_eq_same]

theorem injective_of_inequivalent (f : ∀ i, IntertwiningMap (a i) b)
    (hf : ∀ i, f i ≠ 0)
    (hd : ∀ i j, i ≠ j → ¬ Nonempty (Representation.Equiv (a i) (a j))) :
    Function.Injective (assemble a b f) := by
  let F := assemble a b f
  have hk : F.ker = ⊥ := by
    by_contra hn
    obtain ⟨K,hK,hAtom⟩ := Representation.exists_isAtom_le hn
    let : IsIrreducible K.toRepresentation := Representation.isIrreducible_toRepresentation_of_isAtom hAtom
    let c := fun i => (FiniteBlockHom.project a i).comp K.subtype
    have hc : ∃ i, c i ≠ 0 := by
      by_contra hh
      have he : K.subtype = 0 := by
        ext x i
        have hi : c i = 0 := by simpa using not_exists.mp hh i
        exact DFunLike.congr_fun hi x
      have hbot : K = ⊥ := by
        simpa only [Subrepresentation.range_subtype] using
          (IntertwiningMap.eq_zero_iff_range_eq_bot K.subtype).mp he
      exact hAtom.ne_bot hbot
    obtain ⟨i,hi⟩ := hc
    have hbij := (IsIrreducible.bijective_or_eq_zero (c i)).resolve_right hi
    let e := (c i).ofBijective hbij
    have hz (j : I) (hji : j ≠ i) : c j = 0 := by
      let d := (c j).comp e.symm.toIntertwiningMap
      have hz : d=0 := by
        by_contra hn
        exact hd i j (Ne.symm hji)
          ⟨d.ofBijective ((IsIrreducible.bijective_or_eq_zero d).resolve_right hn)⟩
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun hz (e x)
      simpa [d] using hx
    have hnontrivial : Nontrivial K.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.mpr
        (by intro he; exact hAtom.ne_bot (Subrepresentation.toSubmodule_injective he))
    let : Nontrivial K.toSubmodule := hnontrivial
    obtain ⟨x,hx⟩ := exists_ne (0 : K.toSubmodule)
    have he : (x.val : ∀ j, A j) = Pi.single i (c i x) := by
      funext j
      by_cases hji : j=i
      · subst j; simp only [Pi.single_eq_same]; rfl
      · have hj := DFunLike.congr_fun (hz j hji) x
        rw [Pi.single_eq_of_ne hji]; exact hj
    have hzero : F x.val = 0 := hK x.property
    rw [he,assemble_single] at hzero
    have hfi := (IsIrreducible.injective_or_eq_zero (f i)).resolve_right (hf i)
    have hc0 : c i x = 0 := hfi (by simpa using hzero)
    exact hx (hbij.1 (by simpa using hc0))
  exact (LinearMap.ker_eq_bot).mp
    (by simpa only [IntertwiningMap.ker_toSubmodule,Subrepresentation.toSubmodule_bot] using
      congrArg Subrepresentation.toSubmodule hk)

/-- Dimension inequality is a sufficient special case. Joint factors of the
same dimension can instead use `injective_of_inequivalent`. -/
theorem injective (f : ∀ i, IntertwiningMap (a i) b)
    (hf : ∀ i, f i ≠ 0)
    (hd : ∀ i j, i ≠ j → Module.finrank ℂ (A i) ≠ Module.finrank ℂ (A j)) :
    Function.Injective (assemble a b f) :=
  injective_of_inequivalent a b f hf (by
    rintro i j hij ⟨e⟩
    exact hd i j hij e.finrank_eq)

end
end Math.DistinctIrreducibleAssembly

import Math.RepresentationTheory.Decomposition.ExternalCopyFactorization
import Math.RepresentationTheory.Characters.CompactCoefficientSupport

/-! Equivalence of external irreducibles is exactly equivalence in each
factor. No compactness, character comparison or multiplicity evaluation is
needed; slices of a nonzero map supply the first-factor witness. -/
namespace Math.ExternalIrreducibleMatch
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

variable {G H V W A B : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  (r : Representation ℂ G V) (s : Representation ℂ G W)
  (a : Representation ℂ H A) (b : Representation ℂ H B)

def slice (M : IntertwiningMap (external r a) (external s b)) (x : A)
    (j : Fin (Module.finrank ℂ B)) : IntertwiningMap r s where
  toLinearMap := ((LinearMap.proj j).comp
    (ExternalCopyFactorization.coordinates (V := W) (Module.finBasis ℂ B)).toLinearMap).comp
      (M.toLinearMap.comp ((TensorProduct.mk ℂ V A).flip x))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let c := ExternalCopyFactorization.coordinates (V := W) (Module.finBasis ℂ B)
    have hm : M (r g v ⊗ₜ[ℂ] x) = external s b (g,1) (M (v ⊗ₜ[ℂ] x)) := by
      simpa [external, Representation.tprod_apply] using
        M.isIntertwining _ _ (g,1) (v ⊗ₜ[ℂ] x)
    change c (M (r g v ⊗ₜ[ℂ] x)) j = s g (c (M (v ⊗ₜ[ℂ] x)) j)
    rw [hm]
    have hc (t : W ⊗[ℂ] B) : c (external s b (g,1) t) j = s g (c t j) := by
      induction t using TensorProduct.inductionOn with
      | tmul w y => simp [c, external, Representation.tprod_apply,
          ExternalCopyFactorization.coordinates_tmul]
      | add t u ht hu => simp only [map_add, Pi.add_apply, ht, hu]
    exact hc _

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem exists_nonzero_slice (M : IntertwiningMap (external r a) (external s b)) (hM : M ≠ 0) :
    ∃ x j, slice r s a b M x j ≠ 0 := by
  by_contra h
  apply hM
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v x
  apply (ExternalCopyFactorization.coordinates (V := W) (Module.finBasis ℂ B)).injective
  funext j
  have hz : slice r s a b M x j = 0 := by simpa using not_exists.mp (not_exists.mp h x) j
  simpa [slice] using DFunLike.congr_fun hz v

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem first_equiv_of_nonzero [IsIrreducible r] [IsIrreducible s]
    (M : IntertwiningMap (external r a) (external s b)) (hM : M ≠ 0) :
    Nonempty (Representation.Equiv r s) := by
  obtain ⟨x,j,hj⟩ := exists_nonzero_slice r s a b M hM
  exact ⟨(slice r s a b M x j).ofBijective
    ((IsIrreducible.bijective_or_eq_zero _).resolve_right hj)⟩

omit [FiniteDimensional ℂ W] in
/-- Multiplicity representations need not be irreducible. First-factor
matching and the actual multiplicity Hom are both necessary and sufficient. -/
theorem hom_allowed_iff [IsIrreducible r] [IsIrreducible s] :
    SelectionCriteria.Allowed (IntertwiningMap (external r a) (external s b)) ↔
      Nonempty (Representation.Equiv r s) ∧ SelectionCriteria.Allowed (IntertwiningMap a b) := by
  constructor
  · rintro ⟨M,hM⟩
    obtain ⟨e⟩ := first_equiv_of_nonzero r s a b M hM
    let t := externalEquiv e.symm (Representation.Equiv.refl b)
    let M' := t.toIntertwiningMap.comp M
    have hn : M' ≠ 0 := by
      intro hz
      apply hM
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply t.injective
      simpa [M'] using DFunLike.congr_fun hz x
    obtain ⟨m,hm⟩ := ExternalCopyFactorization.exists_copy_map r a b M'
    refine ⟨⟨e⟩,m,?_⟩
    intro hz
    apply hn
    apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro v x
    change M' (v ⊗ₜ[ℂ] x) = 0
    rw [hm,hz]
    simp
  · rintro ⟨⟨e⟩,m,hm⟩
    let f : IntertwiningMap (external r a) (external s b) :=
      { toLinearMap := TensorProduct.map e.toLinearMap m.toLinearMap
        isIntertwining' g := by
          apply TensorProduct.ext'
          intro v x
          change e (r g.1 v) ⊗ₜ[ℂ] m (a g.2 x) = s g.1 (e v) ⊗ₜ[ℂ] b g.2 (m x)
          exact congrArg₂ (fun v x => v ⊗ₜ[ℂ] x)
            (e.toIntertwiningMap.isIntertwining _ _ g.1 v) (m.isIntertwining _ _ g.2 x) }
    refine ⟨f,?_⟩
    intro hz
    apply hm
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    let : Nontrivial V := IsIrreducible.nontrivial (ρ := r) inferInstance
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    have hev : e v ≠ 0 := fun h => hv (e.injective (by simpa using h))
    obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hev
    have he := congrArg (fun z => (TensorProduct.lid ℂ B)
      (TensorProduct.map phi (LinearMap.id : B →ₗ[ℂ] B) z)) (DFunLike.congr_fun hz (v ⊗ₜ[ℂ] x))
    simpa [f,hphi] using he

omit [FiniteDimensional ℂ W] in
theorem equiv_iff [IsIrreducible r] [IsIrreducible s]
    [IsIrreducible a] [IsIrreducible b] :
    Nonempty (Representation.Equiv (external r a) (external s b)) ↔
      Nonempty (Representation.Equiv r s) ∧ Nonempty (Representation.Equiv a b) := by
  constructor
  · rintro ⟨e⟩
    let : Nontrivial V := IsIrreducible.nontrivial (ρ := r) inferInstance
    let : Nontrivial A := IsIrreducible.nontrivial (ρ := a) inferInstance
    have he : e.toIntertwiningMap ≠ 0 := by
      intro hz
      obtain ⟨v,hv⟩ := exists_ne (0 : V)
      obtain ⟨x,hx⟩ := exists_ne (0 : A)
      obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
      have ht : v ⊗ₜ[ℂ] x ≠ 0 := by
        intro hh
        have htest := congrArg (fun z => (TensorProduct.rid ℂ V)
          (TensorProduct.map (LinearMap.id : V →ₗ[ℂ] V) phi z)) hh
        exact hv (by simpa [hphi] using htest)
      apply ht
      apply e.injective
      simpa using DFunLike.congr_fun hz (v ⊗ₜ[ℂ] x)
    obtain ⟨f⟩ := first_equiv_of_nonzero r s a b e.toIntertwiningMap he
    let t := externalEquiv f.symm (Representation.Equiv.refl b)
    let M := t.toIntertwiningMap.comp e.toIntertwiningMap
    have hM : M ≠ 0 := by
      intro hz
      apply he
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply t.injective
      simpa [M] using DFunLike.congr_fun hz x
    obtain ⟨m,hm⟩ := ExternalCopyFactorization.exists_copy_map r a b M
    have hn : m ≠ 0 := by
      intro hz
      apply hM
      apply IntertwiningMap.ext
      apply TensorProduct.ext'
      intro v x
      change M (v ⊗ₜ[ℂ] x) = 0
      rw [hm, hz]
      simp
    exact ⟨⟨f⟩, ⟨m.ofBijective ((IsIrreducible.bijective_or_eq_zero m).resolve_right hn)⟩⟩
  · rintro ⟨⟨e⟩,⟨f⟩⟩
    exact ⟨externalEquiv e f⟩

end
end Math.ExternalIrreducibleMatch

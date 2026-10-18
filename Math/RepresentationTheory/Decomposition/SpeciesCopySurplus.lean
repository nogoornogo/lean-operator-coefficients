import Math.RepresentationTheory.Decomposition.SemisimpleSplitting
import Math.RepresentationTheory.Characters.CharacterExact
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-! Species-dependent Hom surpluses force a selected irreducible into actual
mass kernels. No topology or target semisimplicity is used. -/
namespace Math.SpeciesCopySurplus
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped MonoidAlgebra
variable {H R A C : Type*} [Group H]
  [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]
  [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  (r : Representation ℂ H R) (a : Representation ℂ H A) (c : Representation ℂ H C)

def Surplus : Prop :=
  Module.finrank ℂ (IntertwiningMap r c) < Module.finrank ℂ (IntertwiningMap r a)

/-- Postcomposition by the actual mass map. -/
def postcompose (M : IntertwiningMap a c) :
    IntertwiningMap r a →ₗ[ℂ] IntertwiningMap r c := IntertwiningMap.llcomp r a c M

def intoKernel (M : IntertwiningMap a c) (f : IntertwiningMap r a)
    (hf : M.comp f = 0) : IntertwiningMap r M.ker.toRepresentation where
  toLinearMap := {
    toFun := fun x => ⟨f x, by
      have hx := DFunLike.congr_fun hf x
      exact hx⟩
    map_add' := by intro x y; apply Subtype.ext; exact map_add f x y
    map_smul' := by intro z x; apply Subtype.ext; exact map_smul f z x }
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact f.isIntertwining _ _ h x

/-- Exact identification of postcomposition's kernel with maps into the
actual mass kernel. This is an equivalence of complex vector spaces. -/
def homKernelEquiv (M : IntertwiningMap a c) :
    IntertwiningMap r M.ker.toRepresentation ≃ₗ[ℂ]
      (postcompose r a c M).ker where
  toFun f := ⟨(CharacterExact.subtypeIntertwiner M.ker).comp f, by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (f x).property⟩
  invFun f := intoKernel r a c M f.val f.property
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' z f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

omit [FiniteDimensional ℂ A] in
/-- Rank-nullity in Hom form; no irreducibility is needed for nonzero survival. -/
theorem exists_nonzero_kernel_map (M : IntertwiningMap a c) (hd : Surplus r a c) :
    ∃ f : IntertwiningMap r M.ker.toRepresentation, f ≠ 0 := by
  classical
  have hn : ¬ Function.Injective (postcompose r a c M) := by
    intro hi
    exact (not_le_of_gt hd) (LinearMap.finrank_le_finrank_of_injective hi)
  obtain ⟨f,g,he,hne⟩ := Function.not_injective_iff.mp hn
  have hz : M.comp (f-g) = 0 := by
    change postcompose r a c M (f-g) = 0
    rw [map_sub, he, sub_self]
  refine ⟨intoKernel r a c M (f-g) hz, ?_⟩
  intro hzero
  apply (sub_ne_zero.mpr hne)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (DFunLike.congr_fun hzero x)

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ C] in
theorem kernel_semisimple (M : IntertwiningMap a c)
    (ha : IsSemisimpleRepresentation a) : IsSemisimpleRepresentation M.ker.toRepresentation := by
  let : IsSemisimpleModule ℂ[H] a.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule a).mp ha
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule M.ker.toRepresentation a
      (CharacterExact.subtypeIntertwiner M.ker)) Subtype.val_injective

omit [FiniteDimensional ℂ A] in
/-- The selected irreducible splits in the actual kernel for every mass. -/
theorem exists_kernel_split [IsIrreducible r] (M : IntertwiningMap a c)
    (ha : IsSemisimpleRepresentation a) (hd : Surplus r a c) :
    Nonempty (Split M.ker.toRepresentation r) := by
  obtain ⟨f,hf⟩ := exists_nonzero_kernel_map r a c M hd
  have hi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨p,hp⟩ := SemisimpleSplitting.exists_retraction _ _
    (kernel_semisimple a c M ha) f hi
  exact ⟨p⟩

/-- Independent sources/targets can be indexed by any family; the same selected
irreducible survives all maps if each has the required Hom surplus. -/
theorem family_kernel_splits [IsIrreducible r]
    {I : Type*} {As Cs : I → Type*}
    [∀ i, AddCommGroup (As i)] [∀ i, Module ℂ (As i)]
    [∀ i, AddCommGroup (Cs i)] [∀ i, Module ℂ (Cs i)]
    [∀ i, FiniteDimensional ℂ (Cs i)]
    (sources : ∀ i, Representation ℂ H (As i))
    (targets : ∀ i, Representation ℂ H (Cs i))
    (maps : ∀ i, IntertwiningMap (sources i) (targets i))
    (hs : ∀ i, IsSemisimpleRepresentation (sources i))
    (hd : ∀ i, Surplus r (sources i) (targets i)) :
    ∀ i, Nonempty (Split (maps i).ker.toRepresentation r) :=
  fun i => exists_kernel_split r (sources i) (targets i) (maps i) (hs i) (hd i)

end
end Math.SpeciesCopySurplus

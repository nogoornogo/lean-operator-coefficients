import Math.RepresentationTheory.TwoSpeciesPattern
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Typed two-species permutation relations as independent symmetric blocks. -/
namespace Math.TwoSpeciesSymmetricDescent
set_option autoImplicit false
noncomputable section
open TwoSpeciesPattern
open scoped TensorProduct
variable {V : Fin 2 → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {N : Type*} [AddCommGroup N] [Module ℂ N]

abbrev Raw (h d : ℕ) := MultilinearMap ℂ (fun i => V (pattern h d i)) N
abbrev Blocks (h d : ℕ) := MultilinearMap ℂ (fun _ : Fin h => V 0)
  (MultilinearMap ℂ (fun _ : Fin d => V 1) N)

def slotCast {u v : Fin 2} (he : u=v) : V u ≃ₗ[ℂ] V v := by
  subst v
  exact .refl ℂ _

@[simp] theorem slotCast_apply {u v : Fin 2} (he : u=v) (w : ∀ s, V s) :
    slotCast he (w u) = w v := by
  subst v
  rfl

def tag (h d : ℕ) : Fin h ⊕ Fin d → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

theorem pattern_sum (h d : ℕ) (s : Fin h ⊕ Fin d) :
    pattern h d (finSumFinEquiv s) = tag h d s := by
  simp [pattern,tag]

def reindex (h d : ℕ) : Raw (V := V) (N := N) h d ≃ₗ[ℂ]
    MultilinearMap ℂ (fun s : Fin h ⊕ Fin d => V (tag h d s)) N :=
  (MultilinearMap.domDomCongrLinearEquiv' (R := ℂ) (S := ℂ)
    (M₁ := fun i => V (pattern h d i)) (M₂ := N)
    (finSumFinEquiv : Fin h ⊕ Fin d ≃ Fin (h+d)).symm).trans
      (LinearEquiv.multilinearMapCongrLeft (fun s => slotCast (pattern_sum h d s).symm))

def rawEquiv (h d : ℕ) : Raw (V := V) (N := N) h d ≃ₗ[ℂ] Blocks (V := V) (N := N) h d :=
  (reindex h d).trans (MultilinearMap.currySumEquiv (R := ℂ)
    (N := fun s : Fin h ⊕ Fin d => V (tag h d s)) (M₂ := N))

theorem ordered_apply (h d : ℕ) (k : Raw (V := V) (N := N) h d)
    (w : Fin (h+d) → ∀ s, V s) :
    rawEquiv h d k (fun i => w (left i) 0) (fun j => w (right j) 1) =
      TypedPatternSymmetrization.ordered (pattern h d) k w := by
  simp only [rawEquiv,reindex,tag,MultilinearMap.compLinearMap_apply,
    TypedPatternSymmetrization.ordered,TypedPatternAlternation.ordered]
  apply congrArg k
  funext i
  obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
  calc
    _ = slotCast (pattern_sum h d s).symm
        (Sum.rec (fun i => w (left i) 0) (fun j => w (right j) 1) s) := by
      exact Equiv.piCongrLeft'_symm_apply_apply (fun i => V (pattern h d i))
        (finSumFinEquiv : Fin h ⊕ Fin d ≃ Fin (h+d)).symm
        (fun s => slotCast (pattern_sum h d s).symm
          (Sum.rec (fun i => w (left i) 0) (fun j => w (right j) 1) s)) s
    _ = _ := by cases s <;> exact slotCast_apply (V := V) _ _

def pack {h d : ℕ} (v : Fin h → V 0) (w : Fin d → V 1) : Fin (h+d) → ∀ s, V s :=
  SymmetricPowerOperations.concat (fun i => Pi.single 0 (v i)) (fun j => Pi.single 1 (w j))

omit [∀ s, Module ℂ (V s)] in
@[simp] theorem pack_left {h d : ℕ} (v : Fin h → V 0) (w : Fin d → V 1) (i : Fin h) :
    pack v w (left i) 0 = v i := by simp [pack,SymmetricPowerOperations.concat,left]
omit [∀ s, Module ℂ (V s)] in
@[simp] theorem pack_right {h d : ℕ} (v : Fin h → V 0) (w : Fin d → V 1) (j : Fin d) :
    pack v w (right j) 1 = w j := by simp [pack,SymmetricPowerOperations.concat,right]

def symmetricBlocks (h d : ℕ) : Submodule ℂ (Blocks (V := V) (N := N) h d) where
  carrier := {k | (∀ (p : Equiv.Perm (Fin h)) v w, k (v ∘ p) w = k v w) ∧
    (∀ (q : Equiv.Perm (Fin d)) v w, k v (w ∘ q) = k v w)}
  zero_mem' := ⟨by intro p v w; rfl,by intro q v w; rfl⟩
  add_mem' := by
    intro f k hf hk
    constructor
    · intro p v w
      change f (v ∘ p) w + k (v ∘ p) w = f v w + k v w
      rw [hf.1,hk.1]
    · intro q v w
      change f v (w ∘ q) + k v (w ∘ q) = f v w + k v w
      rw [hf.2,hk.2]
  smul_mem' := by
    intro z k hk
    constructor
    · intro p v w
      change z • k (v ∘ p) w = z • k v w
      rw [hk.1]
    · intro q v w
      change z • k v (w ∘ q) = z • k v w
      rw [hk.2]

theorem compatible_iff (h d : ℕ) (k : Raw (V := V) (N := N) h d) :
    TypedPatternSymmetrization.Compatible (pattern h d) k ↔ rawEquiv h d k ∈ symmetricBlocks h d := by
  constructor
  · intro hk
    constructor
    · intro p v w
      have he := hk (SymmetricPowerOperations.blockPerm p (Equiv.refl (Fin d)))
        (block_preserves p (Equiv.refl (Fin d))) (pack v w)
      rw [← ordered_apply,← ordered_apply] at he
      simpa [pack,SymmetricPowerOperations.concat,left,right,
        SymmetricPowerOperations.blockPerm,Function.comp_def] using he
    · intro q v w
      have he := hk (SymmetricPowerOperations.blockPerm (Equiv.refl (Fin h)) q)
        (block_preserves (Equiv.refl (Fin h)) q) (pack v w)
      rw [← ordered_apply,← ordered_apply] at he
      simpa [pack,SymmetricPowerOperations.concat,left,right,
        SymmetricPowerOperations.blockPerm,Function.comp_def] using he
  · intro hk p hp w
    rw [← ordered_apply,← ordered_apply]
    simp_rw [Function.comp_apply,perm_left p hp,perm_right p hp]
    exact (hk.2 (rightPerm p hp) ((fun i => w (left i) 0) ∘ leftPerm p hp)
      (fun j => w (right j) 1)).trans
        (hk.1 (leftPerm p hp) (fun i => w (left i) 0) (fun j => w (right j) 1))

abbrev Nested (h d : ℕ) := SymmetricPowerDescent.symmetricMaps (A := V 0)
  (N := SymmetricPowerDescent.symmetricMaps (A := V 1) (N := N) d) h

def nestedRaw {h d : ℕ} (k : Nested (V := V) (N := N) h d) : Blocks (V := V) (N := N) h d :=
  (SymmetricPowerDescent.symmetricMaps (A := V 1) (N := N) d).subtype.compMultilinearMap k.val

def nestedEquiv (h d : ℕ) : Nested (V := V) (N := N) h d ≃ₗ[ℂ] symmetricBlocks (V := V) (N := N) h d where
  toFun k := ⟨nestedRaw k,⟨by intro p v w; exact congrArg (fun z => z.val w) (k.property p v),
    by intro q v w; exact (k.val v).property q w⟩⟩
  invFun k := ⟨k.val.codRestrict _ (by intro v q w; exact k.property.2 q v w),by
    intro p v
    apply Subtype.ext
    ext w
    exact k.property.1 p v w⟩
  left_inv k := by apply Subtype.ext; ext v w; rfl
  right_inv k := by apply Subtype.ext; ext v w; rfl
  map_add' f k := by apply Subtype.ext; ext v w; rfl
  map_smul' z k := by apply Subtype.ext; ext v w; rfl

def tensorNested (h d : ℕ) : (Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N) ≃ₗ[ℂ]
    Nested (V := V) (N := N) h d :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (Sym[ℂ]^h (V 0)) (Sym[ℂ]^d (V 1)) N).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (Sym[ℂ]^h (V 0)))
      (SymmetricPowerDescent.equiv (A := V 1) (N := N) d)).trans
        (SymmetricPowerDescent.equiv (A := V 0)
          (N := SymmetricPowerDescent.symmetricMaps (A := V 1) (N := N) d) h))

def blockDescent (h d : ℕ) : (Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N) ≃ₗ[ℂ]
    symmetricBlocks (V := V) (N := N) h d := (tensorNested h d).trans (nestedEquiv h d)

@[simp] theorem blockDescent_apply (h d : ℕ) (f : Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N)
    (v : Fin h → V 0) (w : Fin d → V 1) :
    (blockDescent h d f).val v w = f (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) := rfl

def compatibleSpace (h d : ℕ) : Submodule ℂ (Raw (V := V) (N := N) h d) :=
  (symmetricBlocks h d).comap (rawEquiv h d).toLinearMap

theorem mem_compatibleSpace (h d : ℕ) (k : Raw (V := V) (N := N) h d) :
    k ∈ compatibleSpace h d ↔ TypedPatternSymmetrization.Compatible (pattern h d) k :=
  (compatible_iff h d k).symm

def linearJoin (h d : ℕ) : (Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N) ≃ₗ[ℂ]
    compatibleSpace (V := V) (N := N) h d :=
  (blockDescent h d).trans (LinearEquiv.ofSubmodule' (rawEquiv h d) (symmetricBlocks h d)).symm

@[simp] theorem linearJoin_apply (h d : ℕ) (f : Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N)
    (v : Fin h → V 0) (w : Fin d → V 1) :
    rawEquiv h d (linearJoin h d f).val v w =
      f (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) := by
  change rawEquiv h d ((rawEquiv h d).symm (blockDescent h d f).val) v w = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end
end Math.TwoSpeciesSymmetricDescent

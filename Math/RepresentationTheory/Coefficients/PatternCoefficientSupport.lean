import Math.RepresentationTheory.Exterior.PatternExteriorSource
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

/-! Fixed fermion content coefficients on the original exterior carrier
are equivalent to coefficients on its actual statistical content image. -/
namespace Math.PatternCoefficientSupport
set_option autoImplicit false
noncomputable section
open Representation PatternExteriorSource
open scoped TensorProduct
variable {S G Y : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [AddCommGroup Y] [Module ℂ Y]
  (r : ∀ s, Representation ℂ G (V s)) {n : ℕ} (p : Fin n → S)
  (b : Representation ℂ G Y)

abbrev FullSpace := InvariantCoefficientTransport.Invariants ((Full r (n := n)).tprod b)
abbrev ContentSpace := InvariantCoefficientTransport.Invariants ((representation r p).tprod b)

def Supported (f : FullSpace r b (n := n)) : Prop :=
  ∀ labels : Fin n → S, (¬ ∃ e : Equiv.Perm (Fin n), labels ∘ e = p) →
    ∀ (v : ∀ i, V (labels i)) (y : Y),
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y) = 0

def space : Submodule ℂ (FullSpace r b (n := n)) where
  carrier := {f | Supported r p b f}
  zero_mem' := by intro labels h v y; rfl
  add_mem' := by
    intro f g hf hg labels h v y
    change f _ + g _ = 0
    rw [hf labels h v y, hg labels h v y, add_zero]
  smul_mem' := by intro z f hf labels h v y; change z • f _ = 0; rw [hf labels h v y, smul_zero]

def restrict (f : FullSpace r b (n := n)) : ContentSpace r p b :=
  f.comp ((inclusion r p).rTensor b)

def extend (f : ContentSpace r p b) : FullSpace r b (n := n) :=
  f.comp ((projection r p).rTensor b)

theorem restrict_extend (f : ContentSpace r p b) : restrict r p b (extend r p b f) = f := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change f (projectionLinear r p x.val ⊗ₜ[ℂ] y) = f (x ⊗ₜ[ℂ] y)
  rw [projection_inclusion]

theorem extend_supported (f : ContentSpace r p b) : Supported r p b (extend r p b f) := by
  intro labels h v y
  change f (projectionLinear r p (exteriorPower.ιMulti ℂ n
    (fun i => Pi.single (labels i) (v i))) ⊗ₜ[ℂ] y) = 0
  rw [projection_vanish r p labels v h, TensorProduct.zero_tmul, map_zero]

def raw (f : FullSpace r b (n := n)) (y : Y) :
    (∀ s, V s) [⋀^Fin n]→ₗ[ℂ] ℂ :=
  (f.toLinearMap.comp ((TensorProduct.mk ℂ (⋀[ℂ]^n (∀ s, V s)) Y).flip y)).compAlternatingMap
    (exteriorPower.ιMulti ℂ n)

theorem pure_ext (f g : FullSpace r b (n := n))
    (he : ∀ (labels : Fin n → S) (v : ∀ i, V (labels i)) (y : Y),
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y) =
      g (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y)) : f=g := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply LinearMap.ext
  intro y
  change raw r b f y v = raw r b g y v
  have expand (k : FullSpace r b (n := n)) : raw r b k y v =
      ∑ labels : Fin n → S, raw r b k y (fun i => Pi.single (labels i) (v i (labels i))) := by
    calc
      _ = raw r b k y (fun i => ∑ s, Pi.single s (v i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = _ := (raw r b k y).toMultilinearMap.map_sum _
  rw [expand f,expand g]
  apply Finset.sum_congr rfl
  intro labels _
  exact he labels _ y

theorem pattern_ext (f g : FullSpace r b (n := n))
    (hf : Supported r p b f) (hg : Supported r p b g)
    (he : ∀ (v : ∀ i, V (p i)) (y : Y),
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)) ⊗ₜ[ℂ] y) =
      g (exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)) ⊗ₜ[ℂ] y)) : f=g := by
  apply pure_ext r b
  intro labels v y
  by_cases ho : ∃ e : Equiv.Perm (Fin n), labels ∘ e = p
  · obtain ⟨e,heq⟩ := ho
    let w : Fin n → ∀ s, V s := fun i => Pi.single (labels i) (v i)
    have hw : w ∘ e = fun i => Pi.single (p i) (w (e i) (p i)) := by
      funext i
      have hi := congrFun heq i
      dsimp only [Function.comp_apply] at hi
      dsimp only [w, Function.comp_apply]
      rw [← hi, Pi.single_eq_same]
    calc
      _ = Equiv.Perm.sign e • raw r b f y (w ∘ e) := (raw r b f y).map_congr_perm w e
      _ = Equiv.Perm.sign e • raw r b g y (w ∘ e) := by
        rw [hw]
        exact congrArg (Equiv.Perm.sign e • ·) (he _ y)
      _ = _ := ((raw r b g y).map_congr_perm w e).symm
  · rw [hf labels ho v y, hg labels ho v y]

theorem extend_restrict (f : space r p b) : extend r p b (restrict r p b f.val) = f.val := by
  apply pattern_ext r p b _ _ (extend_supported r p b _) f.property
  intro v y
  change f.val ((projectionLinear r p
    (exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)))).val ⊗ₜ[ℂ] y) = _
  rw [projection_pure, pure_val]

def equiv : space r p b ≃ₗ[ℂ] ContentSpace r p b where
  toFun f := restrict r p b f.val
  invFun f := ⟨extend r p b f, extend_supported r p b f⟩
  left_inv f := Subtype.ext (extend_restrict r p b f)
  right_inv := restrict_extend r p b
  map_add' _ _ := by ext x y; rfl
  map_smul' _ _ := by ext x y; rfl

end
end Math.PatternCoefficientSupport

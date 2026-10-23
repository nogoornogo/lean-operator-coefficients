import Math.RepresentationTheory.Symmetric.SymmetricSquareDescent
import TauCeti.Data.Fin.Basic

/-! Binary tensor intertwiners as equivariant two-variable multilinear maps. -/
namespace Math.TensorSquareMultilinear
noncomputable section
open Representation
open scoped TensorProduct
variable {A N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup N] [Module ℂ N]

def toMultilinear (f : (A ⊗[ℂ] A) →ₗ[ℂ] N) :
    MultilinearMap ℂ (fun _ : Fin 2 => A) N :=
  MultilinearMap.mk' (fun v => f (v 0 ⊗ₜ[ℂ] v 1))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i z x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

omit [AddCommGroup A] [Module ℂ A] in
private theorem update_zero (x y z : A) : Function.update ![x, y] 0 z = ![z, y] := by
  ext i
  fin_cases i <;> rfl

omit [AddCommGroup A] [Module ℂ A] in
private theorem update_one (x y z : A) : Function.update ![x, y] 1 z = ![x, z] := by
  ext i
  fin_cases i <;> rfl

def fromMultilinear (f : MultilinearMap ℂ (fun _ : Fin 2 => A) N) :
    (A ⊗[ℂ] A) →ₗ[ℂ] N :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun x y => f ![x, y])
    (by
      intro x x' y
      simpa only [update_zero] using f.map_update_add ![x, y] 0 x x')
    (by
      intro z x y
      simpa only [update_zero] using f.map_update_smul ![x, y] 0 z x)
    (by
      intro x y y'
      simpa only [update_one] using f.map_update_add ![x, y] 1 y y')
    (by
      intro z x y
      simpa only [update_one] using f.map_update_smul ![x, y] 1 z y))

def equiv : ((A ⊗[ℂ] A) →ₗ[ℂ] N) ≃ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin 2 => A) N where
  toFun := toMultilinear
  invFun := fromMultilinear
  left_inv f := by ext x y; rfl
  right_inv f := by
    ext v
    change f ![v 0, v 1] = f v
    congr 1
    ext i
    fin_cases i <;> rfl
  map_add' f g := by ext v; rfl
  map_smul' z f := by ext v; rfl

variable {H : Type*} [Group H]
  (a : Representation ℂ H A) (n : Representation ℂ H N)

def fromEquivariant (f : SymmetricSquareDescent.equivariantMaps a n) :
    IntertwiningMap (a.tprod a) n where
  toLinearMap := fromMultilinear f.val.val
  isIntertwining' h := by
    ext x y
    change f.val.val ![a h x, a h y] = n h (f.val.val ![x, y])
    have hf := f.property h ![x, y]
    convert hf using 1
    congr 1
    ext i
    fin_cases i <;> rfl

abbrev symmetricIntertwiners : Submodule ℂ (IntertwiningMap (a.tprod a) n) where
  carrier := {f | ∀ x y, f (y ⊗ₜ[ℂ] x) = f (x ⊗ₜ[ℂ] y)}
  zero_mem' := by intro x y; rfl
  add_mem' := by
    intro f g hf hg x y
    change f _ + g _ = f _ + g _
    rw [hf x y, hg x y]
  smul_mem' := by
    intro z f hf x y
    change z • f _ = z • f _
    rw [hf x y]

def toEquivariant (f : symmetricIntertwiners a n) :
    SymmetricSquareDescent.equivariantMaps a n :=
  ⟨⟨toMultilinear f.val.toLinearMap, by
      intro e v
      rcases TauCeti.perm_fin_two_eq_one_or_swap e with rfl | rfl
      · rfl
      · change f.val (v 1 ⊗ₜ[ℂ] v 0) = f.val (v 0 ⊗ₜ[ℂ] v 1)
        exact f.property (v 0) (v 1)⟩, by
    intro h v
    change f.val ((a.tprod a) h (v 0 ⊗ₜ[ℂ] v 1)) = n h (f.val (v 0 ⊗ₜ[ℂ] v 1))
    exact IntertwiningMap.isIntertwining _ _ f.val h _⟩

def symmetricEquiv : symmetricIntertwiners a n ≃ₗ[ℂ]
    SymmetricSquareDescent.equivariantMaps a n where
  toFun := toEquivariant a n
  invFun f := ⟨fromEquivariant a n f, by
    intro x y
    have hs := f.val.property (Equiv.swap 0 1) ![x, y]
    change f.val.val ![y, x] = f.val.val ![x, y]
    convert hs using 1
    congr 1
    ext i
    fin_cases i <;> rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    ext x y
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact equiv.right_inv f.val.val
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact equiv.map_add f.val.toLinearMap g.val.toLinearMap
  map_smul' z f := by
    apply Subtype.ext
    apply Subtype.ext
    exact equiv.map_smul z f.val.toLinearMap

def symmetricSquareEquiv : symmetricIntertwiners a n ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) n :=
  (symmetricEquiv a n).trans (SymmetricSquareDescent.equivariantEquiv a n).symm

end
end Math.TensorSquareMultilinear

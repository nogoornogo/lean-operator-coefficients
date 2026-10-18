import Math.LinearAlgebra.PairedMultilinear
import Math.RepresentationTheory.TopExteriorCauchy

/-! The universal exterior/symmetric column, without a dimension hypothesis.
The color slots descend through their exterior power; pure symmetric powers
prove alternation without expanding a permutation table. -/
namespace Math.ExteriorSymmetricColumn
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] (n : ℕ)

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V →ₗ[ℂ] W) := inferInstance

def multilinear : MultilinearMap ℂ (fun _ : Fin n => A)
    (Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B)) :=
  ((SymmetricPowerDescent.equiv n).symm.toLinearMap.comp
    (SymmetricMultilinearProjection.project n)).compMultilinearMap
      (PairedMultilinear.map (exteriorPower.ιMulti ℂ n).toMultilinearMap)

def alternating : A [⋀^Fin n]→ₗ[ℂ] (Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B)) where
  toMultilinearMap := multilinear n
  map_eq_zero_of_eq' v i j hij hne := by
    apply SymmetricPurePowers.ext
    intro s
    change TopExteriorCauchy.map v (SymmetricPower.tprod ℂ (fun _ : Fin n => s))=0
    rw [TopExteriorCauchy.diagonal]
    exact (exteriorPower.ιMulti ℂ n).map_eq_zero_of_eq _
      (congrArg (fun a => a ⊗ₜ[ℂ] s) hij) hne

def column : (⋀[ℂ]^n A) ⊗[ℂ] Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B) :=
  TensorProduct.lift (exteriorPower.alternatingMapLinearEquiv
    (N := Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B)) (alternating n))

@[simp] theorem column_pure (a : Fin n → A) (x : Sym[ℂ]^n B) :
    column n (exteriorPower.ιMulti ℂ n a ⊗ₜ[ℂ] x)=TopExteriorCauchy.map a x := by
  change exteriorPower.alternatingMapLinearEquiv
    (N := Sym[ℂ]^n B →ₗ[ℂ] ⋀[ℂ]^n (A ⊗[ℂ] B)) (alternating n)
    (exteriorPower.ιMulti ℂ n a) x=_
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem diagonal (a : Fin n → A) (b : B) :
    column n (exteriorPower.ιMulti ℂ n a ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin n => b))=
      exteriorPower.ιMulti ℂ n (fun i => a i ⊗ₜ[ℂ] b) := by
  rw [column_pure,TopExteriorCauchy.diagonal]

theorem natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    (exteriorPower.map n (TensorProduct.map f g)).comp (column n)=
      (column n).comp (TensorProduct.map (exteriorPower.map n f)
        (SymmetricPower.map (ι := Fin n) g)) := by
  apply TensorProduct.ext'
  intro x y
  have hx : ((exteriorPower.map n (TensorProduct.map f g)).comp (column n)).comp
      ((TensorProduct.mk ℂ _ _).flip y)=
      ((column n).comp (TensorProduct.map (exteriorPower.map n f)
        (SymmetricPower.map (ι := Fin n) g))).comp ((TensorProduct.mk ℂ _ _).flip y) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change exteriorPower.map n (TensorProduct.map f g)
      (column n (exteriorPower.ιMulti ℂ n a ⊗ₜ[ℂ] y))=
      column n (TensorProduct.map (exteriorPower.map n f)
        (SymmetricPower.map (ι := Fin n) g) (exteriorPower.ιMulti ℂ n a ⊗ₜ[ℂ] y))
    rw [column_pure,TensorProduct.map_tmul,exteriorPower.map_apply_ιMulti,column_pure]
    exact LinearMap.congr_fun (TopExteriorCauchy.natural a f g) y
  exact LinearMap.congr_fun hx x

end
end Math.ExteriorSymmetricColumn

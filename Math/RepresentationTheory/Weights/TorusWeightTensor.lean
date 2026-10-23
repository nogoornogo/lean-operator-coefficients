import Math.RepresentationTheory.Weights.TorusWeightSlice
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! A simple circle weight in a tensor factor retains exactly the whole
other representation. Coordinates are symbolic in an arbitrary basis;
neither that basis nor a matrix of the group action is expanded. -/
namespace Math.TorusWeightTensor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor TorusWeightSlice
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G K V U I : Type*} [Group G] [Group K] [DecidableEq I]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  (r : Representation ℂ G V) (s : Representation ℂ K U)
  (t : Circle →* G) (b : Module.Basis I ℂ V) (w : I → ℤ)
  (hb : ∀ z i, r (t z) (b i)=(z : ℂ)^(w i) • b i)
  (hw : Function.Injective w)
abbrev source := external r s

def coordinates : (V ⊗[ℂ] U) ≃ₗ[ℂ] (I →₀ U) := TensorProduct.equivFinsuppOfBasisLeft b
def coordinate (i : I) : (V ⊗[ℂ] U) →ₗ[ℂ] U :=
  (Finsupp.lapply i).comp (coordinates (U := U) b).toLinearMap

theorem coordinate_pure (i : I) (v : V) (u : U) :
    coordinate b i (v ⊗ₜ[ℂ] u)=b.repr v i • u :=
  TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b v u i

include hb in
theorem coordinate_circle (i : I) (z : Circle) (x : V ⊗[ℂ] U) :
    coordinate b i (source r s (t z,1) x)=(z : ℂ)^(w i) • coordinate b i x := by
  classical
  have h : (coordinate (U := U) b i).comp (source r s (t z,1))=
      (z : ℂ)^(w i) • coordinate b i := by
    apply TensorProduct.ext
    apply b.ext
    intro j
    apply LinearMap.ext
    intro u
    change coordinate b i (r (t z) (b j) ⊗ₜ[ℂ] s 1 u)=
      (z : ℂ)^(w i) • coordinate b i (b j ⊗ₜ[ℂ] u)
    rw [map_one]
    change coordinate b i (r (t z) (b j) ⊗ₜ[ℂ] u)=_
    rw [hb, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    simp only [coordinate_pure, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hji : j=i
    · subst j; simp
    · simp [hji]
  exact LinearMap.congr_fun h x

theorem coordinate_residual (i : I) (k : K) (x : V ⊗[ℂ] U) :
    coordinate b i (source r s (1,k) x)=s k (coordinate b i x) := by
  have h : (coordinate (U := U) b i).comp (source r s (1,k))=
      (s k).comp (coordinate b i) := by
    apply TensorProduct.ext'
    intro v u
    change coordinate b i (r 1 v ⊗ₜ[ℂ] s k u)=s k (coordinate b i (v ⊗ₜ[ℂ] u))
    rw [map_one]
    change coordinate b i (v ⊗ₜ[ℂ] s k u)=_
    rw [coordinate_pure, coordinate_pure, map_smul]
  exact LinearMap.congr_fun h x

include hb in
theorem coordinate_off_weight (n : ℤ) (x : Space (source r s) t n) (i : I)
    (hi : w i≠n) : coordinate b i x.val=0 := by
  apply eigen_zero_of_ne hi
  intro z
  have he := congrArg (coordinate (U := U) b i) (x.property z)
  rw [coordinate_circle r s t b w hb, map_smul] at he
  exact he

def extract (i : I) : Space (source r s) t (w i) →ₗ[ℂ] U :=
  (coordinate b i).comp (Space (source r s) t (w i)).subtype

def insert (i : I) : IntertwiningMap s (action (source r s) t (w i)) where
  toLinearMap := (TensorProduct.mk ℂ V U (b i)).codRestrict _ (by
    intro u z
    change r (t z) (b i) ⊗ₜ[ℂ] s 1 u=(z : ℂ)^(w i) • (b i ⊗ₜ[ℂ] u)
    rw [map_one]
    change r (t z) (b i) ⊗ₜ[ℂ] u=_
    rw [hb, TensorProduct.smul_tmul, TensorProduct.tmul_smul])
  isIntertwining' k := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change b i ⊗ₜ[ℂ] s k u=r 1 (b i) ⊗ₜ[ℂ] s k u
    rw [map_one]
    rfl

theorem extract_insert (i : I) (u : U) : extract r s t b w i (insert r s t b w hb i u)=u := by
  classical
  change coordinate b i (b i ⊗ₜ[ℂ] u)=u
  rw [coordinate_pure, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

include hw in
theorem insert_extract (i : I) (x : Space (source r s) t (w i)) :
    insert r s t b w hb i (extract r s t b w i x)=x := by
  classical
  apply Subtype.ext
  apply (coordinates (U := U) b).injective
  ext j
  change coordinate b j (b i ⊗ₜ[ℂ] coordinate b i x.val)=coordinate b j x.val
  rw [coordinate_pure, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hij : i=j
  · subst j; simp
  · rw [ite_eq_right hij, zero_smul]
    exact (coordinate_off_weight r s t b w hb (w i) x j (by
      intro h; exact hij (hw h).symm)).symm

/-- Every matching torus line leaves the entire independent representation
as its actual weight space, with a proved equivariant inverse. -/
def equivalence (i : I) : Representation.Equiv s (action (source r s) t (w i)) where
  toLinearEquiv :=
    { toLinearMap := (insert r s t b w hb i).toLinearMap
      invFun := extract r s t b w i
      left_inv := extract_insert r s t b w hb i
      right_inv := insert_extract r s t b w hb hw i }
  isIntertwining' := (insert r s t b w hb i).isIntertwining'

include hb in
theorem absent_zero (n : ℤ) (hn : ∀ i, w i≠n) (x : Space (source r s) t n) : x=0 := by
  apply Subtype.ext
  apply (coordinates (U := U) b).injective
  ext i
  change coordinate b i x.val=coordinate b i 0
  rw [map_zero]
  exact coordinate_off_weight r s t b w hb n x i (hn i)

end
end Math.TorusWeightTensor

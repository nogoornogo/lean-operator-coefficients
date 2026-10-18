import Math.RepresentationTheory.ExternalInvariantTensor
import Math.RepresentationTheory.Decomposition.Schur
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Schur factorization of a fixed irreducible external gauge carrier.
Copy representations are arbitrary; no topology or semisimplicity is needed. -/
namespace Math.ExternalCopyFactorization
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct MonoidAlgebra
variable {n : ℕ}
variable {G H V A C : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  (r : Representation ℂ G V) (a : Representation ℂ H A) (c : Representation ℂ H C)

def coordinates (b : Module.Basis (Fin n) ℂ C) : V ⊗[ℂ] C ≃ₗ[ℂ] (Fin n → V) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) b.equivFun).trans
    ((TensorProduct.piRight ℂ ℂ V (fun _ : Fin n => ℂ)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.rid ℂ V))

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ C] in
@[simp] theorem coordinates_tmul (b : Module.Basis (Fin n) ℂ C) (v : V) (x : C) (i : Fin n) :
    coordinates b (v ⊗ₜ[ℂ] x) i = b.repr x i • v := by
  simp [coordinates, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

def slice (b : Module.Basis (Fin n) ℂ C)
    (M : IntertwiningMap (external r a) (external r c)) (x : A) (j : Fin n) :
    IntertwiningMap r r where
  toLinearMap := ((LinearMap.proj j).comp (coordinates b).toLinearMap).comp
    (M.toLinearMap.comp ((TensorProduct.mk ℂ V A).flip x))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    have he := M.isIntertwining _ _ (g,1) (v ⊗ₜ[ℂ] x)
    change coordinates b (M (r g v ⊗ₜ[ℂ] x)) j = r g (coordinates b (M (v ⊗ₜ[ℂ] x)) j)
    have he' : M (r g v ⊗ₜ[ℂ] x) = (external r c) (g,1) (M (v ⊗ₜ[ℂ] x)) := by
      simpa [external, Representation.tprod_apply] using he
    rw [he']
    have ht : ∀ t : V ⊗[ℂ] C,
        coordinates b ((external r c) (g,1) t) j = r g (coordinates b t j) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul v y => simp [external, Representation.tprod_apply, coordinates_tmul]
      | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs]
    exact ht _

/-- A factorization on all pure tensors, with an equivariant copy map. -/
theorem exists_copy_map [IsIrreducible r]
    (M : IntertwiningMap (external r a) (external r c)) :
    ∃ m : IntertwiningMap a c, ∀ v x, M (v ⊗ₜ[ℂ] x) = v ⊗ₜ[ℂ] m x := by
  classical
  let : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] r.asModule
  obtain ⟨v0,hv0⟩ := exists_ne (0 : V)
  obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hv0
  let b := Module.finBasis ℂ C
  let rows : A →ₗ[ℂ] (Fin (Module.finrank ℂ C) → ℂ) :=
    LinearMap.pi fun j => phi.comp (((LinearMap.proj j).comp (coordinates b).toLinearMap).comp
      (M.toLinearMap.comp (TensorProduct.mk ℂ V A v0)))
  let m : A →ₗ[ℂ] C := b.equivFun.symm.toLinearMap.comp rows
  have hm : ∀ v x, M (v ⊗ₜ[ℂ] x) = v ⊗ₜ[ℂ] m x := by
    intro v x
    apply (coordinates b).injective
    funext j
    obtain ⟨k,hk⟩ := BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible r (slice r a c b M x j)
    have hval (w : V) : coordinates b (M (w ⊗ₜ[ℂ] x)) j = k • w :=
      DFunLike.congr_fun hk w
    have hrow : rows x j = k := by
      change phi (coordinates b (M (v0 ⊗ₜ[ℂ] x)) j) = k
      rw [hval, map_smul, hphi, smul_eq_mul, mul_one]
    rw [coordinates_tmul, hval]
    have hcoord : b.repr (m x) j = rows x j := by
      exact congrFun (b.equivFun.apply_symm_apply (rows x)) j
    rw [hcoord, hrow]
  have equivariant (h : H) (x : A) : m (a h x) = c h (m x) := by
    have he := M.isIntertwining _ _ (1,h) (v0 ⊗ₜ[ℂ] x)
    have he' : v0 ⊗ₜ[ℂ] m (a h x) = v0 ⊗ₜ[ℂ] c h (m x) := by
      calc
        _ = M (v0 ⊗ₜ[ℂ] a h x) := (hm v0 (a h x)).symm
        _ = (external r c) (1,h) (M (v0 ⊗ₜ[ℂ] x)) := by
          simpa [external, Representation.tprod_apply] using he
        _ = _ := by rw [hm]; simp [external, Representation.tprod_apply]
    have hc := congrArg (fun t : V ⊗[ℂ] C =>
      (TensorProduct.lid ℂ C) (TensorProduct.map phi (LinearMap.id) t)) he'
    simpa [hphi] using hc
  exact ⟨⟨m, fun h => LinearMap.ext (equivariant h)⟩, hm⟩

end
end Math.ExternalCopyFactorization

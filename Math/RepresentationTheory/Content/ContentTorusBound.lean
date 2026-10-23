import Math.RepresentationTheory.Weights.BoundedTorusWeights
import Math.RepresentationTheory.Exterior.IndexedExteriorContent

/-! Sum bounds on the actual complete content decomposition. No independent
species-singlet condition, character extraction or numerical certificate. -/
namespace Math.ContentTorusBound
set_option autoImplicit false
noncomputable section
open Representation BoundedTorusWeights ExteriorContentTree
open scoped TensorProduct
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (rho : Representation ℂ G V) (sigma : Representation ℂ G W) (t : Circle →* G)

theorem tprod (N M : ℕ) (hr : Bounded rho t N) (hs : Bounded sigma t M) :
    Bounded (rho.tprod sigma) t (N+M) := by
  let U := Submodule.span ℂ {v : V ⊗[ℂ] W | ∃ w : ℤ,
    -((N+M : ℕ) : ℤ) ≤ w ∧ w ≤ (N+M : ℕ) ∧ Eigen (rho.tprod sigma) t w v}
  have ht (x : V) (y : W) : x ⊗ₜ[ℂ] y ∈ U := by
    have hx : x ∈ Submodule.span ℂ {v : V | ∃ w : ℤ,
        -(N : ℤ) ≤ w ∧ w ≤ N ∧ Eigen rho t w v} := by rw [hr]; trivial
    induction hx using Submodule.span_induction generalizing y with
    | mem x hx =>
      have hy : y ∈ Submodule.span ℂ {v : W | ∃ w : ℤ,
          -(M : ℤ) ≤ w ∧ w ≤ M ∧ Eigen sigma t w v} := by rw [hs]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a,ha₀,ha₁,ha⟩ := hx
        obtain ⟨b,hb₀,hb₁,hb⟩ := hy
        exact Submodule.subset_span ⟨a+b,by push_cast; omega,by push_cast; omega,
          eigen_tmul rho t sigma ha hb⟩
      | zero => simp
      | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact U.add_mem hy hz
      | smul c y _ hy => rw [TensorProduct.tmul_smul]; exact U.smul_mem c hy
    | zero => simp
    | add x z _ _ hx hz => rw [TensorProduct.add_tmul]; exact U.add_mem (hx y) (hz y)
    | smul c x _ hx =>
      change c • (x ⊗ₜ[ℂ] y) ∈ U
      exact U.smul_mem c (hx y)
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ht x y
  | add x y hx hy => exact U.add_mem hx hy

variable (t : Circle →* G)

theorem indexed (k : ℕ) (a : Fin (k+1) → Leaf G) (N : Fin (k+1) → ℕ)
    (h : ∀ s, Bounded ((a s).rho.exteriorPower (a s).degree) t (N s)) :
    Bounded (factor (IndexedExteriorContent.tree k a)) t (∑ s, N s) := by
  induction k with
  | zero =>
    change Bounded ((a 0).rho.exteriorPower (a 0).degree) t (∑ s, N s)
    simpa using h 0
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    exact tprod _ _ t _ _ (h 0) (ih (fun i => a i.succ) (fun i => N i.succ) (fun i => h i.succ))

theorem word (k : ℕ) (a : Fin (k+1) → Leaf G) {n : ℕ} (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i=s)).card = (a s).degree)
    (N : Fin (k+1) → ℕ)
    (h : ∀ s, Bounded ((a s).rho.exteriorPower (a s).degree) t (N s)) :
    Bounded (PatternExteriorSource.representation (fun s => (a s).rho) p) t (∑ s, N s) :=
  bounded_of_surjective _ t _ (IndexedExteriorContent.wordDecomposition k a p hc).toIntertwiningMap
    (IndexedExteriorContent.wordDecomposition k a p hc).surjective _ (indexed t k a N h)

end
end Math.ContentTorusBound

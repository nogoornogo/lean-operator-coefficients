import Math.RepresentationTheory.SL2SymmetricSpan
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Finite direct products and the algebraic dual doublet are spanned by the
same SL2 symmetric powers. -/
namespace Math.SL2SpannedProducts
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings SL2SymmetricSpan

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem image (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W)
    (q : IntertwiningMap rho sigma) (hr : Spanned rho) (x : V) :
    q x ∈ Submodule.span ℂ (generators sigma) := by
  have hx : x ∈ Submodule.span ℂ (generators rho) := by rw [hr]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,f,v,rfl⟩ := hx
    exact Submodule.subset_span ⟨n,q.comp f,v,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

def inl (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W) :
    IntertwiningMap rho (rho.prod sigma) where
  toLinearMap := LinearMap.inl ℂ V W
  isIntertwining' g := by ext x <;> simp

def inr (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W) :
    IntertwiningMap sigma (rho.prod sigma) where
  toLinearMap := LinearMap.inr ℂ V W
  isIntertwining' g := by ext x <;> simp

theorem prod (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W)
    (hr : Spanned rho) (hs : Spanned sigma) : Spanned (rho.prod sigma) := by
  apply top_unique
  intro x _
  have h := Submodule.add_mem (Submodule.span ℂ (generators (rho.prod sigma)))
    (image rho _ (inl rho sigma) hr x.1) (image sigma _ (inr rho sigma) hs x.2)
  simpa [inl,inr] using h

theorem transport {rho : Representation ℂ Group V} {sigma : Representation ℂ Group W}
    (e : Representation.Equiv rho sigma) (hr : Spanned rho) : Spanned sigma :=
  of_surjective _ _ e.toIntertwiningMap e.surjective hr

theorem epsilon_invariant (g : Group) (v w : Doublet) :
    SU2DoubletDuality.epsilon (doublet g v) (doublet g w) =
      SU2DoubletDuality.epsilon v w := by
  have hd := g.property
  rw [Matrix.det_fin_two] at hd
  change (((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) 0 *
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec w) 1 -
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) 1 *
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec w) 0) = _
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,SU2DoubletDuality.epsilon_apply]
  linear_combination (v 0*w 1-v 1*w 0)*hd

def doubletDuality : Representation.Equiv doublet doublet.dual where
  toLinearEquiv := SU2DoubletDuality.equivalence.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change SU2DoubletDuality.epsilon (doublet g v) w =
      SU2DoubletDuality.epsilon v (doublet g⁻¹ w)
    have he := epsilon_invariant g v (doublet g⁻¹ w)
    simpa only [Representation.self_inv_apply] using he

theorem dualDoublet : Spanned doublet.dual := transport doubletDuality standard

end
end Math.SL2SpannedProducts

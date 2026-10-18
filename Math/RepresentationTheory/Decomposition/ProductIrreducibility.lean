import Math.RepresentationTheory.Decomposition.Burnside
import Math.RepresentationTheory.Decomposition.ExternalTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

/-!
# Irreducibility of external tensor products

For finite-dimensional representations over an algebraically closed field,
the external tensor product of two irreducibles is irreducible.  The proof
uses the finite-dimensional Burnside lemma to realize rank-one operators by
the two group algebras.
-/

namespace Math
namespace ProductIrreducibility

open TensorProduct ExternalTensorProduct Burnside
open scoped MonoidAlgebra

noncomputable section

variable {k G H V W : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Group H]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W] in
/-- A subrepresentation for the external product is stable under every
group-algebra operator acting on the first tensor factor. -/
theorem map_asAlgebraHom_id_mem
    (rho : Representation k G V) (sigma : Representation k H W)
    (S : Subrepresentation (externalTprod rho sigma))
    (r : k[G]) (x : V ⊗[k] W) (hx : x ∈ S) :
    TensorProduct.map (rho.asAlgebraHom r) LinearMap.id x ∈ S.toSubmodule := by
  apply MonoidAlgebra.induction_on r
  · intro g
    have hg := S.apply_mem_toSubmodule (g, 1) hx
    simpa [externalTprod_apply, Module.End.one_eq_id] using hg
  · intro r s hr hs
    rw [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
    exact S.toSubmodule.add_mem hr hs
  · intro c r hr
    rw [map_smul, TensorProduct.map_smul_left, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c hr

omit [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W] in
/-- A subrepresentation for the external product is stable under every
group-algebra operator acting on the second tensor factor. -/
theorem map_id_asAlgebraHom_mem
    (rho : Representation k G V) (sigma : Representation k H W)
    (S : Subrepresentation (externalTprod rho sigma))
    (s : k[H]) (x : V ⊗[k] W) (hx : x ∈ S) :
    TensorProduct.map LinearMap.id (sigma.asAlgebraHom s) x ∈ S.toSubmodule := by
  apply MonoidAlgebra.induction_on s
  · intro h
    have hh := S.apply_mem_toSubmodule (1, h) hx
    simpa [externalTprod_apply, Module.End.one_eq_id] using hh
  · intro r s hr hs
    rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply]
    exact S.toSubmodule.add_mem hr hs
  · intro c r hr
    rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c hr

/-- The rank-one operator determined by a basis coordinate and an output
vector. -/
def rankOne {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module k M]
    (b : Module.Basis I k M) (i : I) (m : M) : M →ₗ[k] M :=
  (b.coord i).smulRight m

omit [IsAlgClosed k] in
@[simp]
theorem rankOne_apply {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module k M]
    (b : Module.Basis I k M) (i : I) (m x : M) :
    rankOne b i m x = b.repr x i • m :=
  rfl

omit [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Tensoring two coordinate rank-one maps gives the corresponding rank-one
map for the tensor-product basis. -/
theorem map_rankOne_rankOne
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (bV : Module.Basis I k V) (bW : Module.Basis J k W)
    (i : I) (j : J) (v : V) (w : W) :
    TensorProduct.map (rankOne bV i v) (rankOne bW j w) =
      ((bV.tensorProduct bW).coord (i, j)).smulRight (v ⊗ₜ[k] w) := by
  apply TensorProduct.ext'
  intro x y
  simp only [rankOne_apply, TensorProduct.map_tmul,
    LinearMap.smulRight_apply]
  rw [TensorProduct.smul_tmul_smul]
  simp [mul_comm]

/-- The external tensor product of finite-dimensional irreducible
representations over an algebraically closed field is irreducible. -/
theorem externalTprod_isIrreducible
    (rho : Representation k G V) (sigma : Representation k H W)
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma] :
    Representation.IsIrreducible (externalTprod rho sigma) := by
  let : Nontrivial V := IsSimpleModule.nontrivial k[G] rho.asModule
  let : Nontrivial W := IsSimpleModule.nontrivial k[H] sigma.asModule
  let bV := Module.finBasis k V
  let bW := Module.finBasis k W
  let b := bV.tensorProduct bW
  have hdimV : 0 < Module.finrank k V := Module.finrank_pos
  have hdimW : 0 < Module.finrank k W := Module.finrank_pos
  let i0 : Fin (Module.finrank k V) := ⟨0, hdimV⟩
  let j0 : Fin (Module.finrank k W) := ⟨0, hdimW⟩
  let : Nontrivial (V ⊗[k] W) :=
    ⟨⟨b (i0, j0), 0, b.ne_zero (i0, j0)⟩⟩
  let : Nontrivial (Subrepresentation (externalTprod rho sigma)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top :
        (⊥ : Submodule k (V ⊗[k] W)) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.ext
    exact h
  obtain ⟨x, hxS, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hSub
  have hxrepr : b.repr x ≠ 0 := by
    intro h
    apply hx0
    apply b.repr.injective
    simpa using h
  have hCoeff : ∃ ij, b.repr x ij ≠ 0 := by
    by_contra h
    push Not at h
    apply hxrepr
    ext ij
    exact h ij
  obtain ⟨⟨i, j⟩, hij⟩ := hCoeff
  have hpure : ∀ (v : V) (w : W), v ⊗ₜ[k] w ∈ S.toSubmodule := by
    intro v w
    let c := b.repr x (i, j)
    let pV : V →ₗ[k] V := rankOne bV i (c⁻¹ • v)
    let pW : W →ₗ[k] W := rankOne bW j w
    obtain ⟨r, hr⟩ := representation_asAlgebraHom_surjective rho pV
    obtain ⟨s, hs⟩ := representation_asAlgebraHom_surjective sigma pW
    have hfirst : TensorProduct.map pV LinearMap.id x ∈ S.toSubmodule := by
      simpa [hr] using map_asAlgebraHom_id_mem rho sigma S r x hxS
    have hsecond :
        TensorProduct.map LinearMap.id pW
            (TensorProduct.map pV LinearMap.id x) ∈ S.toSubmodule := by
      simpa [hs] using map_id_asAlgebraHom_mem rho sigma S s
        (TensorProduct.map pV LinearMap.id x) hfirst
    have hcompose :
        TensorProduct.map LinearMap.id pW
            (TensorProduct.map pV LinearMap.id x) =
          TensorProduct.map pV pW x := by
      rw [TensorProduct.map_map]
      rfl
    rw [hcompose] at hsecond
    have hrank := LinearMap.congr_fun
      (map_rankOne_rankOne bV bW i j (c⁻¹ • v) w) x
    change TensorProduct.map pV pW x =
      c • ((c⁻¹ • v) ⊗ₜ[k] w) at hrank
    rw [hrank] at hsecond
    have hc : c ≠ 0 := hij
    simpa [TensorProduct.smul_tmul', smul_smul, mul_inv_cancel₀ hc] using hsecond
  apply top_unique
  change (⊤ : Submodule k (V ⊗[k] W)) ≤ S.toSubmodule
  rw [← TensorProduct.span_tmul_eq_top k V W]
  apply Submodule.span_le.2
  rintro t ⟨v, w, rfl⟩
  exact hpure v w

end

end ProductIrreducibility
end Math

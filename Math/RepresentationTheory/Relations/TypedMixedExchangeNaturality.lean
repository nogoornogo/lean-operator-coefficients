import Math.RepresentationTheory.Relations.TypedMixedExchangeQuotient

/-! Species-wise maps preserve the actual signed mixed exchange relations. -/
namespace Math.TypedMixedExchangeNaturality
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q : Type*} {V V' : P → Type*} {W W' : Q → Type*}
  [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  [∀ u, AddCommGroup (V' u)] [∀ u, Module ℂ (V' u)]
  [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  [∀ u, AddCommGroup (W' u)] [∀ u, Module ℂ (W' u)]
  (f : ∀ u, V u →ₗ[ℂ] V' u) (g : ∀ u, W u →ₗ[ℂ] W' u)
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

def tensorMap : TypedMixedExchangeQuotient.Domain (V := V) (W := W) p s →ₗ[ℂ]
    TypedMixedExchangeQuotient.Domain (V := V') (W := W') p s :=
  TensorProduct.map (PiTensorProduct.map (fun i => f (p i)))
    (PiTensorProduct.map (fun j => g (s j)))

theorem tensorMap_pure (v : Fin n → ∀ u, V u) (w : Fin m → ∀ u, W u) :
    tensorMap f g p s (TypedMixedExchangeQuotient.pure p s v w) =
    TypedMixedExchangeQuotient.pure p s (fun i u => f u (v i u))
      (fun j u => g u (w j u)) := by
  simp only [tensorMap, TypedMixedExchangeQuotient.pure, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod]

theorem map_relations : TypedMixedExchangeQuotient.relations (V := V) (W := W) p s ≤
    (TypedMixedExchangeQuotient.relations (V := V') (W := W') p s).comap
      (tensorMap f g p s) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  cases x with
  | inl x =>
    change tensorMap f g p s (TypedMixedExchangeQuotient.relation p s (.inl x)) ∈
      TypedMixedExchangeQuotient.relations (V := V') (W := W') p s
    have he : tensorMap f g p s (TypedMixedExchangeQuotient.relation p s (.inl x)) =
        TypedMixedExchangeQuotient.relation p s (.inl
          (x.1, (fun i u => f u (x.2.1 i u)), (fun j u => g u (x.2.2 j u)))) := by
      simp only [TypedMixedExchangeQuotient.relation, map_sub, Units.smul_def,
        map_zsmul, tensorMap_pure, Function.comp_def]
    rw [he]
    exact Submodule.subset_span ⟨_,rfl⟩
  | inr x =>
    change tensorMap f g p s (TypedMixedExchangeQuotient.relation p s (.inr x)) ∈
      TypedMixedExchangeQuotient.relations (V := V') (W := W') p s
    have he : tensorMap f g p s (TypedMixedExchangeQuotient.relation p s (.inr x)) =
        TypedMixedExchangeQuotient.relation p s (.inr
          (x.1, (fun i u => f u (x.2.1 i u)), (fun j u => g u (x.2.2 j u)))) := by
      simp only [TypedMixedExchangeQuotient.relation, map_sub, tensorMap_pure,
        Function.comp_def]
    rw [he]
    exact Submodule.subset_span ⟨_,rfl⟩

section Equivariance
variable {H : Type*} [Group H]
  (r : ∀ u, Representation ℂ H (V u)) (t : ∀ u, Representation ℂ H (W u))
  (r' : ∀ u, Representation ℂ H (V' u)) (t' : ∀ u, Representation ℂ H (W' u))
  (e : ∀ u, IntertwiningMap (r u) (r' u))
  (h : ∀ u, IntertwiningMap (t u) (t' u))

def intertwiner : IntertwiningMap (TypedMixedExchangeQuotient.action r t p s)
    (TypedMixedExchangeQuotient.action r' t' p s) where
  toLinearMap := tensorMap (fun u => (e u).toLinearMap) (fun u => (h u).toLinearMap) p s
  isIntertwining' k := by
    apply TypedMixedTensorHom.pure_ext
    intro v w
    simp only [LinearMap.comp_apply, tensorMap, TypedMixedExchangeQuotient.action,
      Representation.tprod_apply, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
      MultilinearInvariantHom.tensorRepresentation_tprod]
    congr 1
    · congr 1
      funext i
      exact IntertwiningMap.isIntertwining _ _ (e (p i)) k (v i)
    · congr 1
      funext i
      exact IntertwiningMap.isIntertwining _ _ (h (s i)) k (w i)

variable (e' : ∀ u, Representation.Equiv (r u) (r' u))
  (h' : ∀ u, Representation.Equiv (t u) (t' u))

def tensorEquiv : Representation.Equiv (TypedMixedExchangeQuotient.action r t p s)
    (TypedMixedExchangeQuotient.action r' t' p s) where
  toLinearEquiv := TensorProduct.congr (PiTensorProduct.congr (fun i => (e' (p i)).toLinearEquiv))
    (PiTensorProduct.congr (fun j => (h' (s j)).toLinearEquiv))
  isIntertwining' := (intertwiner p s r t r' t'
    (fun u => (e' u).toIntertwiningMap) (fun u => (h' u).toIntertwiningMap)).isIntertwining'

theorem relations_map_equiv : (TypedMixedExchangeQuotient.relations (V := V) (W := W) p s).map
    (tensorEquiv p s r t r' t' e' h').toLinearMap =
    TypedMixedExchangeQuotient.relations (V := V') (W := W') p s := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact map_relations (fun u => (e' u).toLinearMap) (fun u => (h' u).toLinearMap) p s hu
  · intro u hu
    refine ⟨(tensorEquiv p s r t r' t' e' h').symm u, ?_, ?_⟩
    · exact map_relations (fun u => (e' u).symm.toLinearMap)
        (fun u => (h' u).symm.toLinearMap) p s hu
    · exact (tensorEquiv p s r t r' t' e' h').toLinearEquiv.apply_symm_apply u
end Equivariance
end
end Math.TypedMixedExchangeNaturality

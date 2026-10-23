import Math.RepresentationTheory.Tensors.TypedMixedTensorHom
import Math.RepresentationTheory.Relations.RelationQuotient

/-! Explicit same-species signed exchange relations on heterogeneous mixed tensors. -/
namespace Math.TypedMixedExchangeQuotient
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

abbrev Domain := TypedMixedTensorHom.Domain (V := fun i => V (p i))
  (W := fun j => W (s j))
def action : Representation ℂ G (Domain (V := V) (W := W) p s) :=
  (MultilinearInvariantHom.tensorRepresentation (fun i => r (p i))).tprod
    (MultilinearInvariantHom.tensorRepresentation (fun j => t (s j)))
def pure (v : Fin n → ∀ u, V u) (w : Fin m → ∀ u, W u) :
    Domain (V := V) (W := W) p s :=
  PiTensorProduct.tprod ℂ (fun i => v i (p i)) ⊗ₜ[ℂ]
    PiTensorProduct.tprod ℂ (fun j => w j (s j))
abbrev FermionIndex := {e : Equiv.Perm (Fin n) // p ∘ e = p} ×
  (Fin n → ∀ u, V u) × (Fin m → ∀ u, W u)
abbrev BosonIndex := {e : Equiv.Perm (Fin m) // s ∘ e = s} ×
  (Fin n → ∀ u, V u) × (Fin m → ∀ u, W u)
abbrev Index := Sum (FermionIndex (V := V) (W := W) p (m := m))
  (BosonIndex (V := V) (W := W) s (n := n))
def relation : Index (V := V) (W := W) p s → Domain (V := V) (W := W) p s
  | .inl x => Equiv.Perm.sign x.1.val • pure p s (x.2.1 ∘ x.1.val) x.2.2 -
      pure p s x.2.1 x.2.2
  | .inr x => pure p s x.2.1 (x.2.2 ∘ x.1.val) - pure p s x.2.1 x.2.2
abbrev relations := RelationQuotient.relations (k := ℂ) (relation (V := V) (W := W) p s)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem action_pure (g : G) (v : Fin n → ∀ u, V u) (w : Fin m → ∀ u, W u) :
    action r t p s g (pure p s v w) =
      pure p s (fun i u => r u g (v i u)) (fun j u => t u g (w j u)) := by
  simp only [action, pure, Representation.tprod_apply, TensorProduct.map_tmul,
    MultilinearInvariantHom.tensorRepresentation_tprod]

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem stable : ∀ g, relations (V := V) (W := W) p s ≤
    (relations p s).comap (action r t p s g) := by
  apply RelationQuotient.relations_stable
  intro g x
  cases x with
  | inl x =>
    have he : action r t p s g (relation p s (.inl x)) =
        relation p s (.inl (x.1, (fun i u => r u g (x.2.1 i u)),
          (fun j u => t u g (x.2.2 j u)))) := by
      simp only [relation, map_sub, Units.smul_def, map_zsmul, action_pure, Function.comp_def]
    rw [he]
    exact Submodule.subset_span ⟨_, rfl⟩
  | inr x =>
    have he : action r t p s g (relation p s (.inr x)) =
        relation p s (.inr (x.1, (fun i u => r u g (x.2.1 i u)),
          (fun j u => t u g (x.2.2 j u)))) := by
      simp only [relation, map_sub, action_pure, Function.comp_def]
    rw [he]
    exact Submodule.subset_span ⟨_, rfl⟩

abbrev quotient := (action r t p s).quotient (relations p s) (stable r t p s)

omit [Fintype P] [Fintype Q] in
theorem vanish_iff (f : IntertwiningMap (action r t p s) (trivial ℂ G ℂ)) :
    f ∈ RelationQuotient.vanishing (action r t p s) (trivial ℂ G ℂ) (relations p s) ↔
      MixedPatternAssembly.FermionCompatible p s (TypedMixedTensorHom.orderedEquiv f.toLinearMap) ∧
      MixedPatternAssembly.BosonCompatible p s (TypedMixedTensorHom.orderedEquiv f.toLinearMap) := by
  rw [RelationQuotient.vanish_relations_iff]
  constructor
  · intro h
    constructor
    · intro e he v
      ext w
      have hh := h (.inl (⟨e, he⟩, v, fun j => Pi.single (s j) (w j)))
      simpa only [relation, map_sub, Units.smul_def, map_zsmul, sub_eq_zero,
        pure, MixedPatternAssembly.FermionCompatible, TypedPatternAlternation.ordered,
        MultilinearMap.compLinearMap_apply, TypedMixedTensorHom.orderedEquiv_apply,
        smul_apply, Pi.single_eq_same, LinearMap.proj_apply,
        IntertwiningMap.toLinearMap_apply] using hh
    · intro v e he w
      have hh := h (.inr (⟨e, he⟩, (fun i => Pi.single (p i) (v i)), w))
      simpa only [relation, map_sub, sub_eq_zero, pure,
        TypedPatternSymmetrization.ordered, TypedPatternAlternation.ordered,
        MultilinearMap.compLinearMap_apply, LinearMap.proj_apply,
        IntertwiningMap.toLinearMap_apply,
        TypedMixedTensorHom.orderedEquiv_apply, Pi.single_eq_same] using hh
  · rintro ⟨hf, hb⟩ x
    cases x with
    | inl x =>
      have hh := congrArg (fun z => z (fun j => x.2.2 j (s j)))
        (hf x.1.val x.1.property x.2.1)
      simpa only [relation, map_sub, Units.smul_def, map_zsmul, sub_eq_zero,
        TypedPatternAlternation.ordered, MultilinearMap.compLinearMap_apply,
        TypedMixedTensorHom.orderedEquiv_apply, pure, smul_apply,
        LinearMap.proj_apply, IntertwiningMap.toLinearMap_apply] using hh
    | inr x =>
      have hh := hb (fun i => x.2.1 i (p i)) x.1.val x.1.property x.2.2
      simpa only [relation, map_sub, sub_eq_zero,
        TypedPatternSymmetrization.ordered, TypedPatternAlternation.ordered,
        MultilinearMap.compLinearMap_apply, LinearMap.proj_apply,
        IntertwiningMap.toLinearMap_apply,
        TypedMixedTensorHom.orderedEquiv_apply, pure] using hh

def constrainedEquiv : MixedPatternAssembly.orderedSpace r t p s ≃ₗ[ℂ]
    RelationQuotient.vanishing (action r t p s) (trivial ℂ G ℂ) (relations p s) where
  toFun k := ⟨TypedMixedTensorHom.assemble (fun i => r (p i)) (fun j => t (s j))
    ⟨k.val, k.property.1⟩, (vanish_iff r t p s _).mpr (by
      simpa only [TypedMixedTensorHom.assemble, LinearEquiv.apply_symm_apply] using k.property.2)⟩
  invFun f := ⟨TypedMixedTensorHom.orderedEquiv f.val.toLinearMap,
    ⟨((TypedMixedTensorHom.equiv (fun i => r (p i)) (fun j => t (s j))) f.val).property,
      (vanish_iff r t p s f.val).mp f.property⟩⟩
  left_inv k := by apply Subtype.ext; exact TypedMixedTensorHom.orderedEquiv.apply_symm_apply k.val
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact TypedMixedTensorHom.orderedEquiv.symm_apply_apply f.val.toLinearMap
  map_add' k l := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact TypedMixedTensorHom.orderedEquiv.symm.map_add _ _
  map_smul' z k := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact TypedMixedTensorHom.orderedEquiv.symm.map_smul z _

def equiv : MixedPatternAssembly.orderedSpace r t p s ≃ₗ[ℂ]
    IntertwiningMap (quotient r t p s) (trivial ℂ G ℂ) :=
  (constrainedEquiv r t p s).trans
    (RelationQuotient.equiv (action r t p s) (trivial ℂ G ℂ) (relations p s) (stable r t p s))

def projection : IntertwiningMap (action r t p s) (quotient r t p s) :=
  RelationQuotient.projection (action r t p s) (relations p s) (stable r t p s)

omit [Fintype P] [Fintype Q] in
theorem equiv_mk (k : MixedPatternAssembly.orderedSpace r t p s)
    (u : Domain (V := V) (W := W) p s) :
    equiv r t p s k (projection r t p s u) =
      TypedMixedTensorHom.orderedEquiv.symm k.val u := rfl

end
end Math.TypedMixedExchangeQuotient

import Math.RepresentationTheory.CommutingActionHom
import Math.RepresentationTheory.RelationQuotientNaturality
import Math.RepresentationTheory.InvariantHomRestriction

/-! Direct local-coinvariant transport and restriction commute with descent. -/
namespace Math.LocalCoinvariantNaturality
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  (a : Representation k G U) (b : Representation k H U)
  (ha : ∀ g h u, a g (b h u) = b h (a g u))
  (a' : Representation k G V) (b' : Representation k H V)
  (ha' : ∀ g h v, a' g (b' h v) = b' h (a' g v))
  (f : IntertwiningMap b b') (hf : ∀ g u, f (a g u) = a' g (f u))

include hf in
theorem map_relations : LocalCoinvariantHom.relations a ≤
    (LocalCoinvariantHom.relations a').comap f.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,u⟩,rfl⟩
  change f (a g u - u) ∈ LocalCoinvariantHom.relations a'
  rw [map_sub, hf]
  exact Submodule.subset_span ⟨(g,f u),rfl⟩

def quotientMap : IntertwiningMap (LocalCoinvariantHom.quotient a b ha)
    (LocalCoinvariantHom.quotient a' b' ha') :=
  RelationQuotientNaturality.quotientMap b b'
    (LocalCoinvariantHom.relations a) (LocalCoinvariantHom.relations a')
    (LocalCoinvariantHom.stable a b ha) (LocalCoinvariantHom.stable a' b' ha') f
    (map_relations a b a' b' f hf)

@[simp] theorem quotientMap_mk (u : U) :
    quotientMap a b ha a' b' ha' f hf ((LocalCoinvariantHom.relations a).mkQ u) =
      (LocalCoinvariantHom.relations a').mkQ (f u) := rfl

theorem relations_map_equiv (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) :
    (LocalCoinvariantHom.relations a).map e.toLinearMap = LocalCoinvariantHom.relations a' := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact map_relations a b a' b' e.toIntertwiningMap he hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,u⟩,rfl⟩
    refine ⟨LocalCoinvariantHom.relation a (g,e.symm u),
      Submodule.subset_span ⟨(g,e.symm u),rfl⟩, ?_⟩
    change e (a g (e.symm u) - e.symm u) = a' g u - u
    rw [map_sub, he, Representation.Equiv.apply_symm_apply]

def quotientEquiv (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) :
    Representation.Equiv (LocalCoinvariantHom.quotient a b ha)
      (LocalCoinvariantHom.quotient a' b' ha') :=
  RelationQuotientNaturality.quotientEquiv b b'
    (LocalCoinvariantHom.relations a) (LocalCoinvariantHom.relations a')
    (LocalCoinvariantHom.stable a b ha) (LocalCoinvariantHom.stable a' b' ha') e
    (relations_map_equiv a b a' b' e he)

@[simp] theorem quotientEquiv_mk (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) (u : U) :
    quotientEquiv a b ha a' b' ha' e he ((LocalCoinvariantHom.relations a).mkQ u) =
      (LocalCoinvariantHom.relations a').mkQ (e u) := rfl

def pull : LocalCoinvariantHom.invariantHom a' b' (trivial k H k) →ₗ[k]
    LocalCoinvariantHom.invariantHom a b (trivial k H k) where
  toFun q := ⟨q.val.comp f, by intro g u; change q.val (f (a g u)) = q.val (f u); rw [hf, q.property]⟩
  map_add' _ _ := by apply Subtype.ext; ext u; rfl
  map_smul' _ _ := by apply Subtype.ext; ext u; rfl

theorem extraction (q : LocalCoinvariantHom.invariantHom a' b' (trivial k H k)) :
    LocalCoinvariantHom.equiv a b (trivial k H k) ha (pull a b a' b' f hf q) =
    (LocalCoinvariantHom.equiv a' b' (trivial k H k) ha' q).comp
      (quotientMap a b ha a' b' ha' f hf) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations a).mkQ_surjective u
  rfl

section Restriction
variable {J : Type*} [Group J] (j : J →* H)

def restrictInput : LocalCoinvariantHom.invariantHom a b (trivial k H k) →ₗ[k]
    LocalCoinvariantHom.invariantHom a (b.comp j) (trivial k J k) where
  toFun q := ⟨InvariantHomRestriction.restrict b j q.val, q.property⟩
  map_add' _ _ := by apply Subtype.ext; ext u; rfl
  map_smul' _ _ := by apply Subtype.ext; ext u; rfl

theorem restrict_extraction (q : LocalCoinvariantHom.invariantHom a b (trivial k H k)) :
    LocalCoinvariantHom.equiv a (b.comp j) (trivial k J k)
      (fun g h u => ha g (j h) u) (restrictInput a b j q) =
    InvariantHomRestriction.restrict (LocalCoinvariantHom.quotient a b ha) j
      (LocalCoinvariantHom.equiv a b (trivial k H k) ha q) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations a).mkQ_surjective u
  rfl
end Restriction
end
end Math.LocalCoinvariantNaturality

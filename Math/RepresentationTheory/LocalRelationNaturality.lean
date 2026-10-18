import Math.RepresentationTheory.LocalRelationHom
import Math.RepresentationTheory.LocalCoinvariantNaturality

/-! Direct two-stage local/exchange quotient maps, not transported through Hom. -/
namespace Math.LocalRelationNaturality
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  (a : Representation k G U) (b : Representation k H U)
  (ha : ∀ g h u, a g (b h u) = b h (a g u))
  (R : Submodule k U) (hr : ∀ h, R ≤ R.comap (b h))
  (a' : Representation k G V) (b' : Representation k H V)
  (ha' : ∀ g h v, a' g (b' h v) = b' h (a' g v))
  (S : Submodule k V) (hs : ∀ h, S ≤ S.comap (b' h))
  (f : IntertwiningMap b b') (hf : ∀ g u, f (a g u) = a' g (f u))
  (hR : R ≤ S.comap f.toLinearMap)

include hR in
theorem map_image : LocalRelationHom.image a R ≤
    (LocalRelationHom.image a' S).comap
      (LocalCoinvariantNaturality.quotientMap a b ha a' b' ha' f hf).toLinearMap := by
  rintro _ ⟨u,hu,rfl⟩
  exact ⟨f u,hR hu,rfl⟩

def quotientMap : IntertwiningMap (LocalRelationHom.residual a b ha R hr)
    (LocalRelationHom.residual a' b' ha' S hs) :=
  RelationQuotientNaturality.quotientMap
    (LocalCoinvariantHom.quotient a b ha) (LocalCoinvariantHom.quotient a' b' ha')
    (LocalRelationHom.image a R) (LocalRelationHom.image a' S)
    (LocalRelationHom.image_stable a b ha R hr) (LocalRelationHom.image_stable a' b' ha' S hs)
    (LocalCoinvariantNaturality.quotientMap a b ha a' b' ha' f hf)
    (map_image a b ha R a' b' ha' S f hf hR)

@[simp] theorem quotientMap_mk (u : U) :
    quotientMap a b ha R hr a' b' ha' S hs f hf hR
      ((LocalRelationHom.image a R).mkQ ((LocalCoinvariantHom.relations a).mkQ u)) =
    (LocalRelationHom.image a' S).mkQ ((LocalCoinvariantHom.relations a').mkQ (f u)) := rfl

theorem image_map_equiv (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) :
    (LocalRelationHom.image a R).map
      (LocalCoinvariantNaturality.quotientEquiv a b ha a' b' ha' e he).toLinearMap =
      LocalRelationHom.image a' (R.map e.toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨q,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨e u,⟨u,hu,rfl⟩,rfl⟩
  · rintro _ ⟨v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨(LocalCoinvariantHom.relations a).mkQ u,⟨u,hu,rfl⟩,rfl⟩

def quotientEquiv (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) (heR : R.map e.toLinearMap = S) :
    Representation.Equiv (LocalRelationHom.residual a b ha R hr)
      (LocalRelationHom.residual a' b' ha' S hs) :=
  RelationQuotientNaturality.quotientEquiv
    (LocalCoinvariantHom.quotient a b ha) (LocalCoinvariantHom.quotient a' b' ha')
    (LocalRelationHom.image a R) (LocalRelationHom.image a' S)
    (LocalRelationHom.image_stable a b ha R hr) (LocalRelationHom.image_stable a' b' ha' S hs)
    (LocalCoinvariantNaturality.quotientEquiv a b ha a' b' ha' e he)
    ((image_map_equiv a b ha R a' b' ha' e he).trans
      (congrArg (LocalRelationHom.image a') heR))

@[simp] theorem quotientEquiv_mk (e : Representation.Equiv b b')
    (he : ∀ g u, e (a g u) = a' g (e u)) (heR : R.map e.toLinearMap = S) (u : U) :
    quotientEquiv a b ha R hr a' b' ha' S hs e he heR
      ((LocalRelationHom.image a R).mkQ ((LocalCoinvariantHom.relations a).mkQ u)) =
    (LocalRelationHom.image a' S).mkQ ((LocalCoinvariantHom.relations a').mkQ (e u)) := rfl

def pull : LocalRelationHom.Input a' b' (trivial k H k) S →ₗ[k]
    LocalRelationHom.Input a b (trivial k H k) R where
  toFun q := ⟨LocalCoinvariantNaturality.pull a b a' b' f hf q.val, fun u hu => q.property (hR hu)⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; ext u; rfl
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; ext u; rfl

theorem extraction (q : LocalRelationHom.Input a' b' (trivial k H k) S) :
    LocalRelationHom.equiv a b (trivial k H k) ha R hr
      (pull a b R a' b' S f hf hR q) =
    (LocalRelationHom.equiv a' b' (trivial k H k) ha' S hs q).comp
      (quotientMap a b ha R hr a' b' ha' S hs f hf hR) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalRelationHom.image a R).mkQ_surjective u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations a).mkQ_surjective u
  rfl

theorem reconstruction (q : IntertwiningMap (LocalRelationHom.residual a' b' ha' S hs)
    (trivial k H k)) :
    (LocalRelationHom.equiv a b (trivial k H k) ha R hr).symm
      (q.comp (quotientMap a b ha R hr a' b' ha' S hs f hf hR)) =
    pull a b R a' b' S f hf hR
      ((LocalRelationHom.equiv a' b' (trivial k H k) ha' S hs).symm q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply IntertwiningMap.ext
  rfl
end
end Math.LocalRelationNaturality

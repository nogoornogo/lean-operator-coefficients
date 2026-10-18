import Math.RepresentationTheory.RelationQuotient

/-! Direct quotient maps and contravariant Hom descent naturality. -/
namespace Math.RelationQuotientNaturality
set_option autoImplicit false
noncomputable section
open Representation
variable {k H U V W : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  (a : Representation k H U) (b : Representation k H V) (t : Representation k H W)
  (R : Submodule k U) (S : Submodule k V)
  (hr : ∀ h, R ≤ R.comap (a h)) (hs : ∀ h, S ≤ S.comap (b h))
  (f : IntertwiningMap a b) (hf : R ≤ S.comap f.toLinearMap)

def quotientMap : IntertwiningMap (a.quotient R hr) (b.quotient S hs) where
  toLinearMap := R.mapQ S f.toLinearMap hf
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    obtain ⟨u, rfl⟩ := R.mkQ_surjective u
    change S.mkQ (f (a h u)) = S.mkQ (b h (f u))
    rw [IntertwiningMap.isIntertwining]

@[simp] theorem quotientMap_mk (u : U) :
    quotientMap a b R S hr hs f hf (R.mkQ u) = S.mkQ (f u) := rfl

def pull : RelationQuotient.vanishing b t S →ₗ[k] RelationQuotient.vanishing a t R where
  toFun q := ⟨q.val.comp f, fun u hu => q.property (hf hu)⟩
  map_add' q r := by apply Subtype.ext; ext u; rfl
  map_smul' z q := by apply Subtype.ext; ext u; rfl

theorem extraction (q : RelationQuotient.vanishing b t S) :
    RelationQuotient.equiv a t R hr (pull a b t R S f hf q) =
      (RelationQuotient.equiv b t S hs q).comp (quotientMap a b R S hr hs f hf) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u, rfl⟩ := R.mkQ_surjective u
  rfl

theorem reconstruction (q : IntertwiningMap (b.quotient S hs) t) :
    (RelationQuotient.equiv a t R hr).symm
      (q.comp (quotientMap a b R S hr hs f hf)) =
    pull a b t R S f hf ((RelationQuotient.equiv b t S hs).symm q) := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  rfl

theorem quotientMap_id :
    quotientMap a a R R hr hr (IntertwiningMap.id a) (by intro u hu; exact hu) =
      IntertwiningMap.id (a.quotient R hr) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u, rfl⟩ := R.mkQ_surjective u
  rfl

section Composition
variable {X : Type*} [AddCommGroup X] [Module k X]
  (c : Representation k H X) (T : Submodule k X)
  (ht : ∀ h, T ≤ T.comap (c h))
  (g : IntertwiningMap b c) (hg : S ≤ T.comap g.toLinearMap)

theorem quotientMap_comp :
    quotientMap a c R T hr ht (g.comp f) (by intro u hu; exact hg (hf hu)) =
      (quotientMap b c S T hs ht g hg).comp (quotientMap a b R S hr hs f hf) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u, rfl⟩ := R.mkQ_surjective u
  rfl
end Composition

def quotientEquiv (e : Representation.Equiv a b) (he : R.map e.toLinearMap = S) :
    Representation.Equiv (a.quotient R hr) (b.quotient S hs) where
  toLinearEquiv := Submodule.Quotient.equiv R S e.toLinearEquiv he
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    obtain ⟨u,rfl⟩ := R.mkQ_surjective u
    change S.mkQ (e (a h u)) = S.mkQ (b h (e u))
    exact congrArg S.mkQ (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap h u)

@[simp] theorem quotientEquiv_mk (e : Representation.Equiv a b)
    (he : R.map e.toLinearMap = S) (u : U) :
    quotientEquiv a b R S hr hs e he (R.mkQ u) = S.mkQ (e u) := rfl

/-- Change equal actions while keeping the functional definitionally unchanged. -/
def congrDirect {a' : Representation k H U} {t' : Representation k H W}
    (he : a = a') (ht : t = t') :
    RelationQuotient.vanishing a t R ≃ₗ[k] RelationQuotient.vanishing a' t' R where
  toFun q := ⟨{
    toLinearMap := q.val.toLinearMap
    isIntertwining' h := by rw [← he, ← ht]; exact q.val.isIntertwining' h }, q.property⟩
  invFun q := ⟨{
    toLinearMap := q.val.toLinearMap
    isIntertwining' h := by rw [he, ht]; exact q.val.isIntertwining' h }, q.property⟩
  left_inv _ := by apply Subtype.ext; apply IntertwiningMap.ext; rfl
  right_inv _ := by apply Subtype.ext; apply IntertwiningMap.ext; rfl
  map_add' _ _ := by apply Subtype.ext; apply IntertwiningMap.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; apply IntertwiningMap.ext; rfl

@[simp] theorem congrDirect_apply {a' : Representation k H U} {t' : Representation k H W}
    (he : a = a') (ht : t = t') (q : RelationQuotient.vanishing a t R) (u : U) :
    (congrDirect a t R he ht q).val u = q.val u := rfl
end
end Math.RelationQuotientNaturality

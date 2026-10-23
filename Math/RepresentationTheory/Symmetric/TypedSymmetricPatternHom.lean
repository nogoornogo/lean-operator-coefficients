import Math.RepresentationTheory.Symmetric.TypedPatternSymmetrization
import Math.RepresentationTheory.Exterior.FiniteSpeciesExterior
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

/-! Actual full symmetric species content, with arbitrary equivariant output.
The output may be a dual fermion carrier and need not be a scalar. -/
namespace Math.TypedSymmetricPatternHom
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior
variable {P G : Type*} [Fintype P] [DecidableEq P] [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {N : Type*} [AddCommGroup N] [Module ℂ N]
  (b : ∀ s, Representation ℂ G (V s)) (t : Representation ℂ G N)
  {m : ℕ} (pattern : Fin m → P)

abbrev Full := IntertwiningMap ((representation b).symmetricPower m) t

def Orbit (labels : Fin m → P) : Prop := ∃ p : Equiv.Perm (Fin m), labels ∘ p = pattern

def fullSpace : Submodule ℂ (Full b t (m := m)) where
  carrier := {f | ∀ labels, ¬ Orbit pattern labels → ∀ v : ∀ i, V (labels i),
    f (SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (v i))) = 0}
  zero_mem' := by intro labels hn v; rfl
  add_mem' := by intro f k hf hk labels hn v; change f _ + k _ = 0; rw [hf labels hn,hk labels hn,add_zero]
  smul_mem' := by intro z f hf labels hn v; change z • f _ = 0; rw [hf labels hn,smul_zero]

abbrev Raw := MultilinearMap ℂ (fun i => V (pattern i)) N

def orderedSpace : Submodule ℂ (Raw (V := V) (N := N) pattern) where
  carrier := {k | (∀ g v, k (fun i => b (pattern i) g (v i)) = t g (k v)) ∧
    TypedPatternSymmetrization.Compatible pattern k}
  zero_mem' := ⟨by intro g v; simp,by intro p hp w; rfl⟩
  add_mem' := by
    intro f k hf hk
    constructor
    · intro g v; change f _ + k _ = t g (f v + k v); rw [hf.1,hk.1,map_add]
    · intro p hp w; change TypedPatternSymmetrization.ordered pattern f (w ∘ p) +
        TypedPatternSymmetrization.ordered pattern k (w ∘ p) = _
      rw [hf.2 p hp,hk.2 p hp]; rfl
  smul_mem' := by
    intro z f hf
    constructor
    · intro g v; change z • f _ = t g (z • f v); rw [hf.1,map_smul]
    · intro p hp w; change z • TypedPatternSymmetrization.ordered pattern f (w ∘ p) = _
      rw [hf.2 p hp]; rfl

def restrict (f : Full b t (m := m)) : Raw (V := V) (N := N) pattern :=
  (f.toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ)).compLinearMap
    (fun i => LinearMap.single ℂ V (pattern i))

@[simp] theorem restrict_apply (f : Full b t (m := m)) (v : ∀ i, V (pattern i)) :
    restrict b t pattern f v = f (SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (v i))) := rfl

theorem restrict_invariant (f : Full b t (m := m)) (g : G) (v : ∀ i, V (pattern i)) :
    restrict b t pattern f (fun i => b (pattern i) g (v i)) = t g (restrict b t pattern f v) := by
  have he := IntertwiningMap.isIntertwining _ _ f g
    (SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (v i)))
  simpa only [restrict_apply,Representation.symmetricPower_apply_tprod,action_single] using he

theorem restrict_compatible (f : Full b t (m := m)) :
    TypedPatternSymmetrization.Compatible pattern (restrict b t pattern f) := by
  intro p hp w
  have hw : (fun i => Pi.single (pattern i) (w i (pattern i))) ∘ p =
      fun i => Pi.single (pattern i) (w (p i) (pattern i)) := by
    funext i
    have hi := congrFun hp i
    dsimp only [Function.comp_apply] at hi ⊢
    rw [hi]
  change f (SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (w (p i) (pattern i)))) =
    f (SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (w i (pattern i))))
  rw [← hw]
  exact congrArg f (SymmetricPower.tprod_equiv p (fun i => Pi.single (pattern i) (w i (pattern i))))

def assemble (k : orderedSpace b t pattern) : Full b t (m := m) where
  toLinearMap := SymmetricPowerDescent.lift m (TypedPatternSymmetrization.symmetric pattern k.val)
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro w
    change SymmetricPowerDescent.lift m (TypedPatternSymmetrization.symmetric pattern k.val)
      (((representation b).symmetricPower m) g (SymmetricPower.tprod ℂ w)) =
      t g (SymmetricPowerDescent.lift m (TypedPatternSymmetrization.symmetric pattern k.val)
        (SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod,SymmetricPowerDescent.lift_tprod,
      SymmetricPowerDescent.lift_tprod]
    simp only [TypedPatternSymmetrization.symmetric,smul_apply,sum_apply,
      MultilinearMap.domDomCongrLinearEquiv_apply,TypedPatternSymmetrization.ordered,
      TypedPatternAlternation.ordered,
      map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    exact k.property.1 g (fun i => w (p i) (pattern i))

theorem assemble_pure (k : orderedSpace b t pattern) (v : ∀ i, V (pattern i)) :
    assemble b t pattern k (SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (v i))) = k.val v := by
  exact (SymmetricPowerDescent.lift_tprod _ _ _).trans
    (TypedPatternSymmetrization.symmetric_pure pattern k.val k.property.2 v)

theorem assemble_mem (k : orderedSpace b t pattern) : assemble b t pattern k ∈ fullSpace b t pattern := by
  intro labels hn v
  exact (SymmetricPowerDescent.lift_tprod _ _ _).trans
    (TypedPatternSymmetrization.symmetric_vanish pattern k.val labels v hn)

theorem pure_ext (f k : Full b t (m := m))
    (he : ∀ (labels : Fin m → P) (v : ∀ i, V (labels i)),
      f (SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (v i))) =
        k (SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (v i)))) : f=k := by
  apply IntertwiningMap.ext
  apply SymmetricPower.ext
  intro w
  change f (SymmetricPower.tprod ℂ w) = k (SymmetricPower.tprod ℂ w)
  have expand (q : Full b t (m := m)) : q (SymmetricPower.tprod ℂ w) =
      ∑ labels : Fin m → P, q (SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (w i (labels i)))) := by
    calc
      _ = (q.toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ))
          (fun i => ∑ s, Pi.single s (w i s)) := by simp only [LinearMap.sum_single_apply]; rfl
      _ = _ := (q.toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ)).map_sum _
  rw [expand f,expand k]
  exact Finset.sum_congr rfl (fun labels _ => he labels (fun i => w i (labels i)))

omit [Fintype P] [∀ s, Module ℂ (V s)] in
private theorem single_eta (u s : P) (v : V u) (he : u=s) :
    Pi.single s ((Pi.single u v) s) = Pi.single u v := by cases he; simp

theorem family_ext (f k : fullSpace b t pattern)
    (he : restrict b t pattern f.val = restrict b t pattern k.val) : f=k := by
  apply Subtype.ext
  apply pure_ext b t
  intro labels v
  by_cases ho : Orbit pattern labels
  · obtain ⟨p,hp⟩ := ho
    let w := fun i => Pi.single (labels i) (v i)
    let vv := fun i => w (p i) (pattern i)
    have hw : (fun i => Pi.single (pattern i) (vv i)) = w ∘ p := by
      funext i
      exact single_eta (labels (p i)) (pattern i) (v (p i)) (congrFun hp i)
    have hc := DFunLike.congr_fun he vv
    rw [restrict_apply,restrict_apply,hw] at hc
    have ht := SymmetricPower.tprod_equiv (R := ℂ) p w
    exact (congrArg f.val ht).symm.trans (hc.trans (congrArg k.val ht))
  · rw [f.property labels ho,k.property labels ho]

def equiv : fullSpace b t pattern ≃ₗ[ℂ] orderedSpace b t pattern where
  toFun f := ⟨restrict b t pattern f.val,restrict_invariant b t pattern f.val,restrict_compatible b t pattern f.val⟩
  invFun k := ⟨assemble b t pattern k,assemble_mem b t pattern k⟩
  left_inv f := by
    apply family_ext b t pattern
    ext v
    exact assemble_pure b t pattern _ v
  right_inv k := by
    apply Subtype.ext
    ext v
    exact assemble_pure b t pattern k v
  map_add' f k := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

section Source
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (a : Representation ℂ G X)

/-- Full scalar coefficients, with the source statistics already imposed. -/
def sourceCurry : InvariantCoefficientTransport.Invariants
    (a.tprod ((representation b).symmetricPower m)) ≃ₗ[ℂ]
      Full b a.dual (m := m) :=
  (InvariantCoefficientTransport.alongEquiv
    (Representation.TensorProduct.comm a ((representation b).symmetricPower m))).trans
      (InvariantTensorCurry.equiv ((representation b).symmetricPower m) a)

def sourceSpace : Submodule ℂ (InvariantCoefficientTransport.Invariants
    (a.tprod ((representation b).symmetricPower m))) :=
  (fullSpace b a.dual pattern).comap (sourceCurry b a).toLinearMap

def sourceEquiv : sourceSpace b pattern a ≃ₗ[ℂ] orderedSpace b a.dual pattern :=
  (LinearEquiv.ofSubmodule' (sourceCurry b a) (fullSpace b a.dual pattern)).trans
    (equiv b a.dual pattern)

@[simp] theorem sourceEquiv_apply (f : sourceSpace b pattern a)
    (v : ∀ i, V (pattern i)) (x : X) :
    (sourceEquiv b pattern a f).val v x =
      f.val (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => Pi.single (pattern i) (v i))) := rfl

theorem sourceSpace_iff (f : InvariantCoefficientTransport.Invariants
    (a.tprod ((representation b).symmetricPower m))) :
    f ∈ sourceSpace b pattern a ↔
      ∀ labels, ¬ Orbit pattern labels → ∀ (v : ∀ i, V (labels i)) (x : X),
        f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (v i))) = 0 := by
  constructor
  · intro hf labels hn v x
    exact DFunLike.congr_fun (hf labels hn v) x
  · intro hf labels hn v
    ext x
    exact hf labels hn v x
end Source

end
end Math.TypedSymmetricPatternHom

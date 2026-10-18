import Math.RepresentationTheory.TwoSpeciesSymmetricDescent

/-! Exact fixed-content full/split coefficient bridge with actual group covariance. -/
namespace Math.TwoSpeciesCoefficientBridge
set_option autoImplicit false
noncomputable section
open Representation TwoSpeciesPattern TwoSpeciesSymmetricDescent FiniteSpeciesExterior
open scoped TensorProduct
variable {G : Type*} [Group G]
  {V : Fin 2 → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {N : Type*} [AddCommGroup N] [Module ℂ N]
  (b : ∀ s, Representation ℂ G (V s)) (t : Representation ℂ G N)

abbrev Split (h d : ℕ) := (b 0).symmetricPower h |>.tprod ((b 1).symmetricPower d)
abbrev Space (h d : ℕ) := IntertwiningMap (Split b h d) t

theorem joined_ordered (h d : ℕ) (f : Sym[ℂ]^h (V 0) ⊗[ℂ] Sym[ℂ]^d (V 1) →ₗ[ℂ] N)
    (w : Fin (h+d) → ∀ s, V s) :
    TypedPatternSymmetrization.ordered (pattern h d) (linearJoin h d f).val w =
      f (SymmetricPower.tprod ℂ (fun i => w (left i) 0) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun j => w (right j) 1)) := by
  rw [← ordered_apply,linearJoin_apply]

def toOrdered (h d : ℕ) (f : Space b t h d) : TypedSymmetricPatternHom.orderedSpace b t (pattern h d) :=
  ⟨(linearJoin h d f.toLinearMap).val,by
    constructor
    · intro g v
      have ho (w : Fin (h+d) → ∀ s, V s) :
          TypedPatternSymmetrization.ordered (pattern h d) (linearJoin h d f.toLinearMap).val
            (fun i => representation b g (w i)) =
          t g (TypedPatternSymmetrization.ordered (pattern h d) (linearJoin h d f.toLinearMap).val w) := by
        rw [joined_ordered,joined_ordered]
        have he := f.isIntertwining _ _ g
          (SymmetricPower.tprod ℂ (fun i => w (left i) 0) ⊗ₜ[ℂ]
            SymmetricPower.tprod ℂ (fun j => w (right j) 1))
        simpa only [Split,Representation.tprod_apply,TensorProduct.map_tmul,
          Representation.symmetricPower_apply_tprod,representation_apply,IntertwiningMap.coe_toLinearMap] using he
      have he := ho (fun i => Pi.single (pattern h d i) (v i))
      change (linearJoin h d f.toLinearMap).val
        (fun i => (representation b g (Pi.single (pattern h d i) (v i))) (pattern h d i)) =
        t g ((linearJoin h d f.toLinearMap).val (fun i => (Pi.single (pattern h d i) (v i)) (pattern h d i))) at he
      simpa only [action_single,Pi.single_eq_same] using he
    · exact (mem_compatibleSpace h d _).mp (linearJoin h d f.toLinearMap).property⟩

theorem ordered_invariant (h d : ℕ)
    (k : TypedSymmetricPatternHom.orderedSpace b t (pattern h d)) (g : G)
    (w : Fin (h+d) → ∀ s, V s) :
    TypedPatternSymmetrization.ordered (pattern h d) k.val (fun i => representation b g (w i)) =
      t g (TypedPatternSymmetrization.ordered (pattern h d) k.val w) :=
  k.property.1 g (fun i => w i (pattern h d i))

theorem inverse_pure (h d : ℕ) (k : compatibleSpace (V := V) (N := N) h d)
    (v : Fin h → V 0) (w : Fin d → V 1) :
    (linearJoin h d).symm k (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) =
      rawEquiv h d k.val v w := by
  have he := congrArg (fun z : compatibleSpace (V := V) (N := N) h d => rawEquiv h d z.val v w)
    ((linearJoin h d).apply_symm_apply k)
  rw [linearJoin_apply] at he
  exact he

def fromOrdered (h d : ℕ) (k : TypedSymmetricPatternHom.orderedSpace b t (pattern h d)) : Space b t h d where
  toLinearMap := (linearJoin h d).symm ⟨k.val,(mem_compatibleSpace h d k.val).mpr k.property.2⟩
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin h) (V 0))
    rintro _ ⟨v,rfl⟩
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin d) (V 1))
    rintro _ ⟨w,rfl⟩
    change (linearJoin h d).symm _
      ((b 0).symmetricPower h g (SymmetricPower.tprod ℂ v) ⊗ₜ[ℂ]
        (b 1).symmetricPower d g (SymmetricPower.tprod ℂ w)) =
      t g ((linearJoin h d).symm _ (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod,
      inverse_pure,inverse_pure]
    have he := ordered_invariant b t h d k g (pack v w)
    rw [← ordered_apply,← ordered_apply] at he
    simpa only [representation_apply,pack_left,pack_right] using he

def orderedEquiv (h d : ℕ) : Space b t h d ≃ₗ[ℂ] TypedSymmetricPatternHom.orderedSpace b t (pattern h d) where
  toFun := toOrdered b t h d
  invFun := fromOrdered b t h d
  left_inv f := by
    apply IntertwiningMap.ext
    exact (linearJoin h d).symm_apply_apply f.toLinearMap
  right_inv k := by
    apply Subtype.ext
    exact congrArg (fun z : compatibleSpace (V := V) (N := N) h d => z.val) ((linearJoin h d).apply_symm_apply
      ⟨k.val,(mem_compatibleSpace h d k.val).mpr k.property.2⟩)
  map_add' f k := by apply Subtype.ext; exact congrArg (fun z : compatibleSpace (V := V) (N := N) h d => z.val) ((linearJoin h d).map_add _ _)
  map_smul' z f := by apply Subtype.ext; exact congrArg (fun z : compatibleSpace (V := V) (N := N) h d => z.val) ((linearJoin h d).map_smul z _)

def fullEquiv (h d : ℕ) : TypedSymmetricPatternHom.fullSpace b t (pattern h d) ≃ₗ[ℂ] Space b t h d :=
  (TypedSymmetricPatternHom.equiv b t (pattern h d)).trans (orderedEquiv b t h d).symm

section Source
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (a : Representation ℂ G X)

def sourceEquiv (h d : ℕ) : TypedSymmetricPatternHom.sourceSpace b (pattern h d) a ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants (a.tprod (Split b h d)) :=
  (TypedSymmetricPatternHom.sourceEquiv b (pattern h d) a).trans
    (((orderedEquiv b a.dual h d).symm.trans (InvariantTensorCurry.equiv (Split b h d) a).symm).trans
      (InvariantCoefficientTransport.alongEquiv (Representation.TensorProduct.comm (Split b h d) a)))
end Source

end
end Math.TwoSpeciesCoefficientBridge

import Math.RepresentationTheory.MixedWeightSupport
import Math.RepresentationTheory.InvariantCoefficientTransport

/-! Independent exterior/one-boson coefficients are exactly alternating
fermion maps with a linear boson spectator. Both inverse identities are proved. -/
namespace Math.MixedSingleBosonDescent
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] (n : ℕ)

abbrev Domain := (⋀[ℂ]^n A) ⊗[ℂ] (Sym[ℂ]^1 B)
abbrev Ordered := A [⋀^Fin n]→ₗ[ℂ] (B →ₗ[ℂ] ℂ)

def orderedEquiv : (Domain (A := A) (B := B) n →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
    Ordered (A := A) (B := B) n :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (⋀[ℂ]^n A) (Sym[ℂ]^1 B) ℂ).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (⋀[ℂ]^n A))
      (LinearEquiv.arrowCongr SymmetricPowerLowDegree.oneEquiv (LinearEquiv.refl ℂ ℂ))).trans
        exteriorPower.alternatingMapLinearEquiv.symm)

@[simp] theorem orderedEquiv_apply (f : Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (v : Fin n → A) (w : B) : orderedEquiv n f v w =
      f (MixedWeightSupport.pure v (fun _ : Fin 1 => w)) := rfl

@[simp] theorem lift_apply (f : Ordered (A := A) (B := B) n)
    (v : Fin n → A) (w : B) :
    (orderedEquiv n).symm f (MixedWeightSupport.pure v (fun _ : Fin 1 => w)) = f v w := by
  simpa only [orderedEquiv_apply] using congrArg
    (fun k : Ordered (A := A) (B := B) n => k v w) ((orderedEquiv n).apply_symm_apply f)

variable {G : Type*} [Group G]
  (a : Representation ℂ G A) (b : Representation ℂ G B)

def equivariantOrdered : Submodule ℂ (Ordered (A := A) (B := B) n) where
  carrier := {f | ∀ g v w, f (a g ∘ v) (b g w) = f v w}
  zero_mem' := by intro g v w; rfl
  add_mem' := by
    intro f h hf hh g v w
    change f _ _ + h _ _ = f v w + h v w
    rw [hf, hh]
  smul_mem' := by
    intro z f hf g v w
    change z * f _ _ = z * f v w
    rw [hf]

def descend (f : equivariantOrdered n a b) : MixedWeightSupport.Coefficient a b (n := n) (m := 1) where
  toLinearMap := (orderedEquiv n).symm f.val
  isIntertwining' g := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 1) B)
    rintro _ ⟨w, rfl⟩
    have hw : w = fun _ => w 0 := funext (fun i => congrArg w (Subsingleton.elim i 0))
    rw [hw]
    change (orderedEquiv n).symm f.val
      ((a.exteriorPower n g (exteriorPower.ιMulti ℂ n v)) ⊗ₜ[ℂ]
        (b.symmetricPower 1 g (SymmetricPower.tprod ℂ (fun _ => w 0)))) =
      (orderedEquiv n).symm f.val (MixedWeightSupport.pure v (fun _ => w 0))
    rw [Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod]
    exact (lift_apply n f.val _ _).trans ((f.property g v (w 0)).trans (lift_apply n f.val v _).symm)

def extract (f : MixedWeightSupport.Coefficient a b (n := n) (m := 1)) : equivariantOrdered n a b :=
  ⟨orderedEquiv n f.toLinearMap, by
    intro g v w
    have h := Representation.IntertwiningMap.isIntertwining _ _ f g
      (MixedWeightSupport.pure v (fun _ : Fin 1 => w))
    simp only [orderedEquiv_apply]
    change f (MixedWeightSupport.pure (a g ∘ v) (fun _ : Fin 1 => b g w)) =
      f (MixedWeightSupport.pure v (fun _ : Fin 1 => w))
    simpa only [MixedWeightSupport.pure, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, Representation.trivial_apply,
      Function.comp_def] using h⟩

def equiv : MixedWeightSupport.Coefficient a b (n := n) (m := 1) ≃ₗ[ℂ] equivariantOrdered n a b where
  toFun := extract n a b
  invFun := descend n a b
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact (orderedEquiv n).symm_apply_apply f.toLinearMap
  right_inv f := by
    apply Subtype.ext
    exact (orderedEquiv n).apply_symm_apply f.val
  map_add' f h := by apply Subtype.ext; exact (orderedEquiv n).map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (orderedEquiv n).map_smul z _

end
end Math.MixedSingleBosonDescent

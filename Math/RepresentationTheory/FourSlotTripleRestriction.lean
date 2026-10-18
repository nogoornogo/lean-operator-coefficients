import Math.RepresentationTheory.FourSlotTripleSector
import Math.RepresentationTheory.FourTensorMultilinear

/-! Restriction and reconstruction of the intrinsic degree-(3,1) sector. -/
namespace Math.FourSlotTripleRestriction
set_option autoImplicit false
noncomputable section
open Representation FourSlotTripleAlternation FourSlotTripleSector
open scoped TensorProduct
variable {H A B : Type*} [Group H] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

def linearRestriction (f : Coefficient a b) : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ :=
  (FourTensorMultilinear.lift (evaluation a b f).toMultilinearMap).comp
    (TensorProduct.map (TensorProduct.map (LinearMap.inl ℂ A B) (LinearMap.inl ℂ A B))
      (TensorProduct.map (LinearMap.inl ℂ A B) (LinearMap.inr ℂ A B)))

theorem linearRestriction_apply (f : Coefficient a b) (x y z : A) (h : B) :
    linearRestriction a b f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) =
      f (exteriorPower.ιMulti ℂ 4 (slots x y z h)) := by
  exact FourTensorMultilinear.lift_tprod (evaluation a b f).toMultilinearMap (slots x y z h)

def restriction (f : Coefficient a b) :
    IntertwiningMap ((a.tprod a).tprod (a.tprod b)) (Representation.trivial ℂ H ℂ) where
  toLinearMap := linearRestriction a b f
  isIntertwining' g := by
    ext x y z h
    change linearRestriction a b f ((a g x ⊗ₜ[ℂ] a g y) ⊗ₜ[ℂ] (a g z ⊗ₜ[ℂ] b g h)) =
      linearRestriction a b f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
    rw [linearRestriction_apply, linearRestriction_apply]
    have hi := IntertwiningMap.isIntertwining _ _ f g (exteriorPower.ιMulti ℂ 4 (slots x y z h))
    rw [Representation.exteriorPower_apply_ιMulti] at hi
    simp only [Representation.trivial_apply] at hi
    convert hi using 1
    congr 2
    funext i
    fin_cases i <;> simp [slots]

theorem restriction_alternates (f : Coefficient a b) : Alternates (linearRestriction a b f) := by
  intro p hp x y z h
  have hn (i : Fin 4) (hi : i ≠ 3) : p i ≠ 3 := by
    intro he
    exact hi (p.injective (he.trans hp.symm))
  have hv : slots (slots x y z h (p 0)).1 (slots x y z h (p 1)).1
      (slots x y z h (p 2)).1 (slots x y z h (p 3)).2 = slots x y z h ∘ p := by
    have hz (i : Fin 4) (hi : i ≠ 3) : (slots x y z h i).2 = 0 := by
      fin_cases i <;> simp_all [slots]
    funext i
    fin_cases i
    · apply Prod.ext
      · rfl
      · exact (hz _ (hn 0 (by decide))).symm
    · apply Prod.ext
      · rfl
      · exact (hz _ (hn 1 (by decide))).symm
    · apply Prod.ext
      · rfl
      · exact (hz _ (hn 2 (by decide))).symm
    · simp [slots, hp]
  change linearRestriction a b f
    (((slots x y z h (p 0)).1 ⊗ₜ[ℂ] (slots x y z h (p 1)).1) ⊗ₜ[ℂ]
      ((slots x y z h (p 2)).1 ⊗ₜ[ℂ] (slots x y z h (p 3)).2)) = _
  rw [linearRestriction_apply, linearRestriction_apply, hv]
  exact (evaluation a b f).map_perm (slots x y z h) p

theorem reconstruct (f : Coefficient a b) (hf : HasDegree a b f) :
    coefficient a b ((1/6 : ℂ) • restriction a b f) = f := by
  apply slots_ext a b _ f (coefficient_hasDegree a b _) hf
  intro x y z h
  have hs : Alternates (((1/6 : ℂ) • restriction a b f).toLinearMap) := by
    intro p hp x y z h
    rw [IntertwiningMap.toLinearMap_smul]
    change (1/6 : ℂ) • ordered (linearRestriction a b f) (slots x y z h ∘ p) = _
    rw [restriction_alternates a b f p hp]
    exact smul_comm _ _ _
  rw [coefficient_slots a b _ hs]
  rw [IntertwiningMap.smul_apply]
  change (6 : ℂ) * ((1/6 : ℂ) * linearRestriction a b f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))) = _
  rw [linearRestriction_apply]
  ring

def orderedSector : Submodule ℂ
    (IntertwiningMap ((a.tprod a).tprod (a.tprod b)) (Representation.trivial ℂ H ℂ)) where
  carrier := {f | Alternates f.toLinearMap}
  zero_mem' := by intro p hp x y z h; simp [ordered]
  add_mem' := by
    intro f g hf hg p hp x y z h
    change ordered f.toLinearMap _ + ordered g.toLinearMap _ =
      Equiv.Perm.sign p • (f _ + g _)
    rw [hf p hp, hg p hp, smul_add]
    rfl
  smul_mem' := by
    intro c f hf p hp x y z h
    rw [IntertwiningMap.toLinearMap_smul]
    change c • ordered f.toLinearMap _ = Equiv.Perm.sign p • (c • f _)
    rw [hf p hp]
    exact smul_comm _ _ _

/-- Full restriction/descent equivalence for the independently defined (3,1) sector. -/
def equiv : sector a b ≃ₗ[ℂ] orderedSector a b where
  toFun f := ⟨restriction a b f.val, restriction_alternates a b f.val⟩
  invFun f := ⟨coefficient a b ((1/6 : ℂ) • f.val), coefficient_hasDegree a b _⟩
  left_inv f := by apply Subtype.ext; exact reconstruct a b f.val f.property
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    change linearRestriction a b (coefficient a b ((1/6 : ℂ) • f.val)) = f.val.toLinearMap
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    apply TensorProduct.ext
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro h
    change linearRestriction a b (coefficient a b ((1/6 : ℂ) • f.val))
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) = f.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
    rw [linearRestriction_apply]
    have hs : Alternates (((1/6 : ℂ) • f.val).toLinearMap) :=
      (orderedSector a b).smul_mem _ f.property
    rw [coefficient_slots a b _ hs, IntertwiningMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  map_add' f g := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    change linearRestriction a b (f.val + g.val) = linearRestriction a b f.val + linearRestriction a b g.val
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    apply TensorProduct.ext
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro h
    change linearRestriction a b (f.val + g.val) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) =
      linearRestriction a b f.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) +
      linearRestriction a b g.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
    rw [linearRestriction_apply, linearRestriction_apply, linearRestriction_apply]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    change linearRestriction a b (c • f.val) = c • linearRestriction a b f.val
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    apply TensorProduct.ext
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro h
    change linearRestriction a b (c • f.val) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) =
      c • linearRestriction a b f.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
    rw [linearRestriction_apply, linearRestriction_apply]
    rfl

end
end Math.FourSlotTripleRestriction

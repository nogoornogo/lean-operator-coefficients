import Math.RepresentationTheory.Color.Diagrams.ColorTensorTree
import Math.RepresentationTheory.Invariants.InvariantSpanningRestriction

/-! Canonical color diagrams on actual binary raw sources. Owner predicates
decide their incident-flag evaluations in both orientations. -/
namespace Math.ColorTreeDiagrams
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree SU3DefiningExterior ExternalInvariantTensor
open scoped TensorProduct

def positiveOwner (w : Shape) (k : ℕ) (h : positive w = negative w+3*k) :
    Fin (negative w+3*k) → Leaf w := fun i => ColorTensorTree.positiveOwner w (Fin.cast h.symm i)

def negativeOwner (w : Shape) (k : ℕ) (h : negative w = positive w+3*k) :
    Fin (positive w+3*k) → Leaf w := fun i => ColorTensorTree.negativeOwner w (Fin.cast h.symm i)

def positiveEquiv (w : Shape) (k : ℕ) (h : positive w = negative w+3*k) :
    Representation.Equiv (action w) (SU3TensorPositive.mixed (negative w+3*k) (negative w)) :=
  (flatten w).trans (tensorEquiv (TensorVolumeSplit.powerCast rho h)
    (.refl (rho.dual.tensorPower (negative w))))

def negativeEquiv (w : Shape) (k : ℕ) (h : negative w = positive w+3*k) :
    Representation.Equiv (action w) (SU3TensorPositive.mixed (positive w) (positive w+3*k)) :=
  (flatten w).trans (tensorEquiv (.refl (rho.tensorPower (positive w)))
    (TensorVolumeSplit.powerCast rho.dual h))

def positiveContraction (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) : InvariantCoefficientTransport.Invariants (action w) :=
  (SU3VolumeContractions.contraction (negative w) k sigma).comp (positiveEquiv w k h).toIntertwiningMap

def negativeContraction (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) : InvariantCoefficientTransport.Invariants (action w) :=
  (SU3MixedContractionSpan.dualContraction (positive w) k sigma).comp (negativeEquiv w k h).toIntertwiningMap

def PositiveValid (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) : Prop :=
  (∀ i : Fin (negative w), ColorTensorTree.negativeOwner w i ≠
    positiveOwner w k h (sigma.symm (Fin.castAdd (3*k) i))) ∧
  (∀ a : Fin k, Function.Injective
    (SU3ContractionDiagram.triples (negative w) k (positiveOwner w k h) sigma a))

def NegativeValid (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) : Prop :=
  (∀ i : Fin (positive w), negativeOwner w k h (sigma.symm (Fin.castAdd (3*k) i)) ≠
    ColorTensorTree.positiveOwner w i) ∧
  (∀ a : Fin k, Function.Injective
    (SU3DualContractionDiagram.triples (positive w) k (negativeOwner w k h) sigma a))

theorem positive_fields (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k)))
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :
    positiveContraction w k h sigma (fields w v f) =
      SU3VolumeContractions.contraction (negative w) k sigma
        (PiTensorProduct.tprod ℂ (fun i => v (positiveOwner w k h i)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun i => f (ColorTensorTree.negativeOwner w i))) := by
  change SU3VolumeContractions.contraction (negative w) k sigma
    (TensorProduct.map (TensorVolumeSplit.powerCast rho h).toLinearEquiv.toLinearMap LinearMap.id
      (flatten w (fields w v f))) = _
  rw [flatten_fields,TensorProduct.map_tmul]
  change SU3VolumeContractions.contraction (negative w) k sigma
    (TensorVolumeSplit.powerCast rho h (PiTensorProduct.tprod ℂ (fun i => v (ColorTensorTree.positiveOwner w i))) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun i => f (ColorTensorTree.negativeOwner w i))) = _
  rw [TensorVolumeSplit.powerCast_tprod]
  rfl

theorem negative_fields (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k)))
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :
    negativeContraction w k h sigma (fields w v f) =
      SU3MixedContractionSpan.dualContraction (positive w) k sigma
        (PiTensorProduct.tprod ℂ (fun i => v (ColorTensorTree.positiveOwner w i)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun i => f (negativeOwner w k h i))) := by
  change SU3MixedContractionSpan.dualContraction (positive w) k sigma
    (TensorProduct.map LinearMap.id (TensorVolumeSplit.powerCast rho.dual h).toLinearEquiv.toLinearMap
      (flatten w (fields w v f))) = _
  rw [flatten_fields,TensorProduct.map_tmul]
  change SU3MixedContractionSpan.dualContraction (positive w) k sigma
    (PiTensorProduct.tprod ℂ (fun i => v (ColorTensorTree.positiveOwner w i)) ⊗ₜ[ℂ]
      TensorVolumeSplit.powerCast rho.dual h
        (PiTensorProduct.tprod ℂ (fun i => f (ColorTensorTree.negativeOwner w i)))) = _
  rw [TensorVolumeSplit.powerCast_tprod]
  rfl

def flags (w : Shape) (a : Leaf w × Fin 3 → ℂ) : Carrier w :=
  fields w (ColorFlagNonvanishing.vector a) (ColorFlagNonvanishing.functional a)

theorem positive_flag_iff (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) :
    (∃ a : Leaf w × Fin 3 → ℂ, positiveContraction w k h sigma (flags w a) ≠ 0) ↔
      PositiveValid w k h sigma := by
  simp only [flags,positive_fields]
  exact SU3ContractionDiagram.flag_nonzero_iff (negative w) k
    (positiveOwner w k h) (ColorTensorTree.negativeOwner w) sigma

theorem negative_flag_iff (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) :
    (∃ a : Leaf w × Fin 3 → ℂ, negativeContraction w k h sigma (flags w a) ≠ 0) ↔
      NegativeValid w k h sigma := by
  simp only [flags,negative_fields]
  exact SU3DualContractionDiagram.flag_nonzero_iff (positive w) k
    (ColorTensorTree.positiveOwner w) (negativeOwner w k h) sigma

theorem positive_spanning (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (f : InvariantCoefficientTransport.Invariants (action w)) :
    ∃ c : Equiv.Perm (Fin (negative w+3*k)) → ℂ,
      f = ∑ sigma, c sigma • positiveContraction w k h sigma := by
  obtain ⟨c,hc⟩ := SU3VolumeContractions.spanning (negative w) k
    (f.comp (positiveEquiv w k h).symm.toIntertwiningMap)
  refine ⟨c,?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f x = (∑ sigma, c sigma • positiveContraction w k h sigma) x
  have he := DFunLike.congr_fun hc (positiveEquiv w k h x)
  change f ((positiveEquiv w k h).symm (positiveEquiv w k h x)) = _ at he
  rw [Representation.Equiv.symm_apply_apply] at he
  simp only [IntertwiningMap.sum_apply,IntertwiningMap.smul_apply] at he ⊢
  exact he

theorem negative_spanning (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (f : InvariantCoefficientTransport.Invariants (action w)) :
    ∃ c : Equiv.Perm (Fin (positive w+3*k)) → ℂ,
      f = ∑ sigma, c sigma • negativeContraction w k h sigma := by
  obtain ⟨c,hc⟩ := SU3MixedContractionSpan.dual_spanning (positive w) k
    (f.comp (negativeEquiv w k h).symm.toIntertwiningMap)
  refine ⟨c,?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f x = (∑ sigma, c sigma • negativeContraction w k h sigma) x
  have he := DFunLike.congr_fun hc (negativeEquiv w k h x)
  change f ((negativeEquiv w k h).symm (negativeEquiv w k h x)) = _ at he
  rw [Representation.Equiv.symm_apply_apply] at he
  simp only [IntertwiningMap.sum_apply,IntertwiningMap.smul_apply] at he ⊢
  exact he

end
end Math.ColorTreeDiagrams

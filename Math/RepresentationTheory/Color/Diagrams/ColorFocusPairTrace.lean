import Math.RepresentationTheory.Color.Diagrams.ColorTensorFocus
import Math.RepresentationTheory.Color.Diagrams.ColorContractionPairFactor
import Math.RepresentationTheory.Symmetric.SymmetricTraceFactor
import Math.LinearAlgebra.Tensor.TensorSlotInsertion

/-! An internal evaluation pair in a canonical color diagram factors through
the actual trace of its selected symmetric leaf. -/
namespace Math.ColorFocusPairTrace
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree ColorTensorFocus SU3DefiningExterior
open scoped TensorProduct

def degreeFocus (w : Shape) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :
    SymmetricTensorTrace.Raw (V := Vector) (1+p) (1+q) →ₗ[ℂ] ColorTensorTree.Carrier w :=
  (focus w i v f).comp (TensorProduct.map
    (TensorVolumeSplit.powerCast rho hp.symm).toLinearEquiv.toLinearMap
    (TensorVolumeSplit.powerCast rho.dual hq.symm).toLinearEquiv.toLinearMap)

theorem degreeFocus_tprod (w : Shape) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (x : Fin (1+p) → Vector) (y : Fin (1+q) → Module.Dual ℂ Vector) :
    flatten w (degreeFocus w i p q hp hq v f
      (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      PiTensorProduct.tprod ℂ (positiveSubstitute w i (fun j => x (Fin.cast hp j)) v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (negativeSubstitute w i (fun j => y (Fin.cast hq j)) f) := by
  change flatten w (focus w i v f
    (TensorVolumeSplit.powerCast rho hp.symm (PiTensorProduct.tprod ℂ x) ⊗ₜ[ℂ]
      TensorVolumeSplit.powerCast rho.dual hq.symm (PiTensorProduct.tprod ℂ y))) = _
  rw [TensorVolumeSplit.powerCast_tprod,TensorVolumeSplit.powerCast_tprod]
  exact flatten_focus w i v f _ _

theorem cast_update {A : Type*} {p q : ℕ} (h : p = q) (x : A) (j : Fin q) (e : A) :
    (fun a => Function.update (fun _ : Fin q => x) j e (Fin.cast h a)) =
      Function.update (fun _ : Fin p => x) (Fin.cast h.symm j) e := by
  classical
  exact Function.update_comp_equiv (fun _ => x) (finCongr h) j e

theorem positive_focus (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (x : Fin (1+p) → Vector) (y : Fin (1+q) → Module.Dual ℂ Vector) :
    ColorTreeDiagrams.positiveContraction w k h sigma
      (degreeFocus w i p q hp hq v f (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      SU3VolumeContractions.contraction (negative w) k sigma
        (PiTensorProduct.tprod ℂ (fun j =>
          positiveSubstitute w i (fun a => x (Fin.cast hp a)) v (Fin.cast h.symm j)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (negativeSubstitute w i (fun a => y (Fin.cast hq a)) f)) := by
  change SU3VolumeContractions.contraction (negative w) k sigma
    (TensorProduct.map (TensorVolumeSplit.powerCast rho h).toLinearEquiv.toLinearMap LinearMap.id
      (flatten w (degreeFocus w i p q hp hq v f _))) = _
  rw [degreeFocus_tprod,TensorProduct.map_tmul]
  change SU3VolumeContractions.contraction (negative w) k sigma
    (TensorVolumeSplit.powerCast rho h _ ⊗ₜ[ℂ] _) = _
  rw [TensorVolumeSplit.powerCast_tprod]
  rfl

def positiveForm (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :=
  (ColorTreeDiagrams.positiveContraction w k h sigma).toLinearMap.comp
    (degreeFocus w i p q hp hq v f)

theorem positive_factor (w : Shape) (k : ℕ) (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (a : Fin (1+p)) (b : Fin (1+q)) (s : Fin (negative w))
    (ha : Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s)) =
      positiveIndex w i (Fin.cast hp.symm a))
    (hb : s = negativeIndex w i (Fin.cast hq.symm b))
    (e : Vector) (epsilon : Module.Dual ℂ Vector) (he : epsilon e = 1) :
    (positiveForm w k h sigma i p q hp hq v f).comp
        (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) =
      (((positiveForm w k h sigma i p q hp hq v f).comp
        (TensorProduct.map (TensorSlotInsertion.insert p a e) (TensorSlotInsertion.insert q b epsilon))).comp
          (SymmetricTensorTrace.rawTrace p q)).comp
            (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) := by
  classical
  apply SymmetricTraceFactor.factor
  intro x y
  change ColorTreeDiagrams.positiveContraction w k h sigma
    (degreeFocus w i p q hp hq v f _) = y x •
      ColorTreeDiagrams.positiveContraction w k h sigma
        (degreeFocus w i p q hp hq v f (TensorProduct.map _ _ _))
  rw [TensorProduct.map_tmul,TensorSlotInsertion.pure,TensorSlotInsertion.pure,
    positive_focus,positive_focus,cast_update,cast_update,
    positiveSubstitute_update,negativeSubstitute_update]
  have hv : (fun j => Function.update (positiveSubstitute w i (fun _ => x) v)
      (positiveIndex w i (Fin.cast hp.symm a)) e (Fin.cast h.symm j)) =
      Function.update (fun j => positiveSubstitute w i (fun _ => x) v (Fin.cast h.symm j))
        (sigma.symm (Fin.castAdd (3*k) s)) e := by
    rw [← ha]
    exact Function.update_comp_eq_of_injective _ (finCongr h.symm).injective _ _
  rw [hv,← hb]
  have hx := ColorContractionPairFactor.positive (negative w) k sigma s
    (fun j => positiveSubstitute w i (fun _ => x) v (Fin.cast h.symm j))
    (negativeSubstitute w i (fun _ => y) f) e epsilon he
  rw [ha,hb,positiveSubstitute_index,negativeSubstitute_index] at hx
  simpa only [hb,smul_eq_mul] using hx

theorem negative_focus (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (x : Fin (1+p) → Vector) (y : Fin (1+q) → Module.Dual ℂ Vector) :
    ColorTreeDiagrams.negativeContraction w k h sigma
      (degreeFocus w i p q hp hq v f (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      SU3MixedContractionSpan.dualContraction (positive w) k sigma
        (PiTensorProduct.tprod ℂ (positiveSubstitute w i (fun a => x (Fin.cast hp a)) v) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun j =>
            negativeSubstitute w i (fun a => y (Fin.cast hq a)) f (Fin.cast h.symm j))) := by
  change SU3MixedContractionSpan.dualContraction (positive w) k sigma
    (TensorProduct.map LinearMap.id (TensorVolumeSplit.powerCast rho.dual h).toLinearEquiv.toLinearMap
      (flatten w (degreeFocus w i p q hp hq v f _))) = _
  rw [degreeFocus_tprod,TensorProduct.map_tmul]
  change SU3MixedContractionSpan.dualContraction (positive w) k sigma
    (_ ⊗ₜ[ℂ] TensorVolumeSplit.powerCast rho.dual h _) = _
  rw [TensorVolumeSplit.powerCast_tprod]
  rfl

def negativeForm (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :=
  (ColorTreeDiagrams.negativeContraction w k h sigma).toLinearMap.comp
    (degreeFocus w i p q hp hq v f)

theorem negative_factor (w : Shape) (k : ℕ) (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k))) (i : Leaf w) (p q : ℕ)
    (hp : positiveAt w i = 1+p) (hq : negativeAt w i = 1+q)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (a : Fin (1+p)) (b : Fin (1+q)) (s : Fin (positive w))
    (ha : s = positiveIndex w i (Fin.cast hp.symm a))
    (hb : Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s)) =
      negativeIndex w i (Fin.cast hq.symm b))
    (e : Vector) (epsilon : Module.Dual ℂ Vector) (he : epsilon e = 1) :
    (negativeForm w k h sigma i p q hp hq v f).comp
        (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) =
      (((negativeForm w k h sigma i p q hp hq v f).comp
        (TensorProduct.map (TensorSlotInsertion.insert p a e) (TensorSlotInsertion.insert q b epsilon))).comp
          (SymmetricTensorTrace.rawTrace p q)).comp
            (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) := by
  classical
  apply SymmetricTraceFactor.factor
  intro x y
  change ColorTreeDiagrams.negativeContraction w k h sigma
    (degreeFocus w i p q hp hq v f _) = y x •
      ColorTreeDiagrams.negativeContraction w k h sigma
        (degreeFocus w i p q hp hq v f (TensorProduct.map _ _ _))
  rw [TensorProduct.map_tmul,TensorSlotInsertion.pure,TensorSlotInsertion.pure,
    negative_focus,negative_focus,cast_update,cast_update,
    positiveSubstitute_update,negativeSubstitute_update]
  have hv : (fun j => Function.update (negativeSubstitute w i (fun _ => y) f)
      (negativeIndex w i (Fin.cast hq.symm b)) epsilon (Fin.cast h.symm j)) =
      Function.update (fun j => negativeSubstitute w i (fun _ => y) f (Fin.cast h.symm j))
        (sigma.symm (Fin.castAdd (3*k) s)) epsilon := by
    rw [← hb]
    exact Function.update_comp_eq_of_injective _ (finCongr h.symm).injective _ _
  rw [hv,← ha]
  have hx := ColorContractionPairFactor.negative (positive w) k sigma s
    (positiveSubstitute w i (fun _ => x) v)
    (fun j => negativeSubstitute w i (fun _ => y) f (Fin.cast h.symm j)) e epsilon he
  rw [hb,ha,positiveSubstitute_index,negativeSubstitute_index] at hx
  simpa only [ha,smul_eq_mul] using hx

end
end Math.ColorFocusPairTrace

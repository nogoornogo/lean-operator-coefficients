import Math.RepresentationTheory.MixedWeightSupport
import Math.RepresentationTheory.FiniteSpeciesExterior

/-! Typed pure-species values determine a mixed exterior/symmetric functional. -/
namespace Math.MixedSpeciesExt
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {V : P → Type*} [∀ p, AddCommGroup (V p)] [∀ p, Module ℂ (V p)]
  {W : Q → Type*} [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)]
  {n m : ℕ}

abbrev Carrier := (⋀[ℂ]^n (∀ p, V p)) ⊗[ℂ] (Sym[ℂ]^m (∀ q, W q))

theorem ext (f h : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (he : ∀ (labels : Fin n → P) (scalars : Fin m → Q)
      (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)),
      f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
        (fun j => Pi.single (scalars j) (w j))) =
      h (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
        (fun j => Pi.single (scalars j) (w j)))) : f = h := by
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) (∀ q, W q))
  rintro _ ⟨w, rfl⟩
  let E := ⋀[ℂ]^n (∀ p, V p)
  let B := Sym[ℂ]^m (∀ q, W q)
  have expandLeft (k : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ) :
      k (MixedWeightSupport.pure v w) = ∑ labels : Fin n → P,
        k (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i (labels i))) w) := by
    let ev := (k.comp ((TensorProduct.mk ℂ E B).flip (SymmetricPower.tprod ℂ w))).compAlternatingMap
      (exteriorPower.ιMulti ℂ n)
    change ev v = ∑ labels : Fin n → P, ev (fun i => Pi.single (labels i) (v i (labels i)))
    calc
      _ = ev (fun i => ∑ s, Pi.single s (v i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = _ := ev.toMultilinearMap.map_sum _
  have expandRight (k : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
      (v' : Fin n → ∀ p, V p) :
      k (MixedWeightSupport.pure v' w) = ∑ labels : Fin m → Q,
        k (MixedWeightSupport.pure v' (fun i => Pi.single (labels i) (w i (labels i)))) := by
    let ev := (k.comp (TensorProduct.mk ℂ E B (exteriorPower.ιMulti ℂ n v'))).compMultilinearMap
      (SymmetricPower.tprod ℂ)
    change ev w = ∑ labels : Fin m → Q, ev (fun i => Pi.single (labels i) (w i (labels i)))
    calc
      _ = ev (fun i => ∑ s, Pi.single s (w i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = _ := ev.map_sum _
  change f (MixedWeightSupport.pure v w) = h (MixedWeightSupport.pure v w)
  rw [expandLeft f, expandLeft h]
  apply Finset.sum_congr rfl
  intro labels _
  rw [expandRight f, expandRight h]
  apply Finset.sum_congr rfl
  intro scalars _
  exact he labels scalars _ _

end
end Math.MixedSpeciesExt

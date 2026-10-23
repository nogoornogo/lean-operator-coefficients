import Math.RepresentationTheory.Color.Diagrams.ColorTreeDiagrams
import Math.RepresentationTheory.Symmetric.SymmetricTensorTrace

/-! Polarization on labelled symmetric color trees and exclusion of repeated
owners in a determinant, as an equality on the entire symmetric source. -/
namespace Math.ColorSymmetricTree
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree SU3DefiningExterior SplitRepresentationProjection
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

def data : Shape → Data
  | .leaf p q =>
    { Carrier := SymmetricTensorTrace.Symmetric (V := Vector) p q
      action := (rho.symmetricPower p).tprod (rho.dual.symmetricPower q) }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Shape) := (data w).Carrier
abbrev action (w : Shape) := (data w).action

def split : (w : Shape) → Split (ColorTensorTree.action w) (action w)
  | .leaf p q => (SymmetricTensorSplit.split rho p).tensor
      (SymmetricTensorSplit.split rho.dual q)
  | .tensor l r => (split l).tensor (split r)

def pure : (w : Shape) → (Leaf w → Vector) → (Leaf w → Module.Dual ℂ Vector) → Carrier w
  | .leaf p q, v, f => SymmetricPower.tprod ℂ (fun _ : Fin p => v ()) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin q => f ())
  | .tensor l r, v, f => pure l (v ∘ Sum.inl) (f ∘ Sum.inl) ⊗ₜ[ℂ]
      pure r (v ∘ Sum.inr) (f ∘ Sum.inr)

theorem embed_pure (w : Shape) (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :
    (split w).embed (pure w v f) = ColorTensorTree.fields w v f := by
  induction w with
  | leaf p q =>
    exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
      (SymmetricTensorSplit.section_pure_power rho p (v ()))
      (SymmetricTensorSplit.section_pure_power rho.dual q (f ()))
  | tensor l r hl hr =>
    change (split l).embed (pure l (v ∘ Sum.inl) (f ∘ Sum.inl)) ⊗ₜ[ℂ]
      (split r).embed (pure r (v ∘ Sum.inr) (f ∘ Sum.inr)) = _
    rw [hl,hr]
    rfl

theorem ext {N : Type*} [AddCommGroup N] [Module ℂ N] (w : Shape)
    {F H : Carrier w →ₗ[ℂ] N}
    (h : ∀ v f, F (pure w v f) = H (pure w v f)) : F = H := by
  induction w generalizing N with
  | leaf p q =>
    apply SymmetricPurePowers.tensor_ext
    intro v f
    exact h (fun _ => v) (fun _ => f)
  | tensor l r hl hr =>
    apply TensorProduct.ext'
    intro x y
    have hx : F.comp ((TensorProduct.mk ℂ _ _).flip y) =
        H.comp ((TensorProduct.mk ℂ _ _).flip y) := by
      apply hl
      intro v f
      have hy : F.comp (TensorProduct.mk ℂ _ _ (pure l v f)) =
          H.comp (TensorProduct.mk ℂ _ _ (pure l v f)) := by
        apply hr
        intro u g
        exact h (Sum.elim v u) (Sum.elim f g)
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hx x

theorem positive_repeated_zero (w : Shape) (k : ℕ)
    (h : positive w = negative w+3*k)
    (sigma : Equiv.Perm (Fin (negative w+3*k)))
    (a : Fin k) (ha : ¬ Function.Injective
      (SU3ContractionDiagram.triples (negative w) k
        (ColorTreeDiagrams.positiveOwner w k h) sigma a)) :
    (ColorTreeDiagrams.positiveContraction w k h sigma).toLinearMap.comp
      (split w).embed.toLinearMap = 0 := by
  classical
  apply ext w
  intro v f
  simp only [LinearMap.comp_apply,IntertwiningMap.toLinearMap_apply,embed_pure,
    ColorTreeDiagrams.positive_fields,SU3ContractionDiagram.formula,LinearMap.zero_apply]
  have hz : SU3VolumeContractions.basis.det (fun j =>
      v (ColorTreeDiagrams.positiveOwner w k h
        (sigma.symm (Fin.natAdd (negative w) (TensorVolumeEvaluation.blockIndex 3 k a j))))) = 0 := by
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ha
    exact SU3VolumeContractions.basis.det.map_eq_zero_of_eq _ (congrArg v hij) hne
  rw [Finset.prod_eq_zero (Finset.mem_univ a) hz,mul_zero]

theorem negative_repeated_zero (w : Shape) (k : ℕ)
    (h : negative w = positive w+3*k)
    (sigma : Equiv.Perm (Fin (positive w+3*k)))
    (a : Fin k) (ha : ¬ Function.Injective
      (SU3DualContractionDiagram.triples (positive w) k
        (ColorTreeDiagrams.negativeOwner w k h) sigma a)) :
    (ColorTreeDiagrams.negativeContraction w k h sigma).toLinearMap.comp
      (split w).embed.toLinearMap = 0 := by
  classical
  apply ext w
  intro v f
  simp only [LinearMap.comp_apply,IntertwiningMap.toLinearMap_apply,embed_pure,
    ColorTreeDiagrams.negative_fields,SU3DualContractionDiagram.formula,LinearMap.zero_apply]
  have hz : SU3MixedContractionSpan.dualBasis.det (fun j =>
      f (ColorTreeDiagrams.negativeOwner w k h
        (sigma.symm (Fin.natAdd (positive w) (TensorVolumeEvaluation.blockIndex 3 k a j))))) = 0 := by
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ha
    exact SU3MixedContractionSpan.dualBasis.det.map_eq_zero_of_eq _ (congrArg f hij) hne
  rw [Finset.prod_eq_zero (Finset.mem_univ a) hz,mul_zero]

end
end Math.ColorSymmetricTree

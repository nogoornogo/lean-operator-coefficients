import Physics.StandardModel.Operators.QqueCoefficientAssembly
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.TensorSquareMultilinear

open Math

/-! Exact Hom description of symmetric residual coefficients.
Completeness among all gauge/spinor invariant qque forms is separate. -/
namespace GUT.QqueResidualHom
noncomputable section
open Representation QqueCoefficientAssembly
open scoped TensorProduct

variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

abbrev tensorEquiv := InvariantTensorCurry.tensorValuedEquiv (a.tprod a) b d

theorem symmetry_iff (f : ResidualCoefficient a b d) : Symmetric a b d f ↔
    ∀ x y, tensorEquiv a b d f (y ⊗ₜ[ℂ] x) = tensorEquiv a b d f (x ⊗ₜ[ℂ] y) := by
  constructor
  · intro hf x y
    change InvariantTensorCurry.dualTensorDual b d _ = InvariantTensorCurry.dualTensorDual b d _
    congr 1
    apply TensorProduct.ext'
    intro u e
    exact hf x y u e
  · intro hf x y u e
    have hh := (InvariantTensorCurry.dualTensorDual b d).injective (hf x y)
    exact congrArg (fun k : Module.Dual ℂ (Module.Dual ℂ B ⊗[ℂ] Module.Dual ℂ D) =>
      k (u ⊗ₜ[ℂ] e)) hh

def symmetricTensorEquiv : symmetricCoefficients a b d ≃ₗ[ℂ]
    TensorSquareMultilinear.symmetricIntertwiners a (b.tprod d) where
  toFun f := ⟨tensorEquiv a b d f.val, (symmetry_iff a b d f.val).mp f.property⟩
  invFun f := ⟨(tensorEquiv a b d).symm f.val, (symmetry_iff a b d _).mpr (by
    rw [(tensorEquiv a b d).apply_symm_apply]
    exact f.property)⟩
  left_inv f := by apply Subtype.ext; exact (tensorEquiv a b d).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (tensorEquiv a b d).apply_symm_apply f.val
  map_add' f g := by apply Subtype.ext; exact (tensorEquiv a b d).map_add f.val g.val
  map_smul' z f := by apply Subtype.ext; exact (tensorEquiv a b d).map_smul z f.val

def equiv : symmetricCoefficients a b d ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (b.tprod d) :=
  (symmetricTensorEquiv a b d).trans
    (TensorSquareMultilinear.symmetricSquareEquiv a (b.tprod d))

/-- Explicit coefficient duality, evaluated on Q inputs and singlet covectors. -/
theorem equiv_symm_tprod (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d))
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    ((equiv a b d).symm f).val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      TensorProduct.dualDistrib ℂ B D (u ⊗ₜ[ℂ] e)
        (f (SymmetricPower.tprod ℂ ![x,y])) := by
  change (InvariantTensorCurry.dualTensorDual b d).symm
    (f (SymmetricPower.tprod ℂ ![x,y])) (u ⊗ₜ[ℂ] e) = _
  change (Module.evalEquiv ℂ (B ⊗[ℂ] D)
    (f (SymmetricPower.tprod ℂ ![x,y])))
      ((TensorProduct.dualDistribEquiv ℂ B D) (u ⊗ₜ[ℂ] e)) = _
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
  exact congrArg (fun l : Module.Dual ℂ (B ⊗[ℂ] D) =>
    l (f (SymmetricPower.tprod ℂ ![x,y])))
      (DFunLike.congr_fun (TensorProduct.toLinearMap_dualDistribEquiv
        (R := ℂ) (M := B) (N := D)) (u ⊗ₜ[ℂ] e))

def assembly := (symmetricAssembly a b d).comp (equiv a b d).symm.toLinearMap

theorem assembly_injective : Function.Injective (assembly a b d) :=
  (symmetricAssembly_injective a b d).comp (equiv a b d).symm.injective

theorem assembly_nonzero_iff (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d)) :
    assembly a b d f ≠ 0 ↔ f ≠ 0 := by
  have hz := map_zero (assembly a b d)
  constructor
  · intro hn hf
    exact hn ((congrArg (assembly a b d) hf).trans hz)
  · intro hn hf
    exact hn (assembly_injective a b d (hf.trans hz.symm))

theorem exists_on_fields (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d))
    (hf : f ≠ 0)
    {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (q : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Q)
    (u : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) U)
    (e : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)
    (eqQ : Representation.Equiv q (QqueSpinorExterior.qField (a := a)))
    (eqU : Representation.Equiv u (QqueSpinorExterior.uField (b := b)))
    (eqE : Representation.Equiv e (QqueSpinorExterior.eField (d := d))) :
    QqueSpinorExterior.HasNonzeroAlternation q u e := by
  let k := (equiv a b d).symm f
  have hk : k.val ≠ 0 := by
    intro hz
    have hk0 : k = 0 := Subtype.ext hz
    have h := congrArg (equiv a b d) hk0
    have he : (equiv a b d) k = f := (equiv a b d).apply_symm_apply f
    rw [he, map_zero] at h
    exact hf h
  exact QqueCoefficientAssembly.exists_on_fields a b d k.val k.property hk
    q u e eqQ eqU eqE

end
end GUT.QqueResidualHom

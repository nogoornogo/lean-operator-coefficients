import Physics.StandardModel.Operators.QqueSpinorExterior

open Math

/-! Assembly for arbitrary residual coefficients, without constituent inputs.
The probe detects the symmetric part in the two Q slots. -/

namespace GUT.QqueCoefficientAssembly
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor QqueSpinorExterior
open scoped TensorProduct

variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (d : Representation ℂ H D)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space) := inferInstance

abbrev ResidualCoefficient := IntertwiningMap
  ((a.tprod a).tprod (b.dual.tprod d.dual)) (Representation.trivial ℂ H ℂ)

def Symmetric (f : ResidualCoefficient a b d) : Prop :=
  ∀ (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D),
    f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))

def assemble (f : ResidualCoefficient a b d) : ExteriorCoefficient
    (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
    (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
    (qField (a := a)) (uField (b := b)) (eField (d := d)) :=
  exterior _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f)

private theorem ordered_add (f g : ResidualCoefficient a b d) :
    ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual (f + g)) =
      ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f) +
      ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual g) := by
  ext q x s q' y t u z v e w l
  change (_ * (f _ + g _)) * _ = (_ * f _) * _ + (_ * g _) * _
  ring

private theorem ordered_smul (z : ℂ) (f : ResidualCoefficient a b d) :
    ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual (z • f)) =
      z • ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f) := by
  ext q x s q' y t u w v e k l
  change (_ * (z * f _)) * _ = z * ((_ * f _) * _)
  ring

theorem assemble_add (f g : ResidualCoefficient a b d) :
    assemble a b d (f + g) = assemble a b d f + assemble a b d g := by
  unfold assemble exterior
  rw [ordered_add]
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  simp [FourSlotAlternation.coefficient, FourSlotAlternation.alternating,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    FourSlotAlternation.ordered, smul_add, Finset.sum_add_distrib]

theorem assemble_smul (z : ℂ) (f : ResidualCoefficient a b d) :
    assemble a b d (z • f) = z • assemble a b d f := by
  unfold assemble exterior
  rw [ordered_smul]
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  simp [FourSlotAlternation.coefficient, FourSlotAlternation.alternating,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    FourSlotAlternation.ordered, Finset.mul_sum, mul_smul_comm]

def assembleLinear : ResidualCoefficient a b d →ₗ[ℂ] ExteriorCoefficient
    (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
    (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
    (qField (a := a)) (uField (b := b)) (eField (d := d)) where
  toFun := assemble a b d
  map_add' := assemble_add a b d
  map_smul' := assemble_smul a b d

theorem probe (f : ResidualCoefficient a b d) (x y : A)
    (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    assemble a b d f (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 0)
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] weakBasis 1)
      ((colorBasis 2 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] weakBasis 0)
      (((1 : ℂ) ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] weakBasis 1))) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) +
      f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  rw [assemble, exterior, FourSlotAlternation.coefficient_slots]
  simp only [ordered_apply, ExplicitSMResidualTensor.qque_tmul,
    StandardSMGaugeTensor.qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem injective_on_symmetric (f g : ResidualCoefficient a b d)
    (hf : Symmetric a b d f) (hg : Symmetric a b d g)
    (he : assemble a b d f = assemble a b d g) : f = g := by
  apply IntertwiningMap.ext
  ext x y u e
  have h := congrArg (fun k => k (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 0)
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] weakBasis 1)
      ((colorBasis 2 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] weakBasis 0)
      (((1 : ℂ) ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] weakBasis 1)))) he
  rw [probe, probe, hf x y u e, hg x y u e] at h
  change f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
    g ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))
  linear_combination (1 / 2 : ℂ) * h

theorem assemble_nonzero (f : ResidualCoefficient a b d)
    (hf : Symmetric a b d f) (hn : f ≠ 0) : assemble a b d f ≠ 0 := by
  intro hz
  apply hn
  apply IntertwiningMap.ext
  ext x y u e
  have h := probe a b d f x y u e
  rw [hz, hf x y u e] at h
  change (0 : ℂ) = f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) +
    f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) at h
  change f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) = 0
  linear_combination (-1 / 2 : ℂ) * h

/-- Symmetry is a linear condition, independent of constituent extraction. -/
def symmetricCoefficients : Submodule ℂ (ResidualCoefficient a b d) where
  carrier := {f | Symmetric a b d f}
  zero_mem' := by intro x y u e; rfl
  add_mem' := by
    intro f g hf hg x y u e
    change f _ + g _ = f _ + g _
    rw [hf x y u e, hg x y u e]
  smul_mem' := by
    intro z f hf x y u e
    change z * f _ = z * f _
    rw [hf x y u e]

def symmetricAssembly := (assembleLinear a b d).comp (symmetricCoefficients a b d).subtype

theorem symmetricAssembly_injective : Function.Injective (symmetricAssembly a b d) := by
  intro f g h
  apply Subtype.ext
  exact injective_on_symmetric a b d f g f.property g.property h

theorem assemble_nonzero_iff (f : ResidualCoefficient a b d)
    (hf : Symmetric a b d f) : assemble a b d f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro hn hz
    subst f
    exact hn (map_zero (assembleLinear a b d))
  · exact assemble_nonzero a b d f hf

theorem exists_on_fields (f : ResidualCoefficient a b d)
    (hf : Symmetric a b d f) (hn : f ≠ 0)
    {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (q : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Q)
    (u : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) U)
    (e : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)
    (eqQ : Representation.Equiv q (qField (a := a)))
    (eqU : Representation.Equiv u (uField (b := b)))
    (eqE : Representation.Equiv e (eField (d := d))) :
    HasNonzeroAlternation q u e := by
  let eQ := ExternalInvariantTensor.externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left)
  let eU := ExternalInvariantTensor.externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right)
  let eE := ExternalInvariantTensor.externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)
  let k := ordered (qField (a := a)) (uField (b := b)) (eField (d := d))
    (ExplicitSMResidualTensor.qque a a b.dual d.dual f)
  refine ⟨k.comp (ExternalInvariantTensor.tensorEquiv
    (ExternalInvariantTensor.tensorEquiv eQ eQ)
    (ExternalInvariantTensor.tensorEquiv eU eE)).toIntertwiningMap, ?_⟩
  exact FourSlotAlternation.coefficient_transport_ne_zero
    (A' := StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space)
    (B' := Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space)
    (C' := ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space)
    (a' := qSpin (qField (a := a))) (b' := uSpin (uField (b := b)))
    (c' := eSpin (eField (d := d)))
    (qSpin q) (uSpin u) (eSpin e) eQ eU eE k (assemble_nonzero a b d f hf hn)

end
end GUT.QqueCoefficientAssembly

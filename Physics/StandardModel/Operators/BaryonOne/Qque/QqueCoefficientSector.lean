import Physics.StandardModel.Operators.BaryonOne.Qque.QqueResidualHom
import Math.RepresentationTheory.Tensors.FourSlotRestrictionLift

open Math

/-! The qque sector is defined by independent species scaling, not by assembly.
The residual Hom map is injective here; its surjectivity is proved in
QqueCoefficientCompleteness without changing this sector definition. -/
namespace Physics.QqueCoefficientSector
set_option autoImplicit false
noncomputable section
open Representation QqueSpinorExterior
open scoped TensorProduct

variable {K Q U E : Type*} [Group K]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]

def sector (q : Representation ℂ K Q) (u : Representation ℂ K U)
    (e : Representation ℂ K E) : Submodule ℂ (ExteriorCoefficient q u e) :=
  FourSlotSpeciesDegree.sector (qSpin q) (uSpin u) (eSpin e)

theorem alternation_mem (q : Representation ℂ K Q) (u : Representation ℂ K U)
    (e : Representation ℂ K E) (f : OrderedCoefficient q u e) :
    FourSlotAlternation.coefficient (qSpin q) (uSpin u) (eSpin e) f ∈ sector q u e :=
  FourSlotSpeciesDegree.coefficient_hasDegree (qSpin q) (uSpin u) (eSpin e) f

/-- This is surjectivity from ordered spinor-field coefficients, not yet from
the residual symmetric-square Hom space. -/
theorem exists_ordered (q : Representation ℂ K Q) (u : Representation ℂ K U)
    (e : Representation ℂ K E) (f : sector q u e) :
    ∃ g : OrderedCoefficient q u e,
      FourSlotAlternation.coefficient (qSpin q) (uSpin u) (eSpin e) g = f.val :=
  FourSlotRestrictionLift.exists_ordered (qSpin q) (uSpin u) (eSpin e) f.val f.property

theorem hasNonzeroAlternation_iff (q : Representation ℂ K Q) (u : Representation ℂ K U)
    (e : Representation ℂ K E) :
    HasNonzeroAlternation q u e ↔ ∃ f : sector q u e, f ≠ 0 := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨FourSlotAlternation.coefficient _ _ _ g, alternation_mem q u e g⟩, ?_⟩
    intro hz
    exact hg (congrArg Subtype.val hz)
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := exists_ordered q u e f
    refine ⟨g, ?_⟩
    intro hz
    apply hf
    apply Subtype.ext
    exact hg.symm.trans hz

variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] Module.Dual ℂ B) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D) := inferInstance

omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ D] in
theorem assemble_mem (f : QqueCoefficientAssembly.ResidualCoefficient a b d) :
    QqueCoefficientAssembly.assemble a b d f ∈
      sector (qField (a := a)) (uField (b := b)) (eField (d := d)) :=
  alternation_mem _ _ _ _

def fromHom : IntertwiningMap (a.symmetricPower 2) (b.tprod d) →ₗ[ℂ]
    sector (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
      (U := SMEpsilonTensor.Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
      (qField (a := a)) (uField (b := b)) (eField (d := d)) :=
  (QqueResidualHom.assembly a b d).codRestrict _ (fun _f => assemble_mem a b d _)

theorem fromHom_injective : Function.Injective (fromHom a b d) := by
  intro f g h
  exact QqueResidualHom.assembly_injective a b d (congrArg Subtype.val h)

end
end Physics.QqueCoefficientSector

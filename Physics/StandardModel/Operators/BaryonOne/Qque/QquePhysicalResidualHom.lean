import Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalExteriorCompleteness
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientCompleteness

/-! Connect the shared physical convention to the existing symmetric-square
Hom theorem. Finite dimension is used only for the dual-to-Hom conversion. -/
namespace Physics.QquePhysicalResidualHom
set_option autoImplicit false
noncomputable section
open Representation
variable {R A B D : Type*} [Group R]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ R A) (b : Representation ℂ R B) (d : Representation ℂ R D)

def residualIdentification : QquePhysicalExteriorCompleteness.residualSpace a b.dual d.dual
    ≃ₗ[ℂ] QqueCoefficientAssembly.symmetricCoefficients a b d :=
  LinearEquiv.refl ℂ _

variable [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]

def homEquiv : QquePhysicalExteriorCompleteness.Sector a b.dual d.dual ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (b.tprod d) :=
  (QquePhysicalExteriorCompleteness.exteriorEquiv a b.dual d.dual).trans
    ((residualIdentification a b d).trans (QqueResidualHom.equiv a b d))

/-- Comparison of the two independently specified physical sectors, via the
same residual Hom. This is not a redefinition as a contraction image. -/
def legacyEquiv : QquePhysicalExteriorCompleteness.Sector a b.dual d.dual ≃ₗ[ℂ]
    QqueCoefficientCompleteness.Sector a b d :=
  (homEquiv a b d).trans (QqueCoefficientCompleteness.equiv a b d)

theorem exists_nonzero_iff :
    (∃ f : QquePhysicalExteriorCompleteness.Sector a b.dual d.dual, f ≠ 0) ↔
      ∃ k : IntertwiningMap (a.symmetricPower 2) (b.tprod d), k ≠ 0 := by
  let s := homEquiv a b d
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨s f, fun h => hf (s.injective (h.trans s.map_zero.symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨s.symm k, fun h => hk (s.symm.injective (h.trans s.symm.map_zero.symm))⟩

end
end Physics.QquePhysicalResidualHom

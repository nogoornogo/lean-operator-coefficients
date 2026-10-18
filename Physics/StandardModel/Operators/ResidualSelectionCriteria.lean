import Math.LinearAlgebra.SelectionCriteria
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.WeinbergSMInterface
import Physics.StandardModel.Operators.DipoleSMCoefficient

open Math

/-! Common algebraic permission/prohibition certificates without discarding
the existing statistics constraints or actual input domains. -/
namespace GUT.ResidualSelectionCriteria
set_option autoImplicit false
noncomputable section
open SelectionCriteria
universe u

variable {H : Type*} [Group H]

theorem deltaLOne {F : DeltaLOneSignedInput.Species → Type*}
    [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
    (flavor : ∀ s, Representation ℂ H (F s)) :
    Certificate (DeltaLOneSignedFields.Sector flavor 1)
      (DeltaLOneCoefficientCompleteness.ResidualProduct flavor) :=
  ofEquiv (DeltaLOneCoefficientCompleteness.equiv flavor)

theorem deltaBTwo {U D : Type u} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup D] [Module ℂ D]
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ D]
    (u : Representation ℂ H U) (d : Representation ℂ H D) :
    Certificate (DeltaBTwoModelInterface.ModelSector u d)
      (SixQuarkTypedFlavor.StatisticsHom U D u d) := by
  exact ofEquiv (k := ℂ) (DeltaBTwoFlavorBridge.sectorHomEquiv u d)

theorem weinberg {F : Type*} [AddCommGroup F] [Module ℂ F]
    (f : Representation ℂ H F) : Certificate (WeinbergSMInterface.ModelSector f)
      (Representation.IntertwiningMap (f.symmetricPower 2)
        (Representation.trivial ℂ H ℂ)) := ofEquiv (WeinbergSMInterface.homEquiv f)

theorem dipole {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
    (a : Representation ℂ H A) (b : Representation ℂ H B) :
    Certificate (DipoleSMCoefficient.SectorB a b × DipoleSMCoefficient.SectorW a b)
      (Representation.IntertwiningMap a b × Representation.IntertwiningMap a b) :=
  ofEquiv (DipoleSMCoefficient.equiv a b)

theorem deltaLOne_forbidden_iff {F : DeltaLOneSignedInput.Species → Type*}
    [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
    (f : ∀ s, Representation ℂ H (F s)) :
    Forbidden (DeltaLOneSignedFields.Sector f 1) ↔
      Forbidden (DuqlOrderedCompleteness.Residual (f 2) (f 1) (f 0) (f 3)) ∧
      Forbidden (QquePhysicalExteriorCompleteness.residualSpace (f 0) (f 1) (f 4)) ∧
      Forbidden (QqqlExchange.residualSpace (f 0) (f 3)) ∧
      Forbidden (DuueOrderedCompleteness.Residual (f 1) (f 2) (f 4)) := by
  rw [(deltaLOne f).forbidden]
  simp only [DeltaLOneCoefficientCompleteness.ResidualProduct, forbidden_prod]

end
end GUT.ResidualSelectionCriteria

import Physics.StandardModel.Operators.LiDuqlCertificate
import Physics.StandardModel.Operators.LiDuueCertificate
import Physics.StandardModel.Operators.LiQqqlExterior
import Physics.StandardModel.Operators.LiQqueConvention
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness

/-! Composition in the shared direct-carrier convention. Physical dagger
interpretations remain supplied identifications, not inferred dualities. -/
namespace GUT.LiFourFamilyCertificate
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneSignedFields
open DeltaLOneFourFamilyDecomposition DeltaLOneFamilyCompleteness
open scoped TensorProduct
variable {H : Type*} [Group H] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ H (F s))

local instance : AddCommGroup (((SMEpsilonTensor.Color ⊗[ℂ] SMEpsilonTensor.Weak)
    ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] F 0) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 1) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 2) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 3) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 4) := Module.addCommMonoidToAddCommGroup ℂ

def duql (k : DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3)) :=
  (duqlEquiv flavor).symm (DuqlExteriorCompleteness.homEquiv _ _ _ _
    (LiDuqlCertificate.candidate _ _ _ _ k))

theorem duql_eq (k : DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3)) :
    duql flavor k = (duqlEquiv flavor).symm k := by
  unfold duql
  rw [LiDuqlCertificate.extract_candidate]

def duue (k : DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4)) :=
  (duueEquiv flavor).symm (DuueResidualCompleteness.homEquiv _ _ _
    (LiDuueCertificate.candidate _ _ _ k))
theorem duue_eq (k : DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4)) :
    duue flavor k = (duueEquiv flavor).symm k := by
  unfold duue
  rw [LiDuueCertificate.extract_candidate]

def qqql (k : QqqlExchange.residualSpace (flavor 0) (flavor 3)) :=
  (qqqlEquiv flavor).symm (QqqlExteriorCompleteness.exteriorEquiv _ _
    (LiQqqlExterior.candidate _ _ (QqqlFlavorComponents.residualEquiv _ _ k)))
theorem qqql_eq (k : QqqlExchange.residualSpace (flavor 0) (flavor 3)) :
    qqql flavor k = (qqqlEquiv flavor).symm k := by
  unfold qqql
  rw [LiQqqlExterior.candidate_eq]
  simp only [QqqlFlavorComponents.exteriorEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_apply_apply]
  exact congrArg ((qqqlEquiv flavor).symm)
    ((QqqlExteriorCompleteness.exteriorEquiv _ _).apply_symm_apply k)

/-- The direct-carrier QQUE factor uses the same normalized D.38 local
contraction; its singlet order reversal and odd Fermi sign cancel. -/
def qque (k : QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4)) :=
  (patternEquiv flavor 1).symm ((qqueOrderedEquiv flavor).symm
    ((QquePhysicalExteriorCompleteness.orderedEquiv _ _ _).symm k))
theorem qque_eq (k : QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4)) :
    qque flavor k = (qqueEquiv flavor).symm k := rfl

/-- D.38 in the shared direct-flavor convention: the explicit outside minus
is the odd E,U reorder, and the paper right bracket has E before U. -/
theorem qque_literal (k : QquePhysicalOrderedCompleteness.Residual
    (flavor 0) (flavor 1) (flavor 4))
    (a b c : SMEpsilonTensor.Color) (v w : SMEpsilonTensor.Weak)
    (s t h j : WeylSpinor.Space) (x y : F 0) (z : F 1) (r : F 4) (m : ℂ) :
    (QquePhysicalOrderedCompleteness.homEquiv _ _ _).symm k
      (((((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] j) ⊗ₜ[ℂ] r))) =
      -(SMEpsilonTensor.eps3 a b c * SMEpsilonTensor.eps2 v w * m *
        (SMEpsilonTensor.eps2 s t * SMEpsilonTensor.eps2 j h) *
          k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r))) := by
  rw [QquePhysicalOrderedCompleteness.assemble_apply]
  simp only [SMEpsilonTensor.eps2]
  ring

def candidate (k : DeltaLOneCoefficientCompleteness.ResidualProduct flavor) : Sector flavor 1 :=
  (DeltaLOneFourFamilyDecomposition.equiv flavor).symm
    ((DeltaLOneCoefficientCompleteness.familyProduct flavor).symm
      (duql flavor k.1, qque flavor k.2.1, qqql flavor k.2.2.1, duue flavor k.2.2.2))
theorem candidate_eq (k : DeltaLOneCoefficientCompleteness.ResidualProduct flavor) :
    candidate flavor k = DeltaLOneCoefficientCompleteness.reconstruct flavor k := by
  rw [DeltaLOneCoefficientCompleteness.reconstruct_factorization]
  unfold candidate
  apply congrArg ((DeltaLOneFourFamilyDecomposition.equiv flavor).symm)
  apply congrArg ((DeltaLOneCoefficientCompleteness.familyProduct flavor).symm)
  exact Prod.ext (duql_eq flavor k.1) (Prod.ext (qque_eq flavor k.2.1)
    (Prod.ext (qqql_eq flavor k.2.2.1) (duue_eq flavor k.2.2.2)))
theorem extract_candidate (k : DeltaLOneCoefficientCompleteness.ResidualProduct flavor) :
    DeltaLOneCoefficientCompleteness.extract flavor (candidate flavor k) = k := by
  rw [candidate_eq, DeltaLOneCoefficientCompleteness.extract_reconstruct]
theorem candidate_extract (f : Sector flavor 1) :
    candidate flavor (DeltaLOneCoefficientCompleteness.extract flavor f) = f := by
  rw [candidate_eq, DeltaLOneCoefficientCompleteness.reconstruct_extract]
end
end GUT.LiFourFamilyCertificate

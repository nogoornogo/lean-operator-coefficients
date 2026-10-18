import Physics.FieldTheory.Mass.FlavorMajoranaUnitary
import Math.LinearAlgebra.UnitaryCongruenceCertificate
import Math.LinearAlgebra.TakagiExistence

open Math

/-! Majorana inputs with an explicit, not assumed-existing, normalization certificate. -/
namespace GUT.FlavorMajoranaCertificate
set_option autoImplicit false
noncomputable section
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A specified symmetric form and a verified unitary normalization.
This structure does not assert that every symmetric matrix admits such data. -/
structure Input (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : Matrix I I ℂ
  symmetric : matrix.IsSymm
  mass : I → ℝ
  nonnegative : ∀ i, 0 ≤ mass i
  basis : unitaryGroup I ℂ
  normalization : UnitaryCongruenceCertificate.Congruent matrix
    (diagonal (fun i => (mass i : ℂ))) basis

/-- Construct certified inputs in any supplied unitary basis, without a
diagonalization oracle. `fromDiagonal_surjective` proves completeness. -/
def fromDiagonal (m : I → ℝ) (hm : ∀ i, 0 ≤ m i) (P : unitaryGroup I ℂ) : Input I where
  matrix := (P⁻¹).val.transpose * diagonal (fun i => (m i : ℂ)) * (P⁻¹).val
  symmetric := by
    change ((_ : Matrix I I ℂ).transpose) = _
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  mass := m
  nonnegative := hm
  basis := P
  normalization := by
    simpa using (UnitaryCongruenceCertificate.inverse
      (M := diagonal (fun i => (m i : ℂ))) (P := P⁻¹) rfl)

/-- A certificate constructed by the proved Takagi theorem, not an external premise. -/
def ofSymmetric (M : Matrix I I ℂ) (hM : M.IsSymm) : Input I :=
  let h := TakagiExistence.exists_nonnegative_diagonal M hM
  { matrix := M
    symmetric := hM
    mass := h.choose
    nonnegative := h.choose_spec.1
    basis := h.choose_spec.2.choose
    normalization := h.choose_spec.2.choose_spec }

theorem ofSymmetric_matrix (M : Matrix I I ℂ) (hM : M.IsSymm) :
    (ofSymmetric M hM).matrix = M := rfl

/-- The previously conditional parametrization now covers every symmetric matrix. -/
theorem fromDiagonal_surjective (M : Matrix I I ℂ) (hM : M.IsSymm) :
    ∃ (m : I → ℝ) (hm : ∀ i, 0 ≤ m i) (P : unitaryGroup I ℂ),
      (fromDiagonal m hm P).matrix = M := by
  obtain ⟨m, hm, P, hP⟩ := TakagiExistence.exists_nonnegative_diagonal M hM
  exact ⟨m, hm, P, UnitaryCongruenceCertificate.inverse hP⟩

def form (D : Input I) : LinearMap.BilinForm ℂ (I → ℂ) := D.matrix.toBilin'

theorem form_symmetric (D : Input I) : (form D).IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mpr D.symmetric

def subgroup (D : Input I) : Subgroup (unitaryGroup I ℂ) :=
  FlavorStabilizer.massSubgroup FlavorMajoranaUnitary.action (form D)

theorem subgroup_eq (D : Input I) :
    subgroup D = UnitaryCongruenceCertificate.subgroup D.matrix := by
  ext U
  rw [UnitaryCongruenceCertificate.bilinear_iff]
  change U ∈ FlavorStabilizer.massSubgroup FlavorMajoranaUnitary.action (form D) ↔ _
  rw [FlavorStabilizer.mass_mem_iff]
  rfl

def classification (D : Input I) :
    subgroup D ≃* MajoranaUnitaryClassification.Coordinates (fun i => (D.mass i : ℂ)) :=
  (MulEquiv.subgroupCongr (subgroup_eq D)).trans
    (UnitaryCongruenceCertificate.classification D.matrix _ D.basis D.normalization)

def basisFreedom (D : Input I) :
    UnitaryDiagonalCongruence.subgroup (fun i => (D.mass i : ℂ)) ≃
      {Q : unitaryGroup I ℂ // UnitaryCongruenceCertificate.Congruent D.matrix
        (diagonal (fun i => (D.mass i : ℂ))) Q} :=
  UnitaryCongruenceCertificate.certificateEquiv D.basis D.normalization

def residualHomEquiv {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (D : Input I)
    (a : Representation ℂ (subgroup D) V) (b : Representation ℂ (subgroup D) W) :
    Representation.IntertwiningMap
      (a.comp (classification D).symm.toMonoidHom)
      (b.comp (classification D).symm.toMonoidHom) ≃ₗ[ℂ]
        Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv (classification D).symm.toMonoidHom
    (classification D).symm.surjective a b

theorem residual_nonzero_iff {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (D : Input I)
    (a : Representation ℂ (subgroup D) V) (b : Representation ℂ (subgroup D) W) :
    (∃ f : Representation.IntertwiningMap
      (a.comp (classification D).symm.toMonoidHom)
      (b.comp (classification D).symm.toMonoidHom), f ≠ 0) ↔
        ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff (classification D).symm.toMonoidHom
    (classification D).symm.surjective a b

end
end GUT.FlavorMajoranaCertificate

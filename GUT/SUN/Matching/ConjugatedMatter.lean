import Math.RepresentationTheory.ExteriorSquareTransport
import GUT.SUN.Matching.ExteriorCurrents

open Math

/-! Simultaneous SU(N) conjugation of the background, broken directions
and retained matter. The projected currents are recomputed from the action. -/
set_option autoImplicit false
namespace GUT.SUN.ConjugatedMatter

noncomputable section
open ExteriorMatter DiagonalBackground ExteriorSquareCoordinates ExteriorSquareTransport
variable {r : ℕ} (U : Group r)

def rotation : (Fin (5+r) → ℂ) ≃ₗ[ℂ] (Fin (5+r) → ℂ) :=
  { fundamental r U with
    invFun := fundamental r U⁻¹
    left_inv x := by
      change (fundamental r U⁻¹ * fundamental r U) x = x
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    right_inv x := by
      change (fundamental r U * fundamental r U⁻¹) x = x
      rw [← map_mul, mul_inv_cancel, map_one]; rfl }

theorem conjugate_matrix (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :
    conjugate (rotation U) X =
      (U : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) * X * (U⁻¹ : Group r) := by
  apply Matrix.toLin'.injective
  rw [toLin_conjugate, Matrix.toLin'_mul, Matrix.toLin'_mul]
  rfl

def inclusion : SU5.StandardModelEmbedding.TargetGroup →* Group r :=
  (MulAut.conj U).toMonoidHom.comp (ExteriorMatter.inclusion r)
theorem inclusion_injective : Function.Injective (inclusion U) :=
  (MulAut.conj U).injective.comp (ExteriorMatter.inclusion_injective r)

def embed := (exterior (rotation U)).toLinearMap.comp (ExteriorSquareBlock.embed r)
def project := (ExteriorSquareBlock.project r).comp (exterior (rotation U)).symm.toLinearMap
theorem project_embed : (project U).comp (embed U) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change ExteriorSquareBlock.project r
    ((exterior (rotation U)).symm (exterior (rotation U) (ExteriorSquareBlock.embed r x))) = x
  rw [LinearEquiv.symm_apply_apply]
  exact DFunLike.congr_fun (ExteriorSquareBlock.project_embed r) x

theorem exterior_rotation : (exterior (rotation U)).toLinearMap = matter r U := rfl
theorem matter_embed (g : SU5.StandardModelEmbedding.TargetGroup) (x : SU5.Matter.Ten) :
    matter r (inclusion U g) (embed U x) = embed U (SU5.Matter.ten g x) := by
  change matter r (U * ExteriorMatter.inclusion r g * U⁻¹)
    (matter r U (ExteriorSquareBlock.embed r x)) =
    matter r U (ExteriorSquareBlock.embed r (SU5.Matter.ten g x))
  have h : U * ExteriorMatter.inclusion r g * U⁻¹ * U = U * ExteriorMatter.inclusion r g := by group
  change (matter r (U * ExteriorMatter.inclusion r g * U⁻¹) * matter r U)
    (ExteriorSquareBlock.embed r x) = _
  rw [← map_mul, h, map_mul]
  change matter r U (matter r (ExteriorMatter.inclusion r g) (ExteriorSquareBlock.embed r x)) = _
  rw [ExteriorMatter.matter_embed]

def coreAction (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :=
  (project U).comp ((infinitesimal (conjugate (rotation U) X)).comp (embed U))
theorem coreAction_eq (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :
    coreAction U X = ExteriorSquareBlock.coreAction r X := by
  apply LinearMap.ext
  intro x
  change ExteriorSquareBlock.project r ((exterior (rotation U)).symm
    (infinitesimal (conjugate (rotation U) X) (exterior (rotation U) (ExteriorSquareBlock.embed r x)))) = _
  rw [infinitesimal_natural, LinearEquiv.symm_apply_apply]
  rfl

variable (D : Background r)
def background := conjugate (rotation U) D.matrix
def massOperator (g : ℝ) (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :=
  (g : ℂ)^2 • doubleCommutator (background U D) X

theorem background_trace : Matrix.trace (background U D) = 0 := by
  rw [background, conjugate_matrix, Matrix.trace_mul_cycle]
  have h : (U⁻¹ : Group r).val * U.val = 1 := congrArg Subtype.val (inv_mul_cancel U)
  rw [h, one_mul]
  exact D.matrix_trace

theorem background_hermitian : (background U D).conjTranspose = background U D := by
  rw [background, conjugate_matrix]
  change ((U.val * D.matrix * U.val.conjTranspose).conjTranspose) =
    U.val * D.matrix * U.val.conjTranspose
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, D.matrix_hermitian,
    Matrix.mul_assoc]

theorem mass_conjugate (g : ℝ) (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :
    massOperator U D g (conjugate (rotation U) X) =
      conjugate (rotation U) (D.massOperator g X) := by
  rw [massOperator, background, doubleCommutator_conjugate, ← map_smul]
  rfl
theorem mass_zero_iff (g : ℝ) (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :
    massOperator U D g (conjugate (rotation U) X) = 0 ↔ D.massOperator g X = 0 := by
  rw [mass_conjugate]
  exact map_eq_zero_iff _ (conjugate (rotation U)).injective
theorem upper_mass (g : ℝ) (c : D.Channel) :
    massOperator U D g (conjugate (rotation U) (D.upper c)) =
      (D.massSquared g c : ℂ) • conjugate (rotation U) (D.upper c) := by
  rw [mass_conjugate, D.upper_mass, map_smul]
theorem lower_mass (g : ℝ) (c : D.Channel) :
    massOperator U D g (conjugate (rotation U) (D.lower c)) =
      (D.massSquared g c : ℂ) • conjugate (rotation U) (D.lower c) := by
  rw [mass_conjugate, D.lower_mass, map_smul]

def upCurrent (c : D.Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ SMEpsilonTensor.Color :=
  ((LinearMap.fst ℂ _ _).comp SU5.ExteriorSquareBranching.branch).comp
    ((coreAction U (D.upper c)).comp SU5.HeavyCurrents.quarkEmbed)
def electronCurrent (c : D.Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ ℂ :=
  ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp SU5.ExteriorSquareBranching.branch)).comp
    ((coreAction U (D.lower c)).comp SU5.HeavyCurrents.quarkEmbed)

theorem upCurrent_eq (c : D.Channel) : upCurrent U D c = ExteriorCurrents.upCurrent D c := by
  simp only [upCurrent, coreAction_eq, ExteriorCurrents.upCurrent]
theorem electronCurrent_eq (c : D.Channel) :
    electronCurrent U D c = ExteriorCurrents.electronCurrent D c := by
  simp only [electronCurrent, coreAction_eq, ExteriorCurrents.electronCurrent]

end
end GUT.SUN.ConjugatedMatter

import Math.LinearAlgebra.SymmetricFourth22
import Math.RepresentationTheory.ExteriorFourthKernels
import Math.RepresentationTheory.SymmetricSquareCauchy

/-! The universal symmetric quartic split retains an arbitrary group
action, including every commuting color/weak/spin factor. -/
namespace Math.SymmetricFourth22Representation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)
@[reducible] local instance : AddCommGroup (SymmetricFourth22.Source (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
abbrev source := (r.symmetricPower 2).symmetricPower 2
abbrev kernel := ExteriorFourthKernelsRepresentation.action22 r

theorem pair_natural (f : A →ₗ[ℂ] A) (a b c d : A) :
    SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) f)
      (SymmetricFourth22.pair a b c d)=SymmetricFourth22.pair (f a) (f b) (f c) (f d) := by
  unfold SymmetricFourth22.pair
  rw [← SymmetricSquareCauchyRepresentation.sym_natural,
    ← SymmetricSquareCauchyRepresentation.sym_natural,
    ← SymmetricSquareCauchyRepresentation.sym_natural]

theorem multiply_natural (f : A →ₗ[ℂ] A) (x : SymmetricFourth22.Source (A := A)) :
    SymmetricFourth22.multiply
      (SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) f) x)=
        SymmetricPower.map (ι := Fin 4) f (SymmetricFourth22.multiply x) := by
  have h : (SymmetricFourth22.multiply (A := A)).comp
      (SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) f))=
        (SymmetricPower.map (ι := Fin 4) f).comp SymmetricFourth22.multiply := by
    apply SymmetricFourth22.source_ext
    intro a b c d
    simp only [LinearMap.comp_apply, pair_natural, SymmetricFourth22.multiply_pure,
      SymmetricPower.map_tprod]
    congr 1
    ext i
    fin_cases i <;> rfl
  exact LinearMap.congr_fun h x

theorem toExterior_natural (f : A →ₗ[ℂ] A) (x : SymmetricFourth22.Source (A := A)) :
    SymmetricFourth22.toExterior
      (SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) f) x)=
        SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) (SymmetricFourth22.toExterior x) := by
  have h : (SymmetricFourth22.toExterior (A := A)).comp
      (SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) f))=
        (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f)).comp SymmetricFourth22.toExterior := by
    apply SymmetricFourth22.source_ext
    intro a b c d
    simp only [LinearMap.comp_apply, pair_natural, SymmetricFourth22.toExterior_pure, map_add,
      ← ExteriorFourthKernels.sym_natural, ← SymmetricSquareCauchyRepresentation.wedge_natural]
  exact LinearMap.congr_fun h x

def multiply : IntertwiningMap (source r) (r.symmetricPower 4) where
  toLinearMap := SymmetricFourth22.multiply
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact multiply_natural (r g) x

def project : IntertwiningMap (source r) (kernel r) where
  toLinearMap := (3 : ℂ)⁻¹ • SymmetricFourth22.toKernel
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (3 : ℂ)⁻¹ • SymmetricFourth22.toExterior
        (SymmetricPower.map (ι := Fin 2) (SymmetricPower.map (ι := Fin 2) (r g)) x)=
      SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 (r g))
        ((3 : ℂ)⁻¹ • SymmetricFourth22.toExterior x)
    rw [toExterior_natural, map_smul]

/-- An actual equivariant equivalence, with no dimension, irreducibility
or branching hypothesis. -/
def equivalence : Representation.Equiv (source r) ((r.symmetricPower 4).prod (kernel r)) where
  toLinearEquiv := SymmetricFourth22.equivalence
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (multiply r).isIntertwining _ _ g x
    · exact (project r).isIntertwining _ _ g x

/-- In dimension at most three the fourth exterior quotient is zero, so
its actual kernel is the entire symmetric exterior-square source. -/
def kernelFull [FiniteDimensional ℂ A] (hd : Module.finrank ℂ A<4) :
    Representation.Equiv (kernel r) (ExteriorFourthKernelsRepresentation.source22 r) where
  toLinearEquiv := LinearEquiv.ofBijective (ExteriorFourthKernels.K22 (A := A)).subtype
    ⟨Subtype.val_injective, fun x =>
      ⟨⟨x, exteriorPower.eq_zero_of_finrank_lt 4 hd (ExteriorFourthKernels.multiply22 x)⟩, rfl⟩⟩
  isIntertwining' := (ExteriorFourthKernelsRepresentation.kernel22 r).subtype.isIntertwining'

end
end Math.SymmetricFourth22Representation

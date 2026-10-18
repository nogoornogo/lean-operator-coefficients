import Math.RepresentationTheory.SymmetricSquareCauchy

/-! Symmetric/exterior splitting of a binary tensor square. Both inverse
maps are the universal quotient sections, for an arbitrary retained action. -/
namespace Math.SymmetricExteriorSquare
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients Representation
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 A) × (⋀[ℂ]^2 A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem reconstruct (x : A ⊗[ℂ] A) :
    symmetricSection (sym x)+alternatingSection (wedge x)=(2 : ℂ) • x := by
  have h : (symmetricSection (A := A)).comp sym+alternatingSection.comp wedge=
      (2 : ℂ) • LinearMap.id := by
    apply TensorProduct.ext'
    intro a b
    change symmetricSection (sym (a ⊗ₜ[ℂ] b))+alternatingSection (wedge (a ⊗ₜ[ℂ] b))=
      (2 : ℂ) • (a ⊗ₜ[ℂ] b)
    rw [symmetricSection_pure, alternatingSection_pure]
    module
  exact LinearMap.congr_fun h x

def linearEquivalence : (A ⊗[ℂ] A) ≃ₗ[ℂ] (Sym[ℂ]^2 A) × (⋀[ℂ]^2 A) where
  toLinearMap := sym.prod wedge
  invFun x := (2 : ℂ)⁻¹ • (symmetricSection x.1+alternatingSection x.2)
  left_inv x := by
    change (2 : ℂ)⁻¹ • (symmetricSection (sym x)+alternatingSection (wedge x))=x
    rw [reconstruct, smul_smul]
    norm_num
  right_inv x := by
    apply Prod.ext
    · change sym ((2 : ℂ)⁻¹ • (symmetricSection x.1+alternatingSection x.2))=x.1
      rw [map_smul, map_add, sym_section, sym_alternating, add_zero, smul_smul]
      norm_num
    · change wedge ((2 : ℂ)⁻¹ • (symmetricSection x.1+alternatingSection x.2))=x.2
      rw [map_smul, map_add, wedge_symmetric, wedge_section, zero_add, smul_smul]
      norm_num

variable {G : Type*} [Group G] (r : Representation ℂ G A)

def equivalence : Representation.Equiv (r.tprod r)
    ((r.symmetricPower 2).prod (r.exteriorPower 2)) where
  toLinearEquiv := linearEquivalence
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro a b
    apply Prod.ext
    · exact SymmetricSquareCauchyRepresentation.sym_natural (r g) a b
    · exact SymmetricSquareCauchyRepresentation.wedge_natural (r g) a b

end
end Math.SymmetricExteriorSquare

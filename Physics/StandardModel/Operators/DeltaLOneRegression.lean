import Physics.StandardModel.Operators.DeltaLOneInputTransport
import Physics.StandardModel.Operators.QqqlScalarFlavor
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Regression controls for the full classification. Four coefficients is a
neutral scalar-multiplicity specialization, not an arbitrary-flavor count. -/
namespace GUT.DeltaLOneRegression
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneCoefficientCompleteness
open scoped TensorProduct
variable {R : Type*} [Group R]

theorem qque_scalar_symmetric (q u e : Representation ℂ R ℂ)
    (f : QquePhysicalOrderedCompleteness.Residual q u e) :
    QquePhysicalExteriorCompleteness.Symmetric q u e f := by
  intro x y z w
  calc
    _ = ((y*x)*(z*w)) * f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) :=
      DuueScalarFlavor.scalar_formula q u e f y x z w
    _ = ((x*y)*(z*w)) * f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) := by ring
    _ = _ := (DuueScalarFlavor.scalar_formula q u e f x y z w).symm

def qqueScalarForget (q u e : Representation ℂ R ℂ) :
    QquePhysicalExteriorCompleteness.residualSpace q u e ≃ₗ[ℂ]
      QquePhysicalOrderedCompleteness.Residual q u e where
  toFun f := f.val
  invFun f := ⟨f, qque_scalar_symmetric q u e f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def neutralFlavor : ∀ _ : Species, Representation ℂ R ℂ :=
  fun _ => Representation.trivial ℂ R ℂ

/-- Each neutral one-generation family contributes one independent coefficient. -/
def neutralResidualEquiv : ResidualProduct (neutralFlavor (R := R)) ≃ₗ[ℂ]
    ℂ × (ℂ × (ℂ × ℂ)) :=
  LinearEquiv.prodCongr
    (DuueScalarFlavor.scalarEquiv _ _ _ (by intro r; norm_num [neutralFlavor]))
    (LinearEquiv.prodCongr
      ((qqueScalarForget _ _ _).trans
        (DuueScalarFlavor.scalarEquiv _ _ _ (by intro r; norm_num [neutralFlavor])))
      (LinearEquiv.prodCongr
        (QqqlScalarFlavor.residualEquiv _ _ (by intro r; norm_num [neutralFlavor]))
        (DuueScalarFlavor.scalarEquiv _ _ _ (by intro r; norm_num [neutralFlavor]))))

def oneGenerationEquiv : DeltaLOneSignedFields.Sector (neutralFlavor (R := R)) 1 ≃ₗ[ℂ]
    ℂ × (ℂ × (ℂ × ℂ)) :=
  (DeltaLOneCoefficientCompleteness.equiv _).trans neutralResidualEquiv

theorem oneGeneration_finrank : Module.finrank ℂ
    (DeltaLOneSignedFields.Sector (neutralFlavor (R := R)) 1) = 4 := by
  rw [oneGenerationEquiv.finrank_eq]
  norm_num [Module.finrank_prod, Module.finrank_self]

/-- Scalar multiplicity does not mean neutral multiplicity: a nontrivial
product character kills the corresponding residual intertwiner. -/
theorem scalarHom_vanish (a b c d : Representation ℂ R ℂ)
    (r : R) (hn : (a r 1 * b r 1) * (c r 1 * d r 1) ≠ 1)
    (f : IntertwiningMap ((a.tprod b).tprod (c.tprod d))
      (Representation.trivial ℂ R ℂ)) : f = 0 := by
  have he := IntertwiningMap.isIntertwining _ _ f r
    (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
  have eval (x y z w : ℂ) : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) =
      ((x*y)*(z*w)) * f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) := by
    calc
      _ = f (((x • (1 : ℂ)) ⊗ₜ[ℂ] (y • (1 : ℂ))) ⊗ₜ[ℂ]
        ((z • (1 : ℂ)) ⊗ₜ[ℂ] (w • (1 : ℂ)))) := by simp
      _ = _ := by
        rw [TensorProduct.smul_tmul_smul, TensorProduct.smul_tmul_smul,
          TensorProduct.smul_tmul_smul, map_smul]
        rfl
  change f ((a r 1 ⊗ₜ[ℂ] b r 1) ⊗ₜ[ℂ] (c r 1 ⊗ₜ[ℂ] d r 1)) = f _ at he
  rw [eval] at he
  have hz : f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) = 0 := by
    have hp : ((a r 1 * b r 1) * (c r 1 * d r 1) - 1) *
      f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hn)
  apply IntertwiningMap.ext
  ext
  exact hz

/-- If none of the four product characters is neutral, the entire sector
vanishes. The test elements may be different for each family. -/
theorem scalar_charge_vanish (flavor : ∀ _ : Species, Representation ℂ R ℂ)
    (hduql : ∃ r, ((flavor 2 r 1) * (flavor 1 r 1)) *
      ((flavor 0 r 1) * (flavor 3 r 1)) ≠ 1)
    (hqque : ∃ r, ((flavor 0 r 1) * (flavor 0 r 1)) *
      ((flavor 1 r 1) * (flavor 4 r 1)) ≠ 1)
    (hqqql : ∃ r, ((flavor 0 r 1) * (flavor 0 r 1)) *
      ((flavor 0 r 1) * (flavor 3 r 1)) ≠ 1)
    (hduue : ∃ r, ((flavor 1 r 1) * (flavor 1 r 1)) *
      ((flavor 2 r 1) * (flavor 4 r 1)) ≠ 1)
    (f : DeltaLOneSignedFields.Sector flavor 1) : f = 0 := by
  apply coefficient_ext flavor
  rw [map_zero]
  obtain ⟨r₀,h₀⟩ := hduql
  obtain ⟨r₁,h₁⟩ := hqque
  obtain ⟨r₂,h₂⟩ := hqqql
  obtain ⟨r₃,h₃⟩ := hduue
  apply Prod.ext
  · exact scalarHom_vanish _ _ _ _ r₀ h₀ _
  · apply Prod.ext
    · apply Subtype.ext
      exact scalarHom_vanish _ _ _ _ r₁ h₁ _
    · apply Prod.ext
      · apply Subtype.ext
        funext i j
        exact scalarHom_vanish _ _ _ _ r₂ h₂ _
      · exact scalarHom_vanish _ _ _ _ r₃ h₃ _

variable {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

/-- A missing quark species removes precisely the three families containing q. -/
theorem zero_quark_factors [Subsingleton (F 0)] (f : DeltaLOneSignedFields.Sector flavor 1) :
    (extract flavor f).1 = 0 ∧ (extract flavor f).2.1 = 0 ∧
      (extract flavor f).2.2.1 = 0 := by
  constructor
  · apply IntertwiningMap.ext
    repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
    rename_i d u q l
    have hq : q = 0 := Subsingleton.elim _ _
    simp [hq]
  · constructor
    · apply Subtype.ext
      apply IntertwiningMap.ext
      repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
      rename_i q q' u e
      have hq : q = 0 := Subsingleton.elim _ _
      simp [hq]
    · apply Subtype.ext
      funext i j
      apply IntertwiningMap.ext
      repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
      rename_i q q' q'' l
      have hq : q = 0 := Subsingleton.elim _ _
      simp [hq]

/-- With both q and u absent there is no degree-one four-fermion coefficient. -/
theorem zero_quark_up [Subsingleton (F 0)] [Subsingleton (F 1)]
    (f : DeltaLOneSignedFields.Sector flavor 1) : f = 0 := by
  apply coefficient_ext flavor
  rw [map_zero]
  have h := zero_quark_factors flavor f
  have hu : (extract flavor f).2.2.2 = 0 := by
    apply IntertwiningMap.ext
    repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
    rename_i u u' d e
    have hz : u = 0 := Subsingleton.elim _ _
    simp [hz]
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2 hu))

end
end GUT.DeltaLOneRegression

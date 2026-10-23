import Math.LinearAlgebra.Matrix.MajoranaUnitaryClassification

/-! Conditional classification and exact basis freedom for unitary congruence.
No existence of a diagonalizing certificate is asserted. -/
namespace Math.UnitaryCongruenceCertificate
set_option autoImplicit false
noncomputable section
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def Congruent (M N : Matrix I I ℂ) (P : unitaryGroup I ℂ) : Prop :=
  P.val.transpose * M * P.val = N

theorem comp {M N K : Matrix I I ℂ} {P Q : unitaryGroup I ℂ}
    (hP : Congruent M N P) (hQ : Congruent N K Q) : Congruent M K (P * Q) := by
  change (P.val * Q.val).transpose * M * (P.val * Q.val) = K
  calc
    _ = Q.val.transpose * (P.val.transpose * M * P.val) * Q.val := by
      simp only [transpose_mul, Matrix.mul_assoc]
    _ = K := by rw [hP]; exact hQ

theorem inverse {M N : Matrix I I ℂ} {P : unitaryGroup I ℂ}
    (hP : Congruent M N P) : Congruent N M P⁻¹ := by
  change (P⁻¹).val.transpose * N * (P⁻¹).val = M
  rw [← hP]
  have hi : P.val * (P⁻¹).val = 1 :=
    congrArg (fun U : unitaryGroup I ℂ => U.val) (mul_inv_cancel P)
  calc
    _ = (P.val * (P⁻¹).val).transpose * M * (P.val * (P⁻¹).val) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    _ = M := by rw [hi]; simp

def subgroup (M : Matrix I I ℂ) : Subgroup (unitaryGroup I ℂ) where
  carrier := {U | Congruent M M U}
  one_mem' := by change (1 : Matrix I I ℂ).transpose * M * 1 = M; simp
  mul_mem' := fun hP hQ => comp hP hQ
  inv_mem' := fun hP => inverse hP

theorem bilinear_iff (M : Matrix I I ℂ) (U : unitaryGroup I ℂ) :
    U ∈ subgroup M ↔ ∀ x y : I → ℂ,
      M.toBilin' (U.val.toLin' x) (U.val.toLin' y) = M.toBilin' x y := by
  have he : U ∈ subgroup M ↔ M.toBilin'.comp U.val.toLin' U.val.toLin' = M.toBilin' := by
    rw [Matrix.toBilin'_comp]
    exact Matrix.toBilin'.injective.eq_iff.symm
  rw [he]
  constructor
  · intro h x y
    exact congrArg (fun B : LinearMap.BilinForm ℂ (I → ℂ) => B x y) h
  · intro h
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    exact h x y

def congruenceEquiv {M N : Matrix I I ℂ} (P : unitaryGroup I ℂ)
    (hP : Congruent M N P) : subgroup N ≃* subgroup M where
  toFun U := ⟨P * U.val * P⁻¹, comp (comp hP U.property) (inverse hP)⟩
  invFun U := ⟨P⁻¹ * U.val * P, comp (comp (inverse hP) U.property) hP⟩
  left_inv U := by apply Subtype.ext; simp [mul_assoc]
  right_inv U := by apply Subtype.ext; simp [mul_assoc]
  map_mul' U V := by apply Subtype.ext; simp [mul_assoc]

theorem diagonal_subgroup (c : I → ℂ) :
    subgroup (diagonal c) = UnitaryDiagonalCongruence.subgroup c := rfl

def classification (M : Matrix I I ℂ) (c : I → ℂ) (P : unitaryGroup I ℂ)
    (hP : Congruent M (diagonal c) P) :
    subgroup M ≃* MajoranaUnitaryClassification.Coordinates c :=
  (congruenceEquiv P hP).symm.trans (MajoranaUnitaryClassification.classification c)

/-- Every certificate to the fixed target is uniquely P times its stabilizer. -/
def certificateEquiv {M N : Matrix I I ℂ} (P : unitaryGroup I ℂ)
    (hP : Congruent M N P) : subgroup N ≃ {Q : unitaryGroup I ℂ // Congruent M N Q} where
  toFun S := ⟨P * S.val, comp hP S.property⟩
  invFun Q := ⟨P⁻¹ * Q.val, comp (inverse hP) Q.property⟩
  left_inv S := by apply Subtype.ext; simp
  right_inv Q := by apply Subtype.ext; simp

theorem exists_unique_difference {M N : Matrix I I ℂ} (P Q : unitaryGroup I ℂ)
    (hP : Congruent M N P) (hQ : Congruent M N Q) :
    ∃! S : subgroup N, P * S.val = Q := by
  refine ⟨(certificateEquiv P hP).symm ⟨Q, hQ⟩, ?_, ?_⟩
  · exact congrArg Subtype.val ((certificateEquiv P hP).apply_symm_apply ⟨Q, hQ⟩)
  · intro S hS
    apply (certificateEquiv P hP).injective
    rw [(certificateEquiv P hP).apply_symm_apply]
    apply Subtype.ext
    exact hS

def residualHomEquiv {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (M : Matrix I I ℂ) (c : I → ℂ)
    (P : unitaryGroup I ℂ) (hP : Congruent M (diagonal c) P)
    (a : Representation ℂ (subgroup M) V) (b : Representation ℂ (subgroup M) W) :
    Representation.IntertwiningMap
      (a.comp (classification M c P hP).symm.toMonoidHom)
      (b.comp (classification M c P hP).symm.toMonoidHom) ≃ₗ[ℂ]
        Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv (classification M c P hP).symm.toMonoidHom
    (classification M c P hP).symm.surjective a b

theorem residual_nonzero_iff {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (M : Matrix I I ℂ) (c : I → ℂ)
    (P : unitaryGroup I ℂ) (hP : Congruent M (diagonal c) P)
    (a : Representation ℂ (subgroup M) V) (b : Representation ℂ (subgroup M) W) :
    (∃ f : Representation.IntertwiningMap
      (a.comp (classification M c P hP).symm.toMonoidHom)
      (b.comp (classification M c P hP).symm.toMonoidHom), f ≠ 0) ↔
        ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff (classification M c P hP).symm.toMonoidHom
    (classification M c P hP).symm.surjective a b

end
end Math.UnitaryCongruenceCertificate

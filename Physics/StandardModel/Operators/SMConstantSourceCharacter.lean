import Math.RepresentationTheory.ExteriorCharacterPolynomial
import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMWeakWeightBasis

/-! Actual constant-species source characters, uniformly in the exterior degree.
These are torus characters; a zero weight is not a gauge/Weyl invariant. -/
namespace GUT.SMConstantSourceCharacter
set_option autoImplicit false
noncomputable section
open Math Representation Polynomial
open scoped BigOperators
open scoped TensorProduct

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem weak_character (s : DeltaLOneSignedInput.Species) (n : ℕ) (z : Circle) :
    (PatternExteriorSource.representation (DeltaLOneSignedFields.field flavor)
      (fun _ : Fin n => s)).character (SMWeakWeightBasis.fullTorus z) =
    (ExteriorCharacterPolynomial.generating
      (fun i : SMWeakWeightBasis.FieldIndex s =>
        (z : ℂ) ^ SMWeakWeightBasis.gaugeWeight s i.1.1)).coeff n := by
  rw [← Representation.char_iso
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s n)]
  exact ExteriorCharacterPolynomial.exterior_character _
    (SMWeakWeightBasis.fieldBasis s) _ _
    (fun i => SMWeakWeightBasis.field_basis_eigen flavor s i z) n

theorem lepton_generating (z : Circle) :
    ExteriorCharacterPolynomial.generating
      (fun i : SMWeakWeightBasis.FieldIndex 3 =>
        (z : ℂ) ^ SMWeakWeightBasis.gaugeWeight 3 i.1.1) =
      ((1 + C (z : ℂ) * X) * (1 + C ((z : ℂ)⁻¹) * X)) ^ 6 := by
  unfold ExteriorCharacterPolynomial.generating
  change (∏ i : (Fin 2 × Fin 2) × Fin 3,
    (1 + C ((z : ℂ) ^ SMWeakWeightBasis.weakWeight i.1.1) * X)) = _
  simp only [Fintype.prod_prod_type]
  simp [SMWeakWeightBasis.weakWeight, Fin.prod_univ_two, ← mul_pow, ← pow_mul]

/-- The lepton weak character as a symbolic product, for every exterior degree. -/
theorem lepton_weak_character (n : ℕ) (z : Circle) :
    (PatternExteriorSource.representation (DeltaLOneSignedFields.field flavor)
      (fun _ : Fin n => (3 : DeltaLOneSignedInput.Species))).character
        (SMWeakWeightBasis.fullTorus z) =
      (((1 + C (z : ℂ) * X) * (1 + C ((z : ℂ)⁻¹) * X)) ^ 6).coeff n :=
  (weak_character flavor 3 n z).trans (congrArg (fun p : ℂ[X] => p.coeff n)
    (lepton_generating z))

def leptonTorus (z w : Circle) : NeutralHiggsPowers.G H :=
  ((SMWeakWeightBasis.gaugeTorus z,
    FourSameWeylCompleteness.specialLinear (TauCeti.SU2.torusHom w)), 1)

theorem left_torus_basis (w : Circle) (j : Fin 2) :
    WeylSpinor.left (FourSameWeylCompleteness.specialLinear (TauCeti.SU2.torusHom w))
      (Pi.basisFun ℂ (Fin 2) j) =
    (w : ℂ)^SMWeakWeightBasis.weakWeight j • Pi.basisFun ℂ (Fin 2) j := by
  exact SMWeakWeightBasis.weak_basis_eigen j w

theorem lepton_basis_eigen (z w : Circle) (i : SMWeakWeightBasis.FieldIndex 3) :
    DeltaLOneSignedFields.field flavor 3 (leptonTorus z w)
      (SMWeakWeightBasis.fieldBasis 3 i) =
    ((z : ℂ)^SMWeakWeightBasis.weakWeight i.1.1 *
      (w : ℂ)^SMWeakWeightBasis.weakWeight i.1.2) •
        SMWeakWeightBasis.fieldBasis 3 i := by
  rcases i with ⟨⟨i,j⟩,k⟩
  simp only [SMWeakWeightBasis.fieldBasis, Module.Basis.tensorProduct_apply]
  change ((DeltaLOneSignedFields.gauge 3 (SMWeakWeightBasis.gaugeTorus z)
      (SMWeakWeightBasis.gaugeBasis 3 i)) ⊗ₜ[ℂ]
    (WeylSpinor.left (FourSameWeylCompleteness.specialLinear (TauCeti.SU2.torusHom w))
      (Pi.basisFun ℂ (Fin 2) j))) ⊗ₜ[ℂ] (flavor 3 1 (Pi.basisFun ℂ (Fin 3) k)) = _
  rw [SMWeakWeightBasis.gauge_basis_eigen 3 i z, left_torus_basis, map_one]
  simp only [Module.End.one_apply, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_smul]
  simp only [SMWeakWeightBasis.gaugeWeight, mul_comm]

/-- Both weak and Weyl torus variables are retained, for every fermion degree. -/
theorem lepton_character (n : ℕ) (z w : Circle) :
    (PatternExteriorSource.representation (DeltaLOneSignedFields.field flavor)
      (fun _ : Fin n => (3 : DeltaLOneSignedInput.Species))).character
        (leptonTorus z w) =
      (ExteriorCharacterPolynomial.generating
        (fun i : SMWeakWeightBasis.FieldIndex 3 =>
          (z : ℂ)^SMWeakWeightBasis.weakWeight i.1.1 *
          (w : ℂ)^SMWeakWeightBasis.weakWeight i.1.2)).coeff n := by
  rw [← Representation.char_iso
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 3 n)]
  exact ExteriorCharacterPolynomial.exterior_character _
    (SMWeakWeightBasis.fieldBasis 3) _ _ (lepton_basis_eigen flavor z w) n

/-- Four weak/Weyl weight pairs, each with three flavor copies. -/
theorem lepton_pair_generating (z w : Circle) :
    ExteriorCharacterPolynomial.generating
      (fun i : SMWeakWeightBasis.FieldIndex 3 =>
        (z : ℂ)^SMWeakWeightBasis.weakWeight i.1.1 *
        (w : ℂ)^SMWeakWeightBasis.weakWeight i.1.2) =
    (((1 + C ((z : ℂ)*(w : ℂ)) * X) *
      (1 + C ((z : ℂ)*(w : ℂ)⁻¹) * X)) *
      ((1 + C ((z : ℂ)⁻¹*(w : ℂ)) * X) *
      (1 + C ((z : ℂ)⁻¹*(w : ℂ)⁻¹) * X))) ^ 3 := by
  unfold ExteriorCharacterPolynomial.generating
  change (∏ i : (Fin 2 × Fin 2) × Fin 3,
    (1 + C ((z : ℂ)^SMWeakWeightBasis.weakWeight i.1.1 *
      (w : ℂ)^SMWeakWeightBasis.weakWeight i.1.2) * X)) = _
  simp only [Fintype.prod_prod_type]
  simp [SMWeakWeightBasis.weakWeight, Fin.prod_univ_two, ← mul_pow]

theorem lepton_character_product (n : ℕ) (z w : Circle) :
    (PatternExteriorSource.representation (DeltaLOneSignedFields.field flavor)
      (fun _ : Fin n => (3 : DeltaLOneSignedInput.Species))).character
        (leptonTorus z w) =
    ((((1 + C ((z : ℂ)*(w : ℂ)) * X) *
      (1 + C ((z : ℂ)*(w : ℂ)⁻¹) * X)) *
      ((1 + C ((z : ℂ)⁻¹*(w : ℂ)) * X) *
      (1 + C ((z : ℂ)⁻¹*(w : ℂ)⁻¹) * X))) ^ 3).coeff n :=
  (lepton_character flavor n z w).trans
    (congrArg (fun p : ℂ[X] => p.coeff n) (lepton_pair_generating z w))

end
end GUT.SMConstantSourceCharacter

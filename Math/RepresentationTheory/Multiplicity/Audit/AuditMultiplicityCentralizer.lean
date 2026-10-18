import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicityClassification
import Math.RepresentationTheory.Multiplicity.Audit.AuditIsometricMultiplicity

/-!
# Audits of the full U/SU multiplicity classification

All source models are constructed from actual unitary representations.
The weighted-sign check uses the actual Hilbert operator determinant, not
only the determinant of a separately defined block matrix.
-/

namespace Math.AuditMultiplicityCentralizer

noncomputable section

set_option backward.isDefEq.respectTransparency false

open HilbertMultiplicityOperator AuditIsometricMultiplicity

def trivialUnitaryClassification (d : ℕ) :=
  UnitaryMultiplicity.unitaryCentralizerEquiv (G := PUnit.{1}) (trivial d) (trivial_unitary d)

def trivialSpecialClassification (d : ℕ) :=
  UnitaryMultiplicity.specialCentralizerEquiv (G := PUnit.{1}) (trivial d) (trivial_unitary d)

example : Nonempty (UnitaryCentralizerTransport.unitaryCentralizer (G := PUnit.{1}) (trivial 0) ≃ₜ*
    UnitaryMultiplicity.unitaryFactors (G := PUnit.{1}) (trivial 0) (trivial_unitary 0)) :=
  ⟨trivialUnitaryClassification 0⟩

example : Nonempty (UnitaryCentralizerTransport.specialCentralizer (G := PUnit.{1}) (trivial 2) ≃ₜ*
    UnitaryMultiplicity.specialFactors (G := PUnit.{1}) (trivial 2) (trivial_unitary 2)) :=
  ⟨trivialSpecialClassification 2⟩

def permutationUnitaryClassification :=
  UnitaryMultiplicity.unitaryCentralizerEquiv permutation permutation_unitary

def permutationSpecialClassification :=
  UnitaryMultiplicity.specialCentralizerEquiv permutation permutation_unitary

section ArbitrarySource

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E) (h : UnitaryMultiplicity.IsUnitaryRepresentation rho)

example : Continuous ⇑(UnitaryMultiplicity.unitaryCentralizerEquiv rho h) :=
  (UnitaryMultiplicity.unitaryCentralizerEquiv rho h).continuous

example : Continuous ⇑(UnitaryMultiplicity.unitaryCentralizerEquiv rho h).symm :=
  (UnitaryMultiplicity.unitaryCentralizerEquiv rho h).symm.continuous

example : Continuous ⇑(UnitaryMultiplicity.specialCentralizerEquiv rho h) :=
  (UnitaryMultiplicity.specialCentralizerEquiv rho h).continuous

example : Continuous ⇑(UnitaryMultiplicity.specialCentralizerEquiv rho h).symm :=
  (UnitaryMultiplicity.specialCentralizerEquiv rho h).symm.continuous

end ArbitrarySource

local notation "m" => (fun _ : Fin 1 => 1)
local notation "S" => (fun _ : Fin 1 => EuclideanSpace ℂ (Fin 2))
local notation "A" => (fun _ : Fin 1 => (-1 : Matrix (Fin 1) (Fin 1) ℂ))

/-- The minus-identity multiplicity acts unitarily on the actual Hilbert sum. -/
theorem sign_operator_unitary : operator m S A ∈ unitary (Space m S →L[ℂ] Space m S) := by
  rw [operator_mem_unitary_iff]
  intro i
  simp [Matrix.mem_unitaryGroup_iff']

/-- The actual determinant is +1 because the constituent dimension is two. -/
theorem sign_operator_determinant : LinearMap.det (operator m S A).toLinearMap = 1 := by
  rw [det_operator]
  norm_num [Matrix.det_fin_one]

theorem sign_operator_ne_one : operator m S A ≠ 1 := by
  intro h
  have hA := operator_injective m S (h.trans (operator m S).map_one.symm)
  have h00 := congrArg (fun B : Matrices m => B 0 0 0) hA
  norm_num at h00

/-- The exponent cannot be replaced by one. -/
theorem unweighted_sign_determinant : (A 0).det ≠ 1 := by
  norm_num [Matrix.det_fin_one]

#print axioms HilbertMultiplicityOperator.operator_star
#print axioms HilbertMultiplicityOperator.operator_mem_unitary_iff
#print axioms HilbertMultiplicityOperator.det_operator
#print axioms MultiplicityUnitaryCentralizer.amplification_surjective
#print axioms MultiplicityUnitaryCentralizer.unitaryCentralizerEquiv
#print axioms MultiplicitySpecialCentralizer.determinant_unitaryMap
#print axioms MultiplicitySpecialCentralizer.specialCentralizerEquiv
#print axioms UnitaryMultiplicity.unitaryCentralizerEquiv
#print axioms UnitaryMultiplicity.specialCentralizerEquiv
#print axioms trivialUnitaryClassification
#print axioms trivialSpecialClassification
#print axioms permutationUnitaryClassification
#print axioms permutationSpecialClassification
#print axioms sign_operator_unitary
#print axioms sign_operator_determinant
#print axioms sign_operator_ne_one

end

end Math.AuditMultiplicityCentralizer

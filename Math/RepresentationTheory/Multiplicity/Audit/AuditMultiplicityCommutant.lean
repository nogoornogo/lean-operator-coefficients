import Math.RepresentationTheory.Multiplicity.CommutantCentralizer
import Math.RepresentationTheory.Multiplicity.MultiplicityMatrix
import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Audits for multiplicity commutants

Repeated trivial constituents admit the full matrix algebra, not only scalar
endomorphisms. The zero representation is allowed. Determinant audits retain
nontrivial finite solutions of the weighted SU condition.
-/

namespace Math.AuditMultiplicityCommutant

noncomputable section

open MultiplicityCommutant
open scoped MonoidAlgebra

def trivial (d : ℕ) : Representation ℂ PUnit (Fin d → ℂ) :=
  Representation.trivial ℂ PUnit (Fin d → ℂ)

def trivialModel (d : ℕ) : Model ℂ[PUnit] (trivial d).asModule :=
  (exists_representation_model (trivial d) inferInstance).some

def trivialEndEquiv (d : ℕ) :
    (trivial d).IntertwiningMap (trivial d) ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ) where
  toFun f := f.toLinearMap
  invFun f := ⟨f, by intro g; ext x; rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def trivialMatrixEquiv (d : ℕ) :
    (trivial d).IntertwiningMap (trivial d) ≃ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (trivialEndEquiv d).trans LinearMap.toMatrixAlgEquiv'

theorem repeated_commutant_finrank :
    Module.finrank ℂ ((trivial 2).IntertwiningMap (trivial 2)) = 4 := by
  rw [(trivialMatrixEquiv 2).toLinearEquiv.finrank_eq]
  simp [Module.finrank_matrix]

theorem repeated_noncommuting :
    ∃ f g : (trivial 2).IntertwiningMap (trivial 2), f * g ≠ g * f := by
  let e := trivialMatrixEquiv 2
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  refine ⟨e.symm A, e.symm B, ?_⟩
  intro h
  have hm := congrArg e h
  simp only [map_mul, AlgEquiv.apply_symm_apply] at hm
  have h00 := congrArg (fun M => M 0 0) hm
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem zero_commutant_finrank :
    Module.finrank ℂ ((trivial 0).IntertwiningMap (trivial 0)) = 0 := by
  rw [(trivialMatrixEquiv 0).toLinearEquiv.finrank_eq]
  simp [Module.finrank_matrix]

example : Model ℂ[PUnit] (trivial 0).asModule := trivialModel 0

example :
    CommutantCentralizer.linearCentralizer (trivial 2) ≃*
      Π c : isotypicComponents ℂ[PUnit] (trivial 2).asModule,
        (Matrix (Fin ((trivialModel 2).multiplicity c))
          (Fin ((trivialModel 2).multiplicity c)) ℂ)ˣ :=
  CommutantCentralizer.linearCentralizerEquiv (trivial 2) inferInstance (trivialModel 2)

/-- A nontrivial sign survives when the constituent dimension is even. -/
theorem weighted_determinant_retains_sign :
    (MultiplicityMatrix.amplify (fun _ : Fin 1 => 1) (fun _ => 2)
      (fun _ => (-1 : Matrix (Fin 1) (Fin 1) ℂ))).det = 1 := by
  rw [MultiplicityMatrix.det_amplify]
  norm_num [Matrix.det_fin_one]

/-- Dropping the exponent would wrongly discard this element. -/
theorem unweighted_determinant_rejects_sign :
    (-1 : Matrix (Fin 1) (Fin 1) ℂ).det ≠ 1 := by
  norm_num [Matrix.det_fin_one]

def signUnitary : Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨-1, by simp [Matrix.mem_unitaryGroup_iff']⟩

theorem sign_in_specialMultiplicityGroup :
    (fun _ : Fin 1 => signUnitary) ∈
      MultiplicityMatrix.specialMultiplicityGroup (fun _ => 1) (fun _ => 2) := by
  rw [MultiplicityMatrix.mem_specialMultiplicityGroup_iff]
  exact weighted_determinant_retains_sign

theorem signUnitary_ne_one : signUnitary ≠ 1 := by
  intro h
  apply unweighted_determinant_rejects_sign
  have hm := congrArg (fun u : Matrix.unitaryGroup (Fin 1) ℂ =>
    (u : Matrix (Fin 1) (Fin 1) ℂ).det) h
  simpa [signUnitary] using hm

/-- In this example the weighted SU kernel is exactly a two-element group. -/
theorem special_one_two_iff (A : Fin 1 → Matrix.unitaryGroup (Fin 1) ℂ) :
    A ∈ MultiplicityMatrix.specialMultiplicityGroup (fun _ => 1) (fun _ => 2) ↔
      A = (fun _ => 1) ∨ A = (fun _ => signUnitary) := by
  constructor
  · intro h
    have hd : (A 0 : Matrix (Fin 1) (Fin 1) ℂ).det ^ 2 = 1 := by
      simpa [MultiplicityMatrix.specialMultiplicityGroup, MultiplicityMatrix.weightedDet,
        MonoidHom.mem_ker] using h
    rcases sq_eq_one_iff.mp hd with hpos | hneg
    · left
      funext i
      fin_cases i
      apply Subtype.ext
      ext x y
      fin_cases x
      fin_cases y
      simpa [Matrix.det_fin_one] using hpos
    · right
      funext i
      fin_cases i
      apply Subtype.ext
      ext x y
      fin_cases x
      fin_cases y
      simpa [signUnitary, Matrix.det_fin_one] using hneg
  · rintro (rfl | rfl)
    · exact (MultiplicityMatrix.specialMultiplicityGroup _ _).one_mem
    · exact sign_in_specialMultiplicityGroup

example {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (rho : Representation ℂ G E)
    (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    Model ℂ[G] rho.asModule := UnitaryMultiplicity.multiplicityModel rho h

#print axioms exists_model
#print axioms Model.component_finrank
#print axioms Model.multiplicity_eq
#print axioms Model.endAlgEquiv
#print axioms commutantEquiv
#print axioms automorphismEquiv
#print axioms commutant_finrank
#print axioms CommutantCentralizer.linearCentralizerEquiv
#print axioms CommutantCentralizer.linearCentralizer_eq_groupCentralizer
#print axioms repeated_noncommuting
#print axioms zero_commutant_finrank
#print axioms MultiplicityMatrix.det_amplify
#print axioms MultiplicityMatrix.amplify_mem_unitary_iff
#print axioms MultiplicityMatrix.mem_specialMultiplicityGroup_iff
#print axioms MultiplicityMatrix.continuous_unitaryMap
#print axioms MultiplicityMatrix.unitaryMap_injective
#print axioms MultiplicityMatrix.isClosed_specialMultiplicityGroup
#print axioms weighted_determinant_retains_sign
#print axioms sign_in_specialMultiplicityGroup
#print axioms signUnitary_ne_one
#print axioms special_one_two_iff
#print axioms UnitaryMultiplicity.multiplicityModel
#print axioms UnitaryMultiplicity.linearCentralizerEquiv

end

end Math.AuditMultiplicityCommutant

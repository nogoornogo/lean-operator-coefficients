import Physics.StandardModel.Operators.Support.Quark.SMQExactCoordinates
import Math.LinearAlgebra.Constructions.GramNullityPolynomial

/-! A uniform exact polynomial formula for constant-Q local coefficients. -/
namespace Physics.SMQGaussianKernel
set_option autoImplicit false
noncomputable section
open Math Representation GaussianRational SMQExactCoordinates
open scoped BigOperators

/-- Explicit entries use only Gaussian-rational arithmetic, finite minors and
symmetric monomial coordinates; no actual complex kernel is an input. -/
def matrix (n m : ℕ) (delta : ℤ) :
    Matrix (SMRationalLocalKernel.Index n × Index n m) (Index n m) Scalar := fun ij k =>
  actionMatrix n m delta (SMGaussianLocalData.data n ij.1) k ij.2 - if k=ij.2 then 1 else 0

def polynomial (n m : ℕ) (delta : ℤ) : Polynomial Scalar :=
  GaussianRational.gramPolynomial (matrix n m delta)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

local instance carrierFinite (n m : ℕ) : FiniteDimensional ℂ
    (SMFullLocalKernel.Carrier flavor (pattern n) m) := Module.Finite.of_basis (basis flavor n m)

theorem matrix_semantics (n m : ℕ) (delta : ℤ) : (matrix n m delta).map embed =
    FiniteInvariantKernel.matrix (SMIntegralLocalWeights.action flavor (pattern n) m delta)
      (basis flavor n m) (SMRationalLocalKernel.tests n) := by
  ext ij k
  simp only [matrix, Matrix.map_apply, FiniteInvariantKernel.matrix, map_sub]
  rw [action_sample_coordinate]
  congr 1
  split_ifs <;> simp only [map_one,map_zero]

theorem coefficient_dimension (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern n) m delta)) =
        (polynomial n m delta).natTrailingDegree := by
  have e := FiniteInvariantKernel.equiv
    (SMIntegralLocalWeights.action flavor (pattern n) m delta) (basis flavor n m)
      (SMRationalLocalKernel.tests n) (SMRationalLocalKernel.exhaustive flavor (pattern n) m delta)
  have hd := GramNullityPolynomial.nullity ((matrix n m delta).map embed)
  have hp := congrArg Polynomial.natTrailingDegree (GaussianRational.gramPolynomial_map (matrix n m delta))
  have hdeg : ((GaussianRational.gramPolynomial (matrix n m delta)).map embed.toRingHom).natTrailingDegree =
      (polynomial n m delta).natTrailingDegree := GaussianRational.natTrailingDegree_map _
  exact e.finrank_eq.trans
    ((congrArg (fun A : Matrix (SMRationalLocalKernel.Index n × Index n m) (Index n m) ℂ =>
      Module.finrank ℂ (LinearMap.ker A.mulVecLin)) (matrix_semantics flavor n m delta).symm).trans
        (hd.trans (hp.symm.trans hdeg)))

/-- Actual local support is a finite exact polynomial coefficient test. -/
theorem allowed_iff (n m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern n) m delta)) ↔
        (polynomial n m delta).coeff 0 = 0 := by
  rw [SelectionCriteria.Allowed, ← Module.finrank_pos_iff_exists_ne_zero (R := ℂ),
    Nat.pos_iff_ne_zero, coefficient_dimension, Polynomial.natTrailingDegree_ne_zero]
  exact and_iff_right (Matrix.charpoly_monic _).ne_zero

theorem kernel_dimension (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern n) m delta) =
      (polynomial n m delta).natTrailingDegree :=
  (SMFullLocalKernel.coefficientEquiv flavor (pattern n) m delta).finrank_eq.symm.trans
    (coefficient_dimension flavor n m delta)

theorem rank_add_nullity (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern n) m delta)) +
      (polynomial n m delta).natTrailingDegree = SMConstantContentRanks.columns 0 n m := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (SMFullLocalKernel.constraints flavor (pattern n) m delta)
  have hd : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern n) m)) → ℂ) =
      SMConstantContentRanks.columns 0 n m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact SMConstantContentRanks.carrier_dimension flavor 0 n m
  have hk := kernel_dimension flavor n m delta
  exact (congrArg (fun k : ℕ => Module.finrank ℂ (LinearMap.range
      (SMFullLocalKernel.constraints flavor (pattern n) m delta)) + k) hk).symm.trans (h.trans hd)

theorem nullity_above_capacity (n m : ℕ) (delta : ℤ) (hn : 36 < n) :
    (polynomial n m delta).natTrailingDegree = 0 := by
  have h := rank_add_nullity LLHHKernelRank.flavor n m delta
  have hc : SMConstantContentRanks.columns 0 n m = 0 := by
    simp [SMConstantContentRanks.columns, SMConstantContentRanks.dimension, Nat.choose_eq_zero_of_lt hn]
  exact (Nat.add_eq_zero_iff.mp (h.trans hc)).2

theorem forbidden_odd (n m : ℕ) (delta : ℤ) (hn : n % 2 ≠ 0) :
    (polynomial n m delta).coeff 0 ≠ 0 := by
  intro h
  exact ((SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMParityKernelRank.forbidden LLHHKernelRank.flavor (pattern n) m delta hn))
      ((allowed_iff LLHHKernelRank.flavor n m delta).mpr h)

theorem forbidden_charged (n m : ℕ) (delta : ℤ) (hn : (n : ℤ)+3*delta ≠ 0) :
    (polynomial n m delta).coeff 0 ≠ 0 := by
  intro h
  have hq := SMChargedKernelRank.local_charge LLHHKernelRank.flavor (pattern n) m delta
    ((allowed_iff LLHHKernelRank.flavor n m delta).mpr h)
  apply hn
  simpa [SMContentWeakBound.hypercharge, pattern, SMConstantContentRanks.pattern,
    DeltaLOneSignedInput.hypercharge] using hq

end
end Physics.SMQGaussianKernel

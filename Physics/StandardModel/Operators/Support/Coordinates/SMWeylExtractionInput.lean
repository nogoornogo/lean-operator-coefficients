import Math.RepresentationTheory.Characters.CompactWeylExtraction
import Physics.StandardModel.Operators.Support.Coordinates.SMIteratedContent
import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactCoefficients

/-! Conditional literature extraction to actual local SM kernels. Compact
comparison, continuity and character presentation remain separate inputs. -/
namespace Physics.SMWeylExtractionInput
set_option autoImplicit false
noncomputable section
open Math Representation CompactWeylExtraction ContinuousRepresentationScope
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)
  {K T L V : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [Group T] [AddCommGroup L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ K V) (torus : T →* K) (monomial : L → T → ℂ) (roots : List L)
  (comparison : InvariantCoefficientTransport.Invariants rho ≃ₗ[ℂ]
    SMMixedCompactCoefficients.LocalSpace flavor p m delta)
  (hr : IsJointlyContinuous rho) (input : TorusReduction rho torus monomial roots)
  (P : L →₀ ℤ) (hp : Presents rho torus monomial P)

include comparison hr input hp
/-- The only external mathematical premise is `input`. The compact comparison,
continuity and character identity are independent application obligations. -/
theorem kernel_dimension_int :
    (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) : ℤ) = constantTerm roots P := by
  have hc := CompactWeylExtraction.coefficient_dimension rho torus monomial roots hr input P hp
  have he := (comparison.trans (SMMixedCompactCoefficients.kernelEquiv flavor p m delta)).finrank_eq
  rwa [he] at hc

theorem multiplicity_nonnegative : 0 ≤ constantTerm roots P := by
  rw [← kernel_dimension_int flavor p m delta rho torus monomial roots comparison hr input P hp]
  exact Int.natCast_nonneg _

theorem kernel_dimension : Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) =
    (constantTerm roots P).toNat := by
  have hd := kernel_dimension_int flavor p m delta rho torus monomial roots comparison hr input P hp
  simpa only [Int.toNat_natCast] using congrArg Int.toNat hd

theorem multiplicity_le_columns : (constantTerm roots P).toNat ≤ SMIteratedContent.columns p m := by
  have hn := SMIteratedContent.rank_add_nullity flavor p m delta
  have hk := kernel_dimension flavor p m delta rho torus monomial roots comparison hr input P hp
  omega

theorem rank_formula : Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
    SMIteratedContent.columns p m - (constantTerm roots P).toNat := by
  have hn := SMIteratedContent.rank_add_nullity flavor p m delta
  have hk := kernel_dimension flavor p m delta rho torus monomial roots comparison hr input P hp
  omega

/-- Local support only: arbitrary residual invariance is not silently removed. -/
theorem local_allowed_iff : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor p m delta)) ↔ 0 < constantTerm roots P := by
  rw [SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor p m delta)]
  have hd := kernel_dimension_int flavor p m delta rho torus monomial roots comparison hr input P hp
  have ha : SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor p m delta) ↔
      0 < (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) : ℤ) := by
    simp only [Int.natCast_pos,Module.finrank_pos_iff_exists_ne_zero,SelectionCriteria.Allowed]
  exact ha.trans ((congrArg (fun z : ℤ => 0 < z) hd).to_iff)

end
end Physics.SMWeylExtractionInput

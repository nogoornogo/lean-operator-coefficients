import Math.RepresentationTheory.Characters.CompactHomDimension
import Math.RepresentationTheory.Decomposition.SemisimpleSplitting
import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import TauCeti.RepresentationTheory.Compact.UnitaryModel
import TauCeti.RepresentationTheory.Continuous.OrthogonalDecomposition
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.Interval.Set.Infinite
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Persistent API probes: the counting bridge really accepts an infinite group. -/

namespace Math.CompactResidualAPIAudit

/-- Compactness plus continuity supplies a unitary model; H-unitarity need not
be postulated on the original source. Transport back remains a consumer task. -/
theorem exists_unitary_model {H V : Type*}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ H V)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho) :
    ∃ e : V ≃L[ℂ] V, ContRepresentation.IsUnitary
      (ContinuousLinearEquiv.congr e (CompactHomDimension.asContinuous rho)) :=
  ContRepresentation.exists_isUnitary_congr _
    (CompactHomDimension.continuous_asContinuous rho hr)

theorem circle_infinite : Infinite Circle := by
  let : Infinite (Set.Ioc (-Real.pi) Real.pi) :=
    Set.Ioc.infinite (neg_lt_self Real.pi_pos)
  exact Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective

noncomputable local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

theorem circle_counting {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ Circle V) (sigma : Representation ℂ Circle W)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
    (hs : ContinuousRepresentationScope.IsJointlyContinuous sigma) :
    (∫ h, rho.character h⁻¹ * sigma.character h ∂TauCeti.haarProb Circle) =
      (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) :=
  CompactHomDimension.integral_character_mul_eq_finrank rho sigma hr hs

end Math.CompactResidualAPIAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Compact residual API imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.CompactHomDimension.asContinuous_toRepresentation,
    ``Math.CompactHomDimension.continuous_asContinuous,
    ``Math.CompactHomDimension.integral_character_mul_eq_finrank,
    ``Math.CompactHomDimension.integrable_character_mul,
    ``Math.CompactHomDimension.hom_finrank_add,
    ``Math.SemisimpleSplitting.exists_split,
    ``Math.SemisimpleSplitting.exists_split_of_unitary,
    ``Math.FiniteSemisimpleDecomposition.exists_decomposition,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.subrepresentation,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.comp,
    ``Math.CompactResidualAPIAudit.exists_unitary_model,
    ``ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition_of_congr,
    ``Math.CompactResidualAPIAudit.circle_infinite,
    ``Math.CompactResidualAPIAudit.circle_counting]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Compact residual API: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Compact residual API: layer and {declarations.length} strict axiom checks passed"

import Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace Physics.CompactLightQqueAudit

open ContinuousRepresentationScope

theorem continuous_discrete_action {H V : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ H V) : IsJointlyContinuous rho := by
  have hc : Continuous (CompactHomDimension.asContinuous rho) := continuous_of_discreteTopology
  exact (hc.comp continuous_fst).clm_apply continuous_snd

/-- The compact endpoint recovers the finite/discrete case without continuity
certificates. The old purely algebraic finite theorem remains unchanged. -/
theorem finite_recovery {H G E : Type*} [Group H] [Fintype H]
    [TopologicalSpace H] [DiscreteTopology H] [IsTopologicalGroup H] [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℂ (F s)]
    [FiniteDimensional ℂ (F 0)] [Nontrivial (F 0)]
    (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
    (B : InvariantWeylMass.SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ f : Representation.IntertwiningMap
      (NonabelianLightOperators.qqueRepresentation j rho B 0 3 8 14)
      (Representation.trivial ℂ H ℂ), f ≠ 0 :=
  CompactLightQque.exists_qque_coefficient j rho B hu P
    (continuous_discrete_action _) (continuous_discrete_action _) ht c

end Physics.CompactLightQqueAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Compact light qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.CompactResidualLightQuotient.exists_split_of_index_eq,
    ``Physics.CompactResidualLightQuotient.exists_common_quotient,
    ``Physics.CompactLightQque.radical_residual_continuous,
    ``Physics.CompactLightQque.common_quotient,
    ``Physics.CompactLightQque.exists_qque_coefficient,
    ``Physics.CompactLightQque.not_forbidsBothInternalCoefficients,
    ``Physics.CompactLightQqueAudit.continuous_discrete_action,
    ``Physics.CompactLightQqueAudit.finite_recovery]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Compact light qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Compact light qque: layer and {declarations.length} strict axiom checks passed"

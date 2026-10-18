import GUT.SU6.SelectionRules.Benchmarks.ConcreteDiracBenchmark

/-!
# Non-vacuity and axiom audit of the concrete Dirac benchmark

The complete model is constructed, not supplied as a hypothesis. Its strict
residual action and mass map are trivial, but its signed SM generation index
is one. It may contain vectorlike zero modes. No nonzero mass, exact full SM
zero-mode spectrum, or proton-decay amplitude is claimed.

The concrete constructors also guard against accidental polymorphic `rep`
fields caused by unresolved names under `autoImplicit`.
-/

set_option autoImplicit false

#print axioms GUT.ConcreteStandardGeometry.blocks
#print axioms GUT.ConcreteStandardGeometry.hypercharge_injective
#print axioms GUT.ConcreteStandardGeometry.geometry
#print axioms GUT.ConcreteStandardGeometry.hyperchargePair_eq_standard
#print axioms GUT.ConcreteDiracBenchmark.neutralAction
#print axioms GUT.ConcreteDiracBenchmark.matter
#print axioms GUT.ConcreteDiracBenchmark.blockCharacter_eq_one_of_trivial
#print axioms GUT.ConcreteDiracBenchmark.ordinaryChargedSource_neutral
#print axioms GUT.ConcreteDiracBenchmark.matter_restrictedCharacter
#print axioms GUT.ConcreteDiracBenchmark.matter_resolvedCharacter
#print axioms GUT.ConcreteDiracBenchmark.mass_hasExactSMChiralIndex
#print axioms GUT.ConcreteDiracBenchmark.model
#print axioms GUT.ConcreteDiracBenchmark.model_generations
#print axioms GUT.ConcreteDiracBenchmark.model_massMap_eq_zero
#print axioms GUT.ConcreteDiracBenchmark.exists_one_generation_model
#print axioms GUT.ConcreteDiracBenchmark.model_not_forbidsEverySupportedPhysicalDeltaBOneOperator

namespace GUT.AuditConcreteDiracBenchmark

open ConcreteDiracBenchmark

example : ∃ M : DiracPhysicalModel.ContinuousDiracYukawaModel PUnit,
    M.generations = 1 :=
  exists_one_generation_model PUnit

example : ∃ M : DiracPhysicalModel.ContinuousDiracYukawaModel (Multiplicative (ZMod 2)),
    M.generations = 1 :=
  exists_one_generation_model (Multiplicative (ZMod 2))

example (H : Type*) [CommGroup H] :
    Nonempty (StandardBlockGaugeCancellation.CommonGaugeSummand H
      (1 : H →* CompactEmbeddingClassification.SU6)) :=
  ⟨{ coeff := 1
     rep := ConcreteSU6Representations.fundamental
     twisted := FiniteResidualActionFactorization.GaugeTwistedAction.ofCommuting
       (neutralAction ConcreteSU6Representations.fundamental)
     gauge_eq := rfl }⟩

end GUT.AuditConcreteDiracBenchmark

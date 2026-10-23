import GUT.Common.StandardChain.ConjugationAdapter
import GUT.SU5.SelectionRules.StandardChainBenchmark
import Lean.Util.CollectAxioms

open Physics

open Math

/-! Positive control: actual SU(5) representatives, unchanged arbitrary mass
data, and the nonempty 15-dimensional standard-chain benchmark. -/

set_option autoImplicit false

namespace GUT.StandardChainConjugation.Audit
open SU5 StandardModelEmbedding StandardChain FiniteAbelianChargeSectors

section
variable {G H E : Type*} [Group G] [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E} (M : Model i rho)

example : (mass M).form = M.mass.form := rfl
example : (mass M).radical.toSubmodule = M.mass.radical.toSubmodule := rfl
example : StructuralConjugationMass.spectrum (i.comp MaximalTorus.hom)
    rho M.unitary (mass M) = M.lightSpectrum := spectrum_eq M

example [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace H] [IsTopologicalGroup H] (N : ContinuousModel i rho) :
    Continuous (fun p : (G × H) × E => rho p.1 p.2) ∧
      ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
        N.toModel.lightSpectrum :=
  ⟨N.action_continuous, continuous_selection_rule_obstruction N⟩
end

theorem finite_benchmark (q r : ChargeLabel (Multiplicative (ZMod 3))) :
    Module.finrank ℂ (StandardChainBenchmark.model q r).mass.radical.toSubmodule = 15 ∧
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (StandardChainBenchmark.model q r).lightSpectrum :=
  ⟨StandardChainBenchmark.radical_finrank q r,
    selection_rule_obstruction (StandardChainBenchmark.model q r)⟩

end GUT.StandardChainConjugation.Audit

run_cmd do
  let declarations := [
    ``GUT.StandardChainConjugation.realizes,
    ``GUT.StandardChainConjugation.threeConjugations,
    ``GUT.StandardChainConjugation.restrict_eq,
    ``GUT.StandardChainConjugation.mass,
    ``GUT.StandardChainConjugation.mass_eq,
    ``GUT.StandardChainConjugation.hasTarget,
    ``GUT.StandardChainConjugation.spectrum_eq,
    ``GUT.StandardChainConjugation.profiles_compatible,
    ``GUT.StandardChainConjugation.actual_signature_pair,
    ``GUT.StandardChainConjugation.selection_rule_obstruction,
    ``GUT.StandardChainConjugation.continuous_selection_rule_obstruction,
    ``GUT.StandardChainConjugation.Audit.finite_benchmark]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugation adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugation adapter: {declarations.length} strict transitive axiom checks passed"

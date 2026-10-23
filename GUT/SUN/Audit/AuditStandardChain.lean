import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.Audit.AuditBlock
import GUT.SUN.SelectionRules.RankSevenBenchmark

open Physics

open Math

/-! Universal standard-block theorem, exact rank-five recovery, and an
actual rank-seven positive-target model. No transitive SU(6) source import
is permitted; the rank-six comparison has its own legacy-side audit. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(n) standard-chain audit imports SU(6): {mod}"

namespace GUT.SUN.AuditStandardChain


noncomputable section

/-- A nontrivial finite residual group is allowed, but acts neutrally on
this particular benchmark. Nontrivial charged examples live in the SU(5) audit. -/
def rankSeven := RankSevenBenchmark.model (Multiplicative (ZMod 3))

theorem positive_example :
    rankSeven.profile.generations = 1 ∧
      Module.finrank ℂ rankSeven.mass.radical.toSubmodule = 42 ∧
      ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
        rankSeven.lightSpectrum :=
  ⟨rfl, RankSevenBenchmark.radical_finrank _, rankSeven.selection_rule_obstruction⟩

def continuousRankSeven := RankSevenBenchmark.continuousModel Circle

#print axioms StandardChain.rank_five_inclusion
#print axioms StandardChain.rank_five_pullback
#print axioms StandardChain.selection_rule_obstruction
#print axioms StandardChain.continuousModel
#print axioms DiagonalCharacter.fundamental_character
#print axioms DiagonalCharacter.dual_character
#print axioms DiagonalCharacter.wedge_character
#print axioms DiagonalCharacter.entries_product
#print axioms DiagonalCharacter.inclusion_diagonal
#print axioms RankSeven.pairFiveEquiv
#print axioms RankSeven.pairSevenEquiv
#print axioms RankSeven.wedge_restriction
#print axioms RankSeven.dual_restriction
#print axioms RankSevenBenchmark.ambient_unitary
#print axioms RankSevenBenchmark.ambient_continuous
#print axioms RankSevenBenchmark.ambient_character
#print axioms RankSevenBenchmark.restricted_index
#print axioms RankSevenBenchmark.hasTarget
#print axioms RankSevenBenchmark.model
#print axioms RankSevenBenchmark.continuousModel
#print axioms RankSevenBenchmark.finrank_space
#print axioms RankSevenBenchmark.radical_finrank
#print axioms RankSevenBenchmark.nonvacuous
#print axioms positive_example
#print axioms continuousRankSeven

end

end GUT.SUN.AuditStandardChain

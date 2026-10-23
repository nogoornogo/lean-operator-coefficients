import Math.Audit.ImportOrigin
import GUT.Common.Chirality.SelfDualSource
import GUT.SU5.SelectionRules.StandardChainBenchmark
import Physics.StandardModel.Spectrum.Representations.Audit.AuditSelfDualChirality

open Physics

open Math

/-! Physical-torus evaluator compatibility and an actual positive-target
source that the new obstruction correctly proves is not gauge-self-dual. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Self-dual standard-chain adapter imports SU(6): {mod}"

namespace GUT.AuditSelfDualSource

noncomputable section

open StandardChain SelfDualSource SU5 StandardChainBenchmark
open FiniteAbelianChargeSectors AuditFiniteChargeProfiles

theorem actual_benchmark_not_self_dual {H : Type*} [CommGroup H]
    (q r : ChargeLabel H) :
    ¬ Nonempty (Representation.Equiv (gauge (rho q r)) (gauge (rho q r)).dual) := by
  rintro ⟨e⟩
  exact not_model_of_gauge_selfDual (model q r) e

theorem order_two_benchmark_control :
    ¬ Nonempty (Representation.Equiv
      (gauge (rho (cyclicLabels 2 1) (0 : ChargeLabel (Multiplicative (ZMod 2)))))
      (gauge (rho (cyclicLabels 2 1) (0 : ChargeLabel (Multiplicative (ZMod 2))))).dual) :=
  actual_benchmark_not_self_dual _ _

#print axioms gaugeWeight_injective
#print axioms evaluate_forgetCharges
#print axioms not_model_of_gauge_character
#print axioms not_model_of_gauge_selfDual
#print axioms not_model_of_inverse_conjugacy
#print axioms actual_benchmark_not_self_dual
#print axioms order_two_benchmark_control

end

end GUT.AuditSelfDualSource

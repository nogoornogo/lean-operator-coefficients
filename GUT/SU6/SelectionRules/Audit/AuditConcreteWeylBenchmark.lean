import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylBenchmark

open Physics

/-!
# Non-vacuity audit of the standard Weyl model

The generation-one certificate is constructed without a supplied spectrum
hypothesis. All matter coefficients are nonnegative. The explicit zero mass
retains twenty-seven zero modes, not a pure SM-only light spectrum.
-/

set_option autoImplicit false

namespace GUT.AuditConcreteWeylBenchmark

open ConcreteWeylBenchmark
open StandardWeylMassSource (StandardWeylModel)

example : ∃ M : StandardWeylModel PUnit.{1}, M.generations = 1 :=
  exists_one_generation_model PUnit.{1}

example : ∃ M : StandardWeylModel (Multiplicative (ZMod 2)), M.generations = 1 :=
  exists_one_generation_model (Multiplicative (ZMod 2))

example : (model (Multiplicative (ZMod 2))).mass.form = 0 := model_mass_zero

example :
    StandardBranchProtonObstruction.protonFirst (model PUnit.{1}).charges = 0 ∧
      StandardBranchProtonObstruction.protonSecond (model PUnit.{1}).charges = 0 :=
  (model PUnit.{1}).proton_functionals_eq_zero

#print axioms matter_nonnegative
#print axioms chargedSource_neutral
#print axioms source_character_neutral
#print axioms fields_character
#print axioms antifundamental_character_eq_inverse
#print axioms neutral_target_eval
#print axioms fields_dual_character
#print axioms mass_hasDualSMTarget
#print axioms model
#print axioms model_mass_zero
#print axioms fields_finrank
#print axioms model_radical_finrank
#print axioms exists_one_generation_model

end GUT.AuditConcreteWeylBenchmark

import Physics.StandardModel.Operators.Selection.KorenSMSelection
import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.KorenSMSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.KorenSMSelection.H => Physics.KorenSMSelection.H,
  GUT.KorenSMSelection.all_forbidden => Physics.KorenSMSelection.all_forbidden,
  GUT.KorenSMSelection.baryon_divisible => Physics.KorenSMSelection.baryon_divisible,
  GUT.KorenSMSelection.chi => Physics.KorenSMSelection.chi,
  GUT.KorenSMSelection.chi.eq_1 => Physics.KorenSMSelection.chi.eq_1,
  GUT.KorenSMSelection.chi_mul => Physics.KorenSMSelection.chi_mul,
  GUT.KorenSMSelection.chi_restriction => Physics.KorenSMSelection.chi_restriction,
  GUT.KorenSMSelection.copies => Physics.KorenSMSelection.copies,
  GUT.KorenSMSelection.detect => Physics.KorenSMSelection.detect,
  GUT.KorenSMSelection.embedding => Physics.KorenSMSelection.embedding,
  GUT.KorenSMSelection.embedding_injective => Physics.KorenSMSelection.embedding_injective,
  GUT.KorenSMSelection.fermion_conjugates => Physics.KorenSMSelection.fermion_conjugates,
  GUT.KorenSMSelection.flavor => Physics.KorenSMSelection.flavor,
  GUT.KorenSMSelection.higgs_neutral => Physics.KorenSMSelection.higgs_neutral,
  GUT.KorenSMSelection.llhh_detect => Physics.KorenSMSelection.llhh_detect,
  GUT.KorenSMSelection.neutral_iff => Physics.KorenSMSelection.neutral_iff,
  GUT.KorenSMSelection.printed_dictionary => Physics.KorenSMSelection.printed_dictionary,
  GUT.KorenSMSelection.residual_forbidden => Physics.KorenSMSelection.residual_forbidden,
  GUT.KorenSMSelection.scalarFlavor => Physics.KorenSMSelection.scalarFlavor,
  GUT.KorenSMSelection.target => Physics.KorenSMSelection.target,
  GUT.KorenSMSelection.target_union => Physics.KorenSMSelection.target_union
]

assert_compatible GUT.KorenSMSelection.H => Physics.KorenSMSelection.H
assert_compatible GUT.KorenSMSelection.all_forbidden => Physics.KorenSMSelection.all_forbidden
assert_compatible GUT.KorenSMSelection.baryon_divisible => Physics.KorenSMSelection.baryon_divisible
assert_compatible GUT.KorenSMSelection.chi => Physics.KorenSMSelection.chi
assert_compatible GUT.KorenSMSelection.chi.eq_1 => Physics.KorenSMSelection.chi.eq_1
assert_compatible GUT.KorenSMSelection.chi_mul => Physics.KorenSMSelection.chi_mul
assert_compatible GUT.KorenSMSelection.chi_restriction => Physics.KorenSMSelection.chi_restriction
assert_compatible GUT.KorenSMSelection.copies => Physics.KorenSMSelection.copies
assert_compatible GUT.KorenSMSelection.detect => Physics.KorenSMSelection.detect
assert_compatible GUT.KorenSMSelection.embedding => Physics.KorenSMSelection.embedding
assert_compatible GUT.KorenSMSelection.embedding_injective => Physics.KorenSMSelection.embedding_injective
assert_compatible GUT.KorenSMSelection.fermion_conjugates => Physics.KorenSMSelection.fermion_conjugates
assert_compatible GUT.KorenSMSelection.flavor => Physics.KorenSMSelection.flavor
assert_compatible GUT.KorenSMSelection.higgs_neutral => Physics.KorenSMSelection.higgs_neutral
assert_compatible GUT.KorenSMSelection.llhh_detect => Physics.KorenSMSelection.llhh_detect
assert_compatible GUT.KorenSMSelection.neutral_iff => Physics.KorenSMSelection.neutral_iff
assert_compatible GUT.KorenSMSelection.printed_dictionary => Physics.KorenSMSelection.printed_dictionary
assert_compatible GUT.KorenSMSelection.residual_forbidden => Physics.KorenSMSelection.residual_forbidden
assert_compatible GUT.KorenSMSelection.scalarFlavor => Physics.KorenSMSelection.scalarFlavor
assert_compatible GUT.KorenSMSelection.target => Physics.KorenSMSelection.target
assert_compatible GUT.KorenSMSelection.target_union => Physics.KorenSMSelection.target_union

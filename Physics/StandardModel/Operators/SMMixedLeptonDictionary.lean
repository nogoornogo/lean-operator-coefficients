import Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonDictionary
import Physics.StandardModel.Operators.SMContentCapacity
import Physics.StandardModel.Operators.SMChiralitySupport
import Math.RepresentationTheory.BinaryPatternExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonDictionary instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMChiralitySupport.slotCount.eq_1 => Physics.SMChiralitySupport.slotCount.eq_1,
  GUT.SMMixedLeptonDictionary.capacity => Physics.SMMixedLeptonDictionary.capacity,
  GUT.SMMixedLeptonDictionary.chirality => Physics.SMMixedLeptonDictionary.chirality,
  GUT.SMMixedLeptonDictionary.counts => Physics.SMMixedLeptonDictionary.counts,
  GUT.SMMixedLeptonDictionary.fits => Physics.SMMixedLeptonDictionary.fits,
  GUT.SMMixedLeptonDictionary.hypercharge => Physics.SMMixedLeptonDictionary.hypercharge,
  GUT.SMMixedLeptonDictionary.pattern => Physics.SMMixedLeptonDictionary.pattern,
  GUT.SMMixedLeptonDictionary.raw_bound => Physics.SMMixedLeptonDictionary.raw_bound,
  GUT.SMMixedLeptonDictionary.residual => Physics.SMMixedLeptonDictionary.residual,
  GUT.SMMixedLeptonDictionary.sharp_bound => Physics.SMMixedLeptonDictionary.sharp_bound,
  GUT.SMMixedWeakCapacity.bound.eq_1 => Physics.SMMixedWeakCapacity.bound.eq_1,
  GUT.SMMixedWeakCapacity.speciesBound.eq_1 => Physics.SMMixedWeakCapacity.speciesBound.eq_1
]

assert_compatible GUT.SMChiralitySupport.slotCount.eq_1 => Physics.SMChiralitySupport.slotCount.eq_1
assert_compatible GUT.SMMixedLeptonDictionary.capacity => Physics.SMMixedLeptonDictionary.capacity
assert_compatible GUT.SMMixedLeptonDictionary.chirality => Physics.SMMixedLeptonDictionary.chirality
assert_compatible GUT.SMMixedLeptonDictionary.counts => Physics.SMMixedLeptonDictionary.counts
assert_compatible GUT.SMMixedLeptonDictionary.fits => Physics.SMMixedLeptonDictionary.fits
assert_compatible GUT.SMMixedLeptonDictionary.hypercharge => Physics.SMMixedLeptonDictionary.hypercharge
assert_compatible GUT.SMMixedLeptonDictionary.pattern => Physics.SMMixedLeptonDictionary.pattern
assert_compatible GUT.SMMixedLeptonDictionary.raw_bound => Physics.SMMixedLeptonDictionary.raw_bound
assert_compatible GUT.SMMixedLeptonDictionary.residual => Physics.SMMixedLeptonDictionary.residual
assert_compatible GUT.SMMixedLeptonDictionary.sharp_bound => Physics.SMMixedLeptonDictionary.sharp_bound
assert_compatible GUT.SMMixedWeakCapacity.bound.eq_1 => Physics.SMMixedWeakCapacity.bound.eq_1
assert_compatible GUT.SMMixedWeakCapacity.speciesBound.eq_1 => Physics.SMMixedWeakCapacity.speciesBound.eq_1

import GUT.SU6.Embeddings.StandardSUNCompatibility
import GUT.SU6.SelectionRules.Models.CanonicalChainModel

/-! The arbitrary-rank construction agrees with the actual SU(6) block
and physical torus, while the old source/mass/spectrum adapter is retained. -/

#print axioms GUT.SU6.StandardSUNCompatibility.inclusion_eq
#print axioms GUT.SU6.StandardSUNCompatibility.torus_eq
#print axioms GUT.SU6.CanonicalChainModel.model
#print axioms GUT.SU6.CanonicalChainModel.mass_compatible
#print axioms GUT.SU6.CanonicalChainModel.spectrum_compatible
#print axioms GUT.SU6.CanonicalChainModel.selection_rule_obstruction

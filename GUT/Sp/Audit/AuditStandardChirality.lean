import Math.Audit.ImportOrigin
import GUT.Sp.StandardChirality
import GUT.Common.Chirality.Audit.AuditSelfDualSource

open Math

/-! SP-1 chosen-chain specialization, with the existing torsion-charge,
zero-generation, singlet, vectorlike, and non-self-dual SU(5) controls. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Symplectic standard-chain adapter imports SU(6): {mod}"

namespace GUT.CompactSymplectic.StandardChirality

open Math.CompactSymplectic
theorem rank_five_block : blockInclusion 0 = inclusion := by
  unfold blockInclusion
  rw [SUN.Block.inclusion_zero]
  rfl

#print axioms inclusion_injective
#print axioms inclusion_continuous
#print axioms inclusion_torus
#print axioms inclusion_torus_inverse
#print axioms not_model
#print axioms blockInclusion_injective
#print axioms blockInclusion_continuous
#print axioms blockInclusion_torus
#print axioms blockInclusion_torus_inverse
#print axioms not_block_model
#print axioms not_arbitrary_model
#print axioms rank_five_block

end GUT.CompactSymplectic.StandardChirality

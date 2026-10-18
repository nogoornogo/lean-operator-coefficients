import Physics.FieldTheory.Mass.DiracWeylConvention

/-!
# Audit of the Dirac mass and all-left-handed convention bridge

The group is arbitrary, so the statements retain both gauge and residual
actions. These are off-diagonal Dirac bilinears, not general Majorana masses.
-/

#print axioms GUT.DiracWeylConvention.massBilinear
#print axioms GUT.DiracWeylConvention.massBilinear_isSymm
#print axioms GUT.DiracWeylConvention.mem_radical_iff
#print axioms GUT.DiracWeylConvention.radical_eq_ker_prod_annihilator
#print axioms GUT.DiracWeylConvention.massBilinear_invariant
#print axioms GUT.DiracWeylConvention.radicalSubrepresentation
#print axioms GUT.DiracWeylConvention.annihilatorSubrepresentation
#print axioms GUT.DiracWeylConvention.radicalLinearEquiv
#print axioms GUT.DiracWeylConvention.radicalDecompositionEquiv
#print axioms GUT.DiracWeylConvention.annihilatorComplementRepresentationEquiv
#print axioms GUT.DiracWeylConvention.allLeft_dual_character_eq_signed_antisymmetrization
#print axioms GUT.DiracWeylConvention.radical_character_eq_kernel_add_dual_cokernel
#print axioms GUT.DiracWeylConvention.radical_dual_character_eq_lightIndex_antisymmetrization
#print axioms GUT.DiracWeylConvention.radical_dual_character_eq_allLeft_dual_character

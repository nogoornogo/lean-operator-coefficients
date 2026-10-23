import Physics.FieldTheory.Mass.Algebra.DiracWeylConvention

open Physics

/-!
# Audit of the Dirac mass and all-left-handed convention bridge

The group is arbitrary, so the statements retain both gauge and residual
actions. These are off-diagonal Dirac bilinears, not general Majorana masses.
-/

#print axioms Physics.DiracWeylConvention.massBilinear
#print axioms Physics.DiracWeylConvention.massBilinear_isSymm
#print axioms Physics.DiracWeylConvention.mem_radical_iff
#print axioms Physics.DiracWeylConvention.radical_eq_ker_prod_annihilator
#print axioms Physics.DiracWeylConvention.massBilinear_invariant
#print axioms Physics.DiracWeylConvention.radicalSubrepresentation
#print axioms Physics.DiracWeylConvention.annihilatorSubrepresentation
#print axioms Physics.DiracWeylConvention.radicalLinearEquiv
#print axioms Physics.DiracWeylConvention.radicalDecompositionEquiv
#print axioms Physics.DiracWeylConvention.annihilatorComplementRepresentationEquiv
#print axioms Physics.DiracWeylConvention.allLeft_dual_character_eq_signed_antisymmetrization
#print axioms Physics.DiracWeylConvention.radical_character_eq_kernel_add_dual_cokernel
#print axioms Physics.DiracWeylConvention.radical_dual_character_eq_lightIndex_antisymmetrization
#print axioms Physics.DiracWeylConvention.radical_dual_character_eq_allLeft_dual_character

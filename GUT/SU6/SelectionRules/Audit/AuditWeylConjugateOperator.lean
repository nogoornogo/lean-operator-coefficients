import GUT.SU6.SelectionRules.StandardBranch.WeylConjugateOperator
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylNonzeroMass

set_option autoImplicit false

namespace GUT.AuditWeylConjugateOperator

open WeylConjugateOperator WeylZeroModeSupport StandardWeylMassSource

example (M : StandardWeylModel (Multiplicative (ZMod 2))) :
    ¬ ForbidsBothOrientations (lightSpectrum M) := not_forbidsBothOrientations M

example : ¬ ForbidsBothOrientations
    (lightSpectrum (ConcreteWeylNonzeroMass.model (Multiplicative (ZMod 2)))) :=
  not_forbidsBothOrientations _

example (M : StandardWeylModel (Multiplicative (ZMod 2))) (hn : M.generations < 0) :
    conjugateThreeB (conjugateDuql M hn).operator = -3 := conjugateThreeB_eq _

#print axioms conjugateChargesSupported
#print axioms conjugateQque
#print axioms conjugateDuql
#print axioms conjugateThreeB_eq
#print axioms exists_invariant_operator_or_conjugate
#print axioms not_forbidsBothOrientations

end GUT.AuditWeylConjugateOperator

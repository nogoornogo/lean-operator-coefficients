import Math.Audit.ImportOrigin
import Math.LieGroups.Spin.SU5ExteriorAction

/-! Actual compact-lift comparison, with no branching certificate.
Generator conjugation alone does not remove the scalar ambiguity. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Compact exterior comparison imports another gauge family: {mod}"

namespace Math.CompactSpin.AuditSU5ExteriorAction

noncomputable section

open ExteriorComparison

example (T : Module.End ℂ (Fock.Space 0)) : T = Fock.vacuumScalar 0 T • 1 := by
  apply Fock.commutant_scalar
  intro v
  have hv : v = 0 := by funext i; exact Fin.elim0 i
  simp [hv]

example (g : SU5) (x : (P 5).W) :
    WCoordinates 5 (WAction g x) =
      SpecialUnitaryRealification.complexAction g (WCoordinates 5 x) := by
  simp [WAction]

/-- Distinct implementers can induce the same conjugation on every generator. -/
theorem scalar_ambiguity_control (v : Polarized.RealSpace 5) :
    (-1 : Module.End ℂ (Fock.Space 5)) * Fock.generator 5 v * (-1) =
      Fock.generator 5 v := by
  apply LinearMap.ext
  intro s
  change -Fock.generator 5 v (-s) = Fock.generator 5 v s
  rw [map_neg, neg_neg]

theorem scalar_ambiguity_nontrivial : (-1 : Module.End ℂ (Fock.Space 5)) ≠ 1 := by
  intro h
  have he := congrArg ExteriorAlgebra.algebraMapInv (LinearMap.congr_fun h 1)
  norm_num at he

example (g : SU5) (s : Fock.Space 5) :
    Fock.representation 5 (SU5Inclusion g) s = exteriorAction g s := actual_eq_exterior g s

example (g : SU5) (s : HalfSpin.Space 5) :
    (HalfSpin.representation 5 (SU5Inclusion g) s : Fock.Space 5) =
      exteriorAction g s := halfSpin_eq_exterior g s

example (g : SU5) : Fock.representation 5 (SU5Inclusion g) 1 = 1 := actual_fixes_vacuum g

#print axioms Fock.coefficient_continuous
#print axioms Fock.conjugation
#print axioms Fock.SU5_vectorAction
#print axioms Fock.SU5_conjugation
#print axioms Fock.halfSpin_restriction
#print axioms WCoordinates
#print axioms dualAction_fst
#print axioms coordinates_naturality
#print axioms generator_naturality
#print axioms PolarizedSpan.twice_axis
#print axioms PolarizedSpan.linearMap_eq_zero
#print axioms Fock.commutes_all
#print axioms Fock.commutant_scalar
#print axioms comparisonOperator_commutes
#print axioms actual_eq_scalar_exterior
#print axioms scalar_ne_zero
#print axioms scalarHom
#print axioms scalar_continuous
#print axioms scalar_eq_one
#print axioms actual_eq_exterior
#print axioms halfSpin_eq_exterior
#print axioms actual_fixes_vacuum
#print axioms scalar_ambiguity_control
#print axioms scalar_ambiguity_nontrivial

end

end Math.CompactSpin.AuditSU5ExteriorAction

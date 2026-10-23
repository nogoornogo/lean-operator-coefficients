import Math.Audit.ImportOrigin
import GUT.Sp.ChiralityObstruction
import Physics.StandardModel.Spectrum.Representations.Audit.AuditSelfDualChirality

open Math

/-! Arbitrary restrictions use only the pure SM target, not an assumed
SU(5) embedding. DUAL-2 torsion, singlet and zero-generation controls remain. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod ||
        ((`GUT.SU5).isPrefixOf mod &&
          mod != `GUT.SU5.Branching.WeylOrbit && mod != `GUT.SU5.Branching.ChargeResolved) then
      throwError "Symplectic arbitrary-subgroup target theorem imports a GUT source module: {mod}"

#print axioms GUT.CompactSymplectic.no_positive_SM_target

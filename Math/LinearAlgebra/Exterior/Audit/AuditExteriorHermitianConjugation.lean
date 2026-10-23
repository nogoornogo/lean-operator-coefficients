import Math.LinearAlgebra.Exterior.ExteriorHermitianConjugation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "ExteriorHermitianConjugation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExteriorHermitianConjugation.Twisted,
    ``Math.ExteriorHermitianConjugation.untwist,
    ``Math.ExteriorHermitianConjugation.EA,
    ``Math.ExteriorHermitianConjugation.twistedGenerator,
    ``Math.ExteriorHermitianConjugation.conjugate,
    ``Math.ExteriorHermitianConjugation.conjugate_smul,
    ``Math.ExteriorHermitianConjugation.conjugate_involutive,
    ``Math.ExteriorHermitianConjugation.adjoint,
    ``Math.ExteriorHermitianConjugation.adjoint_mul,
    ``Math.ExteriorHermitianConjugation.adjoint_smul,
    ``Math.ExteriorHermitianConjugation.conjugate_reverse,
    ``Math.ExteriorHermitianConjugation.adjoint_involutive,
    ``Math.ExteriorHermitianConjugation.coordinateConjugation,
    ``Math.ExteriorHermitianConjugation.coordinateConjugation_involutive,
    ``Math.ExteriorHermitianConjugation.coordinateConjugation_basis,
    ``Math.ExteriorHermitianConjugation.starRing,
    ``Math.ExteriorHermitianConjugation.starModule]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "ExteriorHermitianConjugation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"ExteriorHermitianConjugation: {ds.length} strict transitive checks passed"

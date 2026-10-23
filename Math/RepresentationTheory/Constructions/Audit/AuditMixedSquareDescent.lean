import Math.RepresentationTheory.Constructions.MixedSquareDescent
import Math.RepresentationTheory.Exterior.ExteriorSquareTensorDescent
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MixedSquareDescent.orderedEquiv,
    ``Math.MixedSquareDescent.equivariantEquiv,
    ``Math.ExteriorSquareTensorDescent.equiv,
    ``Math.ExteriorSquareTensorDescent.tensorEquiv,
    ``Math.ExteriorSquareTensorDescent.tensorEquiv_apply,
    ``Math.ExteriorSquareTensorDescent.tensorEquiv_symm_apply,
    ``Math.ExteriorSquareTensorDescent.equivariantEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed square descent: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed square descent: {declarations.length} strict transitive axiom checks passed"

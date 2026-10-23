import Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightExteriorQque
import Math.RepresentationTheory.Content.FiniteFlavorControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace Physics.CompactLightExteriorQqueAudit
noncomputable section
open Representation QqueSpinorExterior

def identitySplit {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ H V) :=
  SplitRepresentationProjection.Split.ofEquiv (Representation.Equiv.refl r)

theorem one_generation :
    matched (identitySplit (Representation.trivial ℂ Unit ℂ))
      (identitySplit (Representation.trivial ℂ Unit ℂ))
      (identitySplit (Representation.trivial ℂ Unit ℂ)) ≠ 0 :=
  matched_nonzero _ _ _

theorem s3_fields :
    matched (identitySplit FiniteFlavorControls.s3)
      (identitySplit FiniteFlavorControls.s3) (identitySplit FiniteFlavorControls.s3) ≠ 0 :=
  matched_nonzero _ _ _

theorem a4_fields :
    matched (identitySplit FiniteFlavorControls.a4)
      (identitySplit FiniteFlavorControls.a4) (identitySplit FiniteFlavorControls.a4) ≠ 0 :=
  matched_nonzero _ _ _

end
end Physics.CompactLightExteriorQqueAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exterior qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.WeylSpinor.left,
    ``Physics.WeylSpinor.right,
    ``Physics.WeylSpinor.right_apply,
    ``Physics.WeylSpinor.epsilonLeft,
    ``Physics.WeylSpinor.epsilonRight,
    ``Physics.WeylSpinor.four,
    ``Physics.QqueSpinorExterior.ordered,
    ``Physics.QqueSpinorExterior.ordered_apply,
    ``Physics.QqueSpinorExterior.HasNonzeroAlternation,
    ``Physics.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior,
    ``Physics.QqueSpinorExterior.matched_diagonal,
    ``Physics.QqueSpinorExterior.matched_nonzero,
    ``Physics.QqueSpinorExterior.exists_on_fields,
    ``Physics.CompactLightExteriorQque.exists_ordered_nonzero_exterior,
    ``Physics.CompactLightExteriorQque.exists_qque,
    ``Physics.CompactLightExteriorQqueAudit.one_generation,
    ``Physics.CompactLightExteriorQqueAudit.s3_fields,
    ``Physics.CompactLightExteriorQqueAudit.a4_fields]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior qque: layer and {declarations.length} strict axiom checks passed"

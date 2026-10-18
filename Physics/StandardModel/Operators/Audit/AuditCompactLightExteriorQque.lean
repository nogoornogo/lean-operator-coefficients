import Physics.StandardModel.Operators.CompactLightExteriorQque
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.CompactLightExteriorQqueAudit
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
end GUT.CompactLightExteriorQqueAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exterior qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.WeylSpinor.left,
    ``GUT.WeylSpinor.right,
    ``GUT.WeylSpinor.right_apply,
    ``GUT.WeylSpinor.epsilonLeft,
    ``GUT.WeylSpinor.epsilonRight,
    ``GUT.WeylSpinor.four,
    ``GUT.QqueSpinorExterior.ordered,
    ``GUT.QqueSpinorExterior.ordered_apply,
    ``GUT.QqueSpinorExterior.HasNonzeroAlternation,
    ``GUT.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior,
    ``GUT.QqueSpinorExterior.matched_diagonal,
    ``GUT.QqueSpinorExterior.matched_nonzero,
    ``GUT.QqueSpinorExterior.exists_on_fields,
    ``GUT.CompactLightExteriorQque.exists_ordered_nonzero_exterior,
    ``GUT.CompactLightExteriorQque.exists_qque,
    ``GUT.CompactLightExteriorQqueAudit.one_generation,
    ``GUT.CompactLightExteriorQqueAudit.s3_fields,
    ``GUT.CompactLightExteriorQqueAudit.a4_fields]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior qque: layer and {declarations.length} strict axiom checks passed"

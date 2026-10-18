import GUT.SU6.SelectionRules.Models.SMNormalizingColorSample
import GUT.SU6.SelectionRules.Models.NonabelianResidualSamples
import GUT.SU6.SelectionRules.Models.ColorWeakNormalizerSample
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.SU6NonabelianResidualSamples.ambient,
    ``GUT.SU6NonabelianResidualSamples.restriction,
    ``GUT.SU6NonabelianResidualSamples.restricted_action,
    ``GUT.SU6NonabelianResidualSamples.branching,
    ``GUT.SU6NonabelianResidualSamples.s3Ambient,
    ``GUT.SU6NonabelianResidualSamples.a4Ambient,
    ``GUT.SU6NonabelianResidualSamples.s3Branching,
    ``GUT.SU6NonabelianResidualSamples.a4Branching,
    ``GUT.SU6NonabelianResidualSamples.s3_dimension,
    ``GUT.SU6NonabelianResidualSamples.a4_dimension,
    ``GUT.ColorWeakNormalizerSample.exchange,
    ``GUT.ColorWeakNormalizerSample.colorProbe,
    ``GUT.ColorWeakNormalizerSample.colorMatrix,
    ``GUT.ColorWeakNormalizerSample.colorMatrix_apply,
    ``GUT.ColorWeakNormalizerSample.colorMatrix_SU,
    ``GUT.ColorWeakNormalizerSample.gaugeProbe,
    ``GUT.ColorWeakNormalizerSample.probe_in_image,
    ``GUT.ColorWeakNormalizerSample.image_cross_entry_zero,
    ``GUT.ColorWeakNormalizerSample.conjugated_cross_entry,
    ``GUT.ColorWeakNormalizerSample.conjugated_not_in_image,
    ``GUT.ColorWeakNormalizerSample.no_cover_compensator,
    ``GUT.SMNormalizingColorSample.beta,
    ``GUT.SMNormalizingColorSample.normalizes,
    ``GUT.SMNormalizingColorSample.invariant_color_factor]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Outside residual samples: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Outside residual samples: {ds.length} strict transitive checks passed"

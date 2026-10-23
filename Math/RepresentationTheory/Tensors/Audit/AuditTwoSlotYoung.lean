import Math.RepresentationTheory.Tensors.TwoSlotYoung
import Math.RepresentationTheory.Tensors.TwoSlotYoungSquares
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the two-slot Young input decomposition. -/
run_cmd do
  let declarations := [
    ``Math.InvolutionYoung.projector_eigen,
    ``Math.InvolutionYoung.projector_fixed,
    ``Math.InvolutionYoung.projector_idempotent,
    ``Math.InvolutionYoung.projector_vanish,
    ``Math.InvolutionYoung.quotientEquiv,
    ``Math.InvolutionYoung.quotientEquiv_mk,
    ``Math.InvolutionYoung.quotientEquiv_symm,
    ``Math.InvolutionYoung.splitting,
    ``Math.InvolutionYoung.coefficientEquiv,
    ``Math.TwoSlotYoung.swap_involutive,
    ``Math.TwoSlotYoung.splitting,
    ``Math.TwoSlotYoung.symmetricQuotientEquiv,
    ``Math.TwoSlotYoung.antisymmetricQuotientEquiv,
    ``Math.TwoSlotYoung.symmetric_projector,
    ``Math.TwoSlotYoung.antisymmetric_projector,
    ``Math.TwoSlotYoung.antisymmetric_diagonal,
    ``Math.TwoSlotYoungSquares.symmetricProjection,
    ``Math.TwoSlotYoungSquares.symmetricProjection_swap,
    ``Math.TwoSlotYoungSquares.symmetricEmbedding,
    ``Math.TwoSlotYoungSquares.symmetricEmbedding_tprod,
    ``Math.TwoSlotYoungSquares.symmetric_projection_projector,
    ``Math.TwoSlotYoungSquares.symmetric_embedding_projection,
    ``Math.TwoSlotYoungSquares.symmetricEquiv,
    ``Math.TwoSlotYoungSquares.exteriorProjection,
    ``Math.TwoSlotYoungSquares.exteriorEmbedding,
    ``Math.TwoSlotYoungSquares.exteriorEmbedding_wedge,
    ``Math.TwoSlotYoungSquares.exterior_projection_projector,
    ``Math.TwoSlotYoungSquares.exterior_embedding_projection,
    ``Math.TwoSlotYoungSquares.exteriorEquiv,
    ``Math.TwoSlotYoungSquares.componentsEquiv,
    ``Math.TwoSlotYoungSquares.splitting,
    ``Math.TwoSlotYoungSquares.splitting_tmul,
    ``Math.TwoSlotYoungSquares.splitting_symm_symmetric,
    ``Math.TwoSlotYoungSquares.splitting_symm_exterior,
    ``Math.TwoSlotYoungSquares.symmetricQuotientEquiv,
    ``Math.TwoSlotYoungSquares.exteriorQuotientEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-slot Young: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-slot Young: {declarations.length} strict transitive checks passed"

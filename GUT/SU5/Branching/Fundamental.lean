import GUT.SU5.Representations.Matter
import Physics.StandardModel.Gauge.Tensors.WeakContragredient

open Physics

open Math

/-! Full covering-group branching of the actual five and its dual. The
weak epsilon equivalence accounts for the pseudoreality of the weak doublet. -/

set_option autoImplicit false

namespace GUT.SU5.FundamentalBranching

noncomputable section

open StandardModelEmbedding Matter StandardSMGaugeTensor SMEpsilonTensor

abbrev Blocks := Color × Weak

def blocksRho : Representation ℂ GaugeGroup Blocks :=
  (twist color (-2)).prod (twist weak 3)

def splitEquiv : Five ≃ₗ[ℂ] Blocks where
  toFun v := (![v 0, v 1, v 2], ![v 3, v 4])
  invFun p := ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r v := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem index_symm (i : Fin 5) : blockIndexEquiv.symm i =
    ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1] i := by
  fin_cases i <;> rfl

theorem splitEquiv_action (g : GaugeGroup) (v : Five) :
    splitEquiv (fundamental (hom g) v) = blocksRho g (splitEquiv v) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [splitEquiv, fundamental, hom, matrixHom, rawHom, rawMatrix,
        colorBlock, weakBlock, index_symm, blocksRho, twist, color, weak,
        phase, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        mul_add, mul_assoc] <;> rfl
  · funext i
    fin_cases i <;>
      simp [splitEquiv, fundamental, hom, matrixHom, rawHom, rawMatrix,
        colorBlock, weakBlock, index_symm, blocksRho, twist, color, weak,
        phase, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        mul_add, mul_assoc] <;> rfl

def fundamentalEquiv : Representation.Equiv (fundamental.comp hom) blocksRho :=
  .mk splitEquiv (fun g => LinearMap.ext (splitEquiv_action g))

abbrev BarBlocks := Module.Dual ℂ Color × Weak

def barBlocksRho : Representation ℂ GaugeGroup BarBlocks := downRight.dual.prod lepton

def dualBlocksEquiv : Representation.Equiv blocksRho.dual barBlocksRho :=
  (SplitRepresentationProjection.dualProdEquiv downRight (twist weak 3)).symm.trans
    (SplitRepresentationProjection.prodEquiv (Representation.Equiv.refl _)
      StandardSMContragredient.leptonDualEquiv.symm)

def antifundamentalEquiv : Representation.Equiv (antifundamental.comp hom) barBlocksRho := by
  rw [antifundamental, SplitRepresentationProjection.dual_comp]
  exact (SplitRepresentationProjection.dualEquiv fundamentalEquiv).trans dualBlocksEquiv

end

end GUT.SU5.FundamentalBranching

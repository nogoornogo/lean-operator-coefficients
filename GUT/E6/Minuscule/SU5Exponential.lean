import GUT.E6.Minuscule.SU5GroupAction
import GUT.SU6.Embeddings.ContinuousEmbeddingRegularityBridge

open Math

/-! Exponential compatibility of the actual SU(5) action, calculated from
the defining, inverse-transpose and exterior minor formulas. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open SpecialUnitaryLieAlgebra ContinuousEmbeddingRegularityBridge NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

attribute [local instance] TauCeti.normedAlgebraRatOfReal

def coordinateUnits : SU5 →ₜ* (Matrix Index Index ℂ)ˣ where
  toMonoidHom := coordinateAction.toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨coordinateAction_continuous, coordinateAction_continuous.comp continuous_inv⟩

def representedLine (X : CompactRealForm (Fin 5)) :
    Multiplicative ℝ →ₜ* (Matrix Index Index ℂ)ˣ :=
  coordinateUnits.comp (compactOneParameter X)

theorem sourceLine_hasDerivAt (X : CompactRealForm (Fin 5)) :
    HasDerivAt (fun t : ℝ => (CompactRealForm.expSpecialUnitary (t • X)).val)
      (X : Matrix (Fin 5) (Fin 5) ℂ) 0 := by
  let hNormed : NormedAddCommGroup (Matrix (Fin 5) (Fin 5) ℂ) :=
    NonUnitalNormedRing.toNormedAddCommGroup
  let : AddCommGroup (Matrix (Fin 5) (Fin 5) ℂ) := hNormed.toAddCommGroup
  change HasDerivAt (fun t : ℝ => exp (t • (X : Matrix (Fin 5) (Fin 5) ℂ))) _ 0
  simpa using hasDerivAt_exp_smul_const (X : Matrix (Fin 5) (Fin 5) ℂ) (0 : ℝ)

theorem representedLine_hasDerivAt (X : CompactRealForm (Fin 5)) :
    HasDerivAt (fun t : ℝ => (representedLine X (Multiplicative.ofAdd t)).val)
      (blockMatrix (X : Matrix (Fin 5) (Fin 5) ℂ)) 0 := by
  have hp (a b : Fin 5) := hasDerivAt_pi.mp (hasDerivAt_pi.mp (sourceLine_hasDerivAt X) a) b
  have hn (a b : Fin 5) := hasDerivAt_pi.mp (hasDerivAt_pi.mp (sourceLine_hasDerivAt (-X)) a) b
  change HasDerivAt (fun t : ℝ => coordinateAction (CompactRealForm.expSpecialUnitary (t • X))) _ 0
  simp_rw [coordinateAction_eq]
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  rcases a with a | a | ⟨k, a⟩ | a <;> rcases b with b | b | ⟨l, b⟩ | b
  all_goals dsimp only [actionBlock, blockMatrix]
  all_goals try exact hasDerivAt_const _ _
  · exact hp a b
  · split_ifs
    · have h := hn b a
      rw [show ((-X).toSpecialLinear : Matrix (Fin 5) (Fin 5) ℂ) =
        -(X : Matrix (Fin 5) (Fin 5) ℂ) from rfl] at h
      simpa only [CompactRealForm.expSpecialUnitary_real_smul_neg, Matrix.neg_apply] using h
    · exact hasDerivAt_const _ _
  · simp_rw [exteriorMatrix_minor]
    convert ((hp a.val.1 b.val.1).mul (hp a.val.2 b.val.2)).sub
      ((hp a.val.1 b.val.2).mul (hp a.val.2 b.val.1)) using 1 ;
      (try simp only [zero_smul, CompactRealForm.expSpecialUnitary_zero,
        OneMemClass.coe_one, Matrix.one_apply, wedgeMatrix]) ; first | rfl | ring

theorem representedLine_eq_exp (X : CompactRealForm (Fin 5)) :
    representedLine X = TauCeti.expUnitHom (blockMatrix (X : Matrix (Fin 5) (Fin 5) ℂ)) :=
  TauCeti.continuousMonoidHom_eq_expUnitHom_of_hasDerivAt _ _ (representedLine_hasDerivAt X)

theorem coordinateAction_exp (X : CompactRealForm (Fin 5)) (t : ℝ) :
    coordinateAction (CompactRealForm.expSpecialUnitary (t • X)) =
      exp (t • blockMatrix (X : Matrix (Fin 5) (Fin 5) ℂ)) := by
  have h := congrArg (fun f => (f (Multiplicative.ofAdd t)).val) (representedLine_eq_exp X)
  change coordinateAction (CompactRealForm.expSpecialUnitary (t • X)) =
    (TauCeti.expUnitHom (blockMatrix (X : Matrix (Fin 5) (Fin 5) ℂ))
      (Multiplicative.ofAdd t)).val at h
  simpa only [TauCeti.expUnitHom_apply, TauCeti.expUnit_coe] using h

def ambientInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix27 :=
  matrixCoordinates.symm (blockMatrix X)

theorem groupAction_exp (X : CompactRealForm (Fin 5)) (t : ℝ) :
    groupAction (CompactRealForm.expSpecialUnitary (t • X)) =
      exp (t • ambientInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ)) := by
  change matrixCoordinates.symm (coordinateAction _) = _
  rw [coordinateAction_exp, map_exp matrixCoordinates.symm
    matrixCoordinates.symm.toLinearMap.continuous_of_finiteDimensional]
  congr 1
  exact map_smul (matrixCoordinates.symm.toLinearMap.restrictScalars ℝ) t _

end

end GUT.E6.Minuscule.SU5Coordinates

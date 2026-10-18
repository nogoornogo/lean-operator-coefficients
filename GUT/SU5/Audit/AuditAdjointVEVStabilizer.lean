import GUT.SU5.Symmetry.AdjointVEVHom
import Lean.Util.CollectAxioms

open Math

/-! Persistent strict audit, including eigenvalue collision, zero VEV and a
genuine color/weak mixing countercontrol. -/
namespace GUT.SU5.AdjointVEVStabilizer.Audit
set_option autoImplicit false
noncomputable section

def mixing : StandardModelEmbedding.TargetGroup :=
  ⟨!![0, 0, 0, -1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0; 0, 0, 0, 0, 1], by
    constructor
    · change (!![0, 0, 0, -1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
        1, 0, 0, 0, 0; 0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) ℂ) ∈
        Matrix.unitaryGroup (Fin 5) ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    · change Matrix.det
        (!![0, 0, 0, -1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
          1, 0, 0, 0, 0; 0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) ℂ) = 1
      have hd : Matrix.det
          (!![0, 0, 0, -1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
            1, 0, 0, 0, 0; 0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) ℚ) = 1 := by
        decide +kernel
      have hc := congrArg (Rat.castHom ℂ) hd
      rw [RingHom.map_det] at hc
      convert hc using 1 <;> norm_num [Matrix.map_apply]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]⟩

theorem mixing_not_mem : mixing ∉ subgroup := by
  intro h
  have he := ((mem_iff_cross_entries mixing).mp h) 0 0
  change (-1 : ℂ) = 0 ∧ (1 : ℂ) = 0 at he
  norm_num at he

theorem mixing_not_fixed : mixing.val * vev * mixing⁻¹.val ≠ vev := by
  intro h
  exact mixing_not_mem ((fixed_iff mixing).mp h)

theorem zero_control :
    SUN.AdjointStabilizer.subgroup
      (0 : Matrix StandardModelEmbedding.BlockIndex StandardModelEmbedding.BlockIndex ℂ) = ⊤ := by
  apply top_unique
  intro g hg
  change g.val * 0 = 0 * g.val
  simp

end
end GUT.SU5.AdjointVEVStabilizer.Audit

run_cmd do
  let declarations := [
    ``Math.DiagonalCentralizer.commute_iff,
    ``Math.DiagonalCentralizer.two_eigenvalue_iff,
    ``Math.DiagonalCentralizer.block_form_iff,
    ``Math.DiagonalCentralizer.collision,
    ``Math.SUN.AdjointStabilizer.fixed_iff,
    ``Math.SUN.AdjointStabilizer.blocks_unitary,
    ``Math.SUN.AdjointStabilizer.blocks_det,
    ``Math.SUN.AdjointStabilizer.classification,
    ``Math.SUN.AdjointStabilizer.collision,
    ``GUT.SU5.AdjointVEVStabilizer.traceless,
    ``GUT.SU5.AdjointVEVStabilizer.classification,
    ``GUT.SU5.AdjointVEVStabilizer.fixed_iff,
    ``GUT.SU5.AdjointVEVStabilizer.mem_iff_cross_entries,
    ``GUT.SU5.AdjointVEVStabilizer.covering_fixed,
    ``GUT.SU5.AdjointVEVStabilizer.Audit.mixing_not_mem,
    ``GUT.SU5.AdjointVEVStabilizer.Audit.mixing_not_fixed,
    ``GUT.SU5.AdjointVEVStabilizer.Audit.zero_control,
    ``Math.SUN.AdjointStabilizer.blockPairs,
    ``Math.SUN.AdjointStabilizer.joinBlocks,
    ``Math.SUN.AdjointStabilizer.blockEquiv,
    ``Math.SurjectiveHomTransport.homEquiv,
    ``Math.SurjectiveHomTransport.nonzero_iff,
    ``Math.SurjectiveHomTransport.descends_iff,
    ``GUT.SU5.AdjointVEVStabilizer.blocks_lift,
    ``GUT.SU5.AdjointVEVStabilizer.cover_surjective,
    ``GUT.SU5.AdjointVEVStabilizer.image_eq_stabilizer,
    ``GUT.SU5.AdjointVEVStabilizer.cover_kernel,
    ``GUT.SU5.AdjointVEVStabilizer.coverKernelCyclicEquiv,
    ``GUT.SU5.AdjointVEVStabilizer.cover_kernel_card,
    ``GUT.SU5.AdjointVEVStabilizer.cover_kernel_le_center,
    ``GUT.SU5.AdjointVEVStabilizer.cover_mem_kernel_iff,
    ``GUT.SU5.AdjointVEVStabilizer.quotientStabilizerEquiv,
    ``GUT.SU5.AdjointVEVStabilizer.quotientStabilizerEquiv_mk,
    ``GUT.SU5.AdjointVEVStabilizer.unitaryBlockEquiv,
    ``GUT.SU5.AdjointVEVStabilizer.unitaryBlockEquiv_color,
    ``GUT.SU5.AdjointVEVStabilizer.unitaryBlockEquiv_weak,
    ``GUT.SU5.AdjointVEVStabilizer.unitaryBlockEquiv_symm,
    ``GUT.SU5.AdjointVEVStabilizer.residualHomEquiv,
    ``GUT.SU5.AdjointVEVStabilizer.residualHomEquiv_apply,
    ``GUT.SU5.AdjointVEVStabilizer.residualHom_nonzero_iff,
    ``GUT.SU5.AdjointVEVStabilizer.representation_descends_iff,
    ``GUT.SU5.AdjointVEVStabilizer.ambient_representation_descends]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Adjoint VEV stabilizer: {declarations.length} strict transitive checks passed"

import GUT.SU5.Matching.AdjointMass

open Math

/-! The two currents are projections of the actual exterior infinitesimal
action, for all six complexified color/weak mediator directions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.HeavyCurrents
noncomputable section
open ExteriorSquareCoordinates ExteriorSquareBranching SMEpsilonTensor
open scoped TensorProduct

def upper (a : Fin 3) (w : Fin 2) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.single (Fin.castAdd 2 a) (Fin.natAdd 3 w) 1

def lower (a : Fin 3) (w : Fin 2) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.single (Fin.natAdd 3 w) (Fin.castAdd 2 a) 1

def quarkEmbed : StandardSMGaugeTensor.Quark →ₗ[ℂ] Matter.Ten where
  toFun q := tenEquiv.symm (0, (q, 0))
  map_add' q r := by simp [← map_add]
  map_smul' z q := by simp [← map_smul]

theorem branch_quarkEmbed (q : StandardSMGaugeTensor.Quark) :
    branch (quarkEmbed q) = (0, (q, 0)) :=
  tenEquiv.apply_symm_apply _

theorem quarkEmbed_tmul (a : Color) (x : Weak) :
    quarkEmbed (a ⊗ₜ[ℂ] x) = wedge (a, 0) (0, x) := by
  apply branch_bijective.1
  rw [branch_quarkEmbed, branch_wedge_split, pair_color_weak]

def upCurrent (a : Fin 3) (w : Fin 2) :
    StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ Color :=
  ((LinearMap.fst ℂ _ _).comp branch).comp ((infinitesimal (upper a w)).comp quarkEmbed)

def electronCurrent (a : Fin 3) (w : Fin 2) :
    StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ ℂ :=
  ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp branch)).comp
    ((infinitesimal (lower a w)).comp quarkEmbed)

private theorem branch_infinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ)
    (a b : FundamentalBranching.Blocks) :
    branch (infinitesimal X (wedge a b)) =
      pair (FundamentalBranching.splitEquiv (Matrix.toLin' X
        (FundamentalBranching.splitEquiv.symm a))) b +
      pair a (FundamentalBranching.splitEquiv (Matrix.toLin' X
        (FundamentalBranching.splitEquiv.symm b))) := by
  rw [wedge, infinitesimal_leibniz, map_add, branch_wedge, branch_wedge]
  simp

private theorem upper_color (i : Fin 3) (w : Fin 2) (a : Color) :
    FundamentalBranching.splitEquiv (Matrix.toLin' (upper i w)
      (FundamentalBranching.splitEquiv.symm (a, 0))) = 0 := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases w <;> fin_cases j <;>
    simp [upper, FundamentalBranching.splitEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.single_apply]

private theorem upper_weak (i : Fin 3) (w : Fin 2) (x : Weak) :
    FundamentalBranching.splitEquiv (Matrix.toLin' (upper i w)
      (FundamentalBranching.splitEquiv.symm (0, x))) = (x w • colorBasis i, 0) := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases w <;> fin_cases j <;>
    simp [upper, FundamentalBranching.splitEquiv, Matrix.toLin'_apply,
      Matrix.single_mulVec, colorBasis]

private theorem lower_color (i : Fin 3) (w : Fin 2) (a : Color) :
    FundamentalBranching.splitEquiv (Matrix.toLin' (lower i w)
      (FundamentalBranching.splitEquiv.symm (a, 0))) = (0, a i • weakBasis w) := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases w <;> fin_cases j <;>
    simp [lower, FundamentalBranching.splitEquiv, Matrix.toLin'_apply,
      Matrix.single_mulVec, weakBasis]

private theorem lower_weak (i : Fin 3) (w : Fin 2) (x : Weak) :
    FundamentalBranching.splitEquiv (Matrix.toLin' (lower i w)
      (FundamentalBranching.splitEquiv.symm (0, x))) = 0 := by
  apply Prod.ext <;> ext j <;> fin_cases i <;> fin_cases w <;> fin_cases j <;>
    simp [lower, FundamentalBranching.splitEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.single_apply]

theorem upCurrent_tmul (i : Fin 3) (w : Fin 2) (a u : Color) (x : Weak) :
    upCurrent i w (a ⊗ₜ[ℂ] x) u = x w * eps3 a (colorBasis i) u := by
  change (branch (infinitesimal (upper i w) (quarkEmbed (a ⊗ₜ[ℂ] x)))).1 u = _
  rw [quarkEmbed_tmul, branch_infinitesimal, upper_color, upper_weak]
  change (eps3Trilin 0 0 + eps3Trilin a (x w • colorBasis i)) u = _
  simp only [map_zero, zero_add, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rfl

theorem electronCurrent_tmul (i : Fin 3) (w : Fin 2) (a : Color) (x : Weak) (e : ℂ) :
    electronCurrent i w (a ⊗ₜ[ℂ] x) e = a i * eps2 (weakBasis w) x * e := by
  change (branch (infinitesimal (lower i w) (quarkEmbed (a ⊗ₜ[ℂ] x)))).2.2 e = _
  rw [quarkEmbed_tmul, branch_infinitesimal, lower_color, lower_weak]
  change (eps2 (a i • weakBasis w) x • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) +
    eps2 0 0 • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) e = _
  change eps2 (a i • weakBasis w) x * e + eps2 0 0 * e = _
  rw [eps2_smul_left]
  simp [eps2]

def contraction (q r : StandardSMGaugeTensor.Quark) (u : Color) (e : ℂ) : ℂ :=
  ∑ i : Fin 3, ∑ w : Fin 2, upCurrent i w q u * electronCurrent i w r e

theorem contraction_tmul (a b u : Color) (x y : Weak) (e : ℂ) :
    contraction (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y) u e = eps3 a b u * eps2 x y * e := by
  simp only [contraction, upCurrent_tmul, electronCurrent_tmul]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num [colorBasis, weakBasis, eps3, eps2, Pi.single_apply, Fin.ext_iff]
  ring

theorem contraction_eq_qque (q r : StandardSMGaugeTensor.Quark) (u : Color) (e : ℂ) :
    contraction q r u e = StandardSMGaugeTensor.qque ((q ⊗ₜ[ℂ] r) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  induction q using TensorProduct.inductionOn with
  | add q r hq hr => simp_all [contraction, add_mul, Finset.sum_add_distrib, TensorProduct.add_tmul]
  | tmul a x =>
    induction r using TensorProduct.inductionOn with
    | add q r hq hr => simp_all [contraction, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul, TensorProduct.tmul_add]
    | tmul b y => rw [contraction_tmul, StandardSMGaugeTensor.qque_tmul]

end
end GUT.SU5.HeavyCurrents

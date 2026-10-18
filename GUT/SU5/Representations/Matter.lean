import GUT.SU5.Embeddings.StandardModel
import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Actual algebraic SU(5) matter representations. The ten is the exterior
square functor, not a separately specified weight list. -/

set_option autoImplicit false

namespace GUT.SU5.Matter

noncomputable section

open StandardModelEmbedding

abbrev Five := Fin 5 → ℂ
abbrev BarFive := Module.Dual ℂ Five
abbrev Ten := ⋀[ℂ]^2 Five

def fundamental : Representation ℂ TargetGroup Five where
  toFun g := Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

def antifundamental : Representation ℂ TargetGroup BarFive := fundamental.dual

def ten : Representation ℂ TargetGroup Ten := fundamental.exteriorPower 2

theorem fundamental_jointlyContinuous :
    Continuous (fun p : TargetGroup × Five => fundamental p.1 p.2) :=
  (continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd

@[simp] theorem five_finrank : Module.finrank ℂ Five = 5 := by simp [Five]
@[simp] theorem barFive_finrank : Module.finrank ℂ BarFive = 5 := by
  simp [BarFive, Subspace.dual_finrank_eq]
@[simp] theorem ten_finrank : Module.finrank ℂ Ten = 10 := by
  simp [Ten, exteriorPower.finrank_eq, Nat.choose]

theorem ten_not_equiv_barFive : IsEmpty (Representation.Equiv ten antifundamental) := by
  refine ⟨fun e => ?_⟩
  have h := e.toLinearEquiv.finrank_eq
  norm_num [Nat.choose] at h

end

end GUT.SU5.Matter

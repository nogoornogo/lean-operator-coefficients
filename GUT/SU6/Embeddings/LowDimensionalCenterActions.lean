import GUT.SU6.Embeddings.CompactEmbeddingClassification
import Math.RepresentationTheory.Decomposition.ExternalTensorProduct
import Mathlib.Tactic

open Math

/-!
# Concrete weak-center actions in low dimension

This module realizes the two center calculations used by the semisimple embedding classification branch
argument.  The defining two-dimensional representation of `SU(2)` detects
`-I₂`, while its tensor square kills `-I₂`.  Consequently every invariant
subspace of the tensor square, in particular the symmetric-square triplet once
that subspace is identified, also kills the weak center.
-/

namespace GUT
namespace LowDimensionalCenterActions

open CompactEmbeddingClassification
open TensorProduct
open ExternalTensorProduct

noncomputable section

abbrev WeakStd := Fin 2 -> ℂ

/-- The defining representation of `SU(2)` on `ℂ²`. -/
def su2Defining : Representation ℂ SU2 WeakStd where
  toFun g := Matrix.toLin' ((g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    change Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℂ) = LinearMap.id
    exact Matrix.toLin'_one
  map_mul' := by
    intro g h
    change
      Matrix.toLin'
          (((g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *
            ((h : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) =
        (Matrix.toLin' ((g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)).comp
          (Matrix.toLin' ((h : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
    exact Matrix.toLin'_mul
      ((g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      ((h : SU2) : Matrix (Fin 2) (Fin 2) ℂ)

/-- The nontrivial `SU(2)` center acts as `-1` on the defining doublet. -/
theorem su2Defining_center_action :
    su2Defining su2CenterElement =
      (-1 : ℂ) • (LinearMap.id : WeakStd →ₗ[ℂ] WeakStd) := by
  change Matrix.toLin' (-1 : Matrix (Fin 2) (Fin 2) ℂ) = _
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLin'_apply, LinearMap.smul_apply, LinearMap.id_apply,
    neg_one_smul]
  fin_cases i <;> simp [Matrix.mulVec]

/-- The defining weak doublet, inflated from `SU(2)` to `SU(3) × SU(2)`. -/
def weakDoublet : Representation ℂ ProductGroup WeakStd :=
  su2Defining.comp (MonoidHom.snd SU3 SU2)

theorem weakDoublet_weakCenter_action :
    weakDoublet weakCenterElement =
      (-1 : ℂ) • (LinearMap.id : WeakStd →ₗ[ℂ] WeakStd) := by
  exact su2Defining_center_action

/-- The concrete weak doublet satisfies the abstract detection predicate used
by the kernel obstruction. -/
theorem weakDoublet_detectsWeakCenter : DetectsWeakCenter weakDoublet := by
  refine ⟨fun _ => 1, ?_⟩
  rw [weakDoublet_weakCenter_action]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-!
## Irreducibility of the defining doublet

Two explicit elements suffice.  The phase element separates the two standard
basis coordinates, and the quarter-turn exchanges them.
-/

/-- The diagonal element `diag(i,-i)` of `SU(2)`. -/
def su2PhaseElement : SU2 :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply]
    · simp [Matrix.det_fin_two]⟩

/-- The real quarter-turn matrix in `SU(2)`. -/
def su2QuarterTurnElement : SU2 :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply]
    · simp [Matrix.det_fin_two]⟩

theorem su2PhaseElement_action (v : WeakStd) :
    su2Defining su2PhaseElement v =
      ![Complex.I * v 0, -Complex.I * v 1] := by
  ext i
  fin_cases i <;>
    simp [su2Defining, su2PhaseElement, Matrix.toLin'_apply, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]

theorem su2QuarterTurnElement_action (v : WeakStd) :
    su2Defining su2QuarterTurnElement v = ![v 1, -v 0] := by
  ext i
  fin_cases i <;>
    simp [su2Defining, su2QuarterTurnElement, Matrix.toLin'_apply, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]

theorem phase_isolates_first_coordinate (v : WeakStd) :
    v + (-Complex.I) • su2Defining su2PhaseElement v =
      (2 * v 0) • Pi.basisFun ℂ (Fin 2) 0 := by
  rw [su2PhaseElement_action]
  ext i
  fin_cases i <;> simp [Pi.basisFun_apply] <;> ring_nf <;>
    simp [Complex.I_sq] ; ring

theorem phase_isolates_second_coordinate (v : WeakStd) :
    v + Complex.I • su2Defining su2PhaseElement v =
      (2 * v 1) • Pi.basisFun ℂ (Fin 2) 1 := by
  rw [su2PhaseElement_action]
  ext i
  fin_cases i <;> simp [Pi.basisFun_apply] <;> ring_nf <;>
    simp [Complex.I_sq] ; ring

theorem quarterTurn_basis_zero :
    su2Defining su2QuarterTurnElement (Pi.basisFun ℂ (Fin 2) 0) =
      -Pi.basisFun ℂ (Fin 2) 1 := by
  rw [su2QuarterTurnElement_action]
  ext i
  fin_cases i <;> simp [Pi.basisFun_apply]

theorem quarterTurn_basis_one :
    su2Defining su2QuarterTurnElement (Pi.basisFun ℂ (Fin 2) 1) =
      Pi.basisFun ℂ (Fin 2) 0 := by
  rw [su2QuarterTurnElement_action]
  ext i
  fin_cases i <;> simp [Pi.basisFun_apply]

/-- The concrete defining representation of `SU(2)` is irreducible. -/
theorem su2Defining_isIrreducible :
    Representation.IsIrreducible su2Defining := by
  let : Nontrivial (Subrepresentation su2Defining) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule ℂ WeakStd) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.ext
    exact h
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSub
  have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    funext i
    fin_cases i <;> simp [h]
  have hbasis :
      Pi.basisFun ℂ (Fin 2) 0 ∈ S.toSubmodule ∧
        Pi.basisFun ℂ (Fin 2) 1 ∈ S.toSubmodule := by
    rcases hcoord with hfirst | hsecond
    · have hphase := S.apply_mem_toSubmodule su2PhaseElement hvS
      have hcomb := S.toSubmodule.add_mem hvS
        (S.toSubmodule.smul_mem (-Complex.I) hphase)
      rw [phase_isolates_first_coordinate] at hcomb
      have hne : (2 : ℂ) * v 0 ≠ 0 := mul_ne_zero (by norm_num) hfirst
      have he0 := S.toSubmodule.smul_mem (((2 : ℂ) * v 0)⁻¹) hcomb
      have he0' : Pi.basisFun ℂ (Fin 2) 0 ∈ S.toSubmodule := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at he0
        exact he0
      have hturn := S.apply_mem_toSubmodule su2QuarterTurnElement he0'
      rw [quarterTurn_basis_zero] at hturn
      have he1 := S.toSubmodule.smul_mem (-1 : ℂ) hturn
      constructor
      · exact he0'
      · simpa using he1
    · have hphase := S.apply_mem_toSubmodule su2PhaseElement hvS
      have hcomb := S.toSubmodule.add_mem hvS
        (S.toSubmodule.smul_mem Complex.I hphase)
      rw [phase_isolates_second_coordinate] at hcomb
      have hne : (2 : ℂ) * v 1 ≠ 0 := mul_ne_zero (by norm_num) hsecond
      have he1 := S.toSubmodule.smul_mem (((2 : ℂ) * v 1)⁻¹) hcomb
      have he1' : Pi.basisFun ℂ (Fin 2) 1 ∈ S.toSubmodule := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at he1
        exact he1
      have he0 := S.apply_mem_toSubmodule su2QuarterTurnElement he1'
      rw [quarterTurn_basis_one] at he0
      exact ⟨he0, he1'⟩
  apply top_unique
  change (⊤ : Submodule ℂ WeakStd) ≤ S.toSubmodule
  intro v _
  have hvdecomp :
      v = v 0 • Pi.basisFun ℂ (Fin 2) 0 +
        v 1 • Pi.basisFun ℂ (Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [Pi.basisFun_apply]
  rw [hvdecomp]
  exact S.toSubmodule.add_mem
    (S.toSubmodule.smul_mem (v 0) hbasis.1)
    (S.toSubmodule.smul_mem (v 1) hbasis.2)

/-- The diagonal tensor square of the defining `SU(2)` representation. -/
def su2TensorSquare : Representation ℂ SU2 (WeakStd ⊗[ℂ] WeakStd) :=
  su2Defining.tprod su2Defining

/-- The center sign squares to `+1` on the tensor square. -/
theorem su2TensorSquare_center_action :
    su2TensorSquare su2CenterElement =
      (LinearMap.id : (WeakStd ⊗[ℂ] WeakStd) →ₗ[ℂ]
        (WeakStd ⊗[ℂ] WeakStd)) := by
  apply TensorProduct.ext'
  intro v w
  simp only [su2TensorSquare, Representation.tprod_apply,
    su2Defining_center_action, TensorProduct.map_tmul,
    LinearMap.smul_apply, LinearMap.id_apply]
  simp only [neg_one_smul]
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

/-- Every invariant subspace of the tensor square inherits trivial action of
the nontrivial center. -/
theorem center_acts_trivially_on_tensorSquare_subrepresentation
    (S : Subrepresentation su2TensorSquare) (x : S) :
    su2TensorSquare su2CenterElement x = x := by
  rw [su2TensorSquare_center_action]
  rfl

section ProductBlocks

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Any color representation externally tensored with the defining weak
doublet has weak-center character `-1`. -/
theorem externalTprod_weakDoublet_center_action
    (rho : Representation ℂ SU3 V) :
    externalTprod rho su2Defining weakCenterElement =
      (-1 : ℂ) •
        (LinearMap.id : (V ⊗[ℂ] WeakStd) →ₗ[ℂ] (V ⊗[ℂ] WeakStd)) := by
  simpa [weakCenterElement] using
    (externalTprod_apply_eq_smul_id rho su2Defining
      (1 : SU3) su2CenterElement (1 : ℂ) (-1 : ℂ)
      (by rw [map_one, one_smul, Module.End.one_eq_id])
      su2Defining_center_action)

/-- Any color representation externally tensored with the weak tensor square
has trivial weak-center action. -/
theorem externalTprod_weakTensorSquare_center_action
    (rho : Representation ℂ SU3 V) :
    externalTprod rho su2TensorSquare weakCenterElement =
      (LinearMap.id :
        (V ⊗[ℂ] (WeakStd ⊗[ℂ] WeakStd)) →ₗ[ℂ]
          (V ⊗[ℂ] (WeakStd ⊗[ℂ] WeakStd))) := by
  simpa [weakCenterElement] using
    (externalTprod_apply_eq_smul_id rho su2TensorSquare
      (1 : SU3) su2CenterElement (1 : ℂ) (1 : ℂ)
      (by rw [map_one, one_smul, Module.End.one_eq_id])
      (by simpa only [one_smul] using su2TensorSquare_center_action))

end ProductBlocks

end

end LowDimensionalCenterActions
end GUT

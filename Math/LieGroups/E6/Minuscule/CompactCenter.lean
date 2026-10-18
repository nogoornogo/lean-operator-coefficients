import Math.LieGroups.E6.Minuscule.CompactLieGroup
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.GroupTheory.Coset.Card

/-!
# Scalar-center bounds for the actual connected compact candidate

Centrality is differentiated along the actual exponential parametrization.
The scalar commutant and determinant give an upper bound, not an assertion
that every scalar of order dividing 27 belongs to the identity component.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

theorem compact_center_commutes_real (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.center compactIdentityComponent) (X : compactMatrixLieAlgebra) :
    Commute (compactMatrix g) (X : Matrix27) := by
  have he : (fun Y : compactMatrixLieAlgebra => compactMatrix g * compactMatrix (compactExp Y)) =
      (fun Y : compactMatrixLieAlgebra => compactMatrix (compactExp Y) * compactMatrix g) := by
    funext Y
    exact congrArg compactMatrix ((Subgroup.mem_center_iff.mp hg) (compactExp Y)).symm
  have hd := compactExp_hasStrictFDerivAt_zero.hasFDerivAt
  have hl := hd.const_mul (compactMatrix g)
  have hr := hd.mul_const' (compactMatrix g)
  change HasFDerivAt (fun Y => compactMatrix g * compactMatrix (compactExp Y)) _ 0 at hl
  rw [he] at hl
  exact congrArg (fun f : compactMatrixLieAlgebra →L[ℝ] Matrix27 => f X) (hl.unique hr)

theorem compact_commutant_scalar (M : Matrix27)
    (hM : ∀ X : compactMatrixLieAlgebra, Commute M (X : Matrix27)) :
    M = M 0 0 • (1 : Matrix27) := by
  apply matrixLieAlgebra_commutant_scalar M
  intro x hx
  let K := MatrixCompactRealForm.conjugation (matrixLieAlgebra ℂ) matrixLieAlgebra_adjoint
  have hK : Function.Involutive K := MatrixCompactRealForm.conjugation_involutive _ _
  let r : compactRealForm := ⟨TauCeti.conjRealPart K ⟨x, hx⟩, TauCeti.conjRealPart_mem hK _⟩
  let s : compactRealForm :=
    ⟨TauCeti.conjImaginaryPart K ⟨x, hx⟩, TauCeti.conjImaginaryPart_mem hK _⟩
  have hdecomp : r.val.val + Complex.I • s.val.val = x :=
    congrArg (fun z : matrixLieAlgebra ℂ => (z : Matrix27))
      (TauCeti.conjRealPart_add_I_smul_conjImaginaryPart (K := K) ⟨x, hx⟩)
  have hpart (v : compactRealForm) : ⁅M, v.val.val⁆ = 0 :=
    sub_eq_zero.mpr (hM ⟨v.val.val, ⟨v, rfl⟩⟩).eq
  rw [← hdecomp, lie_add, lie_smul, hpart r, hpart s, smul_zero, add_zero]

theorem compact_center_scalar (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.center compactIdentityComponent) :
    compactMatrix g = compactMatrix g 0 0 • (1 : Matrix27) :=
  compact_commutant_scalar _ (compact_center_commutes_real g hg)

theorem compact_mem_center_iff_scalar (g : compactIdentityComponent) :
    g ∈ Subgroup.center compactIdentityComponent ↔ ∃ z : ℂ, compactMatrix g = z • 1 := by
  constructor
  · intro hg
    exact ⟨compactMatrix g 0 0, compact_center_scalar g hg⟩
  · rintro ⟨z, hz⟩
    rw [Subgroup.mem_center_iff]
    intro h
    apply compactMatrix_injective
    simp [compactMatrix_mul, hz]

def compactCenterScalar : Subgroup.center compactIdentityComponent →* ℂ where
  toFun g := compactMatrix g.val 0 0
  map_one' := by simp
  map_mul' g h := by
    change compactMatrix (g.val * h.val) 0 0 = _
    rw [compactMatrix_mul, compact_center_scalar g.val g.property,
      compact_center_scalar h.val h.property]
    simp [mul_comm]

theorem compactCenterScalar_pow (g : Subgroup.center compactIdentityComponent) :
    compactCenterScalar g ^ 27 = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.val.val.property).2
  change Matrix.det (compactMatrix g.val) = 1 at hd
  rw [compact_center_scalar g.val g.property] at hd
  simpa [compactCenterScalar, Matrix.det_smul] using hd

theorem compactCenterScalar_ne_zero (g : Subgroup.center compactIdentityComponent) :
    compactCenterScalar g ≠ 0 := by
  intro hz
  simpa [hz] using compactCenterScalar_pow g

theorem compactCenterScalar_injective : Function.Injective compactCenterScalar := by
  intro g h he
  apply Subtype.ext
  apply compactMatrix_injective
  rw [compact_center_scalar g.val g.property, compact_center_scalar h.val h.property]
  exact congrArg (fun z : ℂ => z • (1 : Matrix27)) he

/-- Only an injection: component membership of arbitrary roots is not asserted. -/
def compactCenterRoot : Subgroup.center compactIdentityComponent →* rootsOfUnity 27 ℂ where
  toFun g := ⟨Units.mk0 (compactCenterScalar g) (compactCenterScalar_ne_zero g),
    (mem_rootsOfUnity' 27 _).mpr (compactCenterScalar_pow g)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact compactCenterScalar.map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact compactCenterScalar.map_mul g h

theorem compactCenterRoot_injective : Function.Injective compactCenterRoot := by
  intro g h he
  apply compactCenterScalar_injective
  exact congrArg (fun z : rootsOfUnity 27 ℂ => ((z : ℂˣ) : ℂ)) he

instance compactCenter_finite : Finite (Subgroup.center compactIdentityComponent) :=
  Finite.of_injective compactCenterRoot compactCenterRoot_injective

instance compactCenter_isCyclic : IsCyclic (Subgroup.center compactIdentityComponent) :=
  isCyclic_of_injective compactCenterRoot compactCenterRoot_injective

theorem compactCenter_card_dvd : Nat.card (Subgroup.center compactIdentityComponent) ∣ 27 := by
  simpa only [Complex.card_rootsOfUnity] using
    Subgroup.card_dvd_of_injective compactCenterRoot compactCenterRoot_injective

theorem compact_center_pow (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.center compactIdentityComponent) : g ^ 27 = 1 := by
  have he : (⟨g, hg⟩ : Subgroup.center compactIdentityComponent) ^ 27 = 1 := by
    apply compactCenterScalar_injective
    rw [map_pow, map_one]
    exact compactCenterScalar_pow _
  exact congrArg Subtype.val he

end

end Math.E6.Minuscule

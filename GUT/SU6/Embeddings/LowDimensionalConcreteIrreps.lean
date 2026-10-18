import GUT.SU6.Embeddings.HighestWeightBridge
import GUT.SU6.Embeddings.LowDimensionalCenterActions

/-!
# Concrete low-dimensional irreducible representations

This file realizes the defining `SU(3)` color triplet as an actual matrix
representation and proves its irreducibility directly.  Together with the
already constructed weak doublet, it also supplies concrete highest-weight
certificates for the two defining representations.
-/

namespace GUT
namespace LowDimensionalConcreteIrreps

open CompactEmbeddingClassification
open HighestWeightBridge
open LowDimensionalCenterActions

noncomputable section

abbrev ColorStd := Fin 3 → ℂ

/-!
## The one-dimensional trivial block
-/

def trivialLine (G : Type*) [Monoid G] : Representation ℂ G ℂ :=
  Representation.trivial ℂ G ℂ

/-- Every one-dimensional trivial complex representation is irreducible. -/
theorem trivialLine_isIrreducible (G : Type*) [Monoid G] :
    Representation.IsIrreducible (trivialLine G) := by
  let : Nontrivial (Subrepresentation (trivialLine G)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.ext
    exact h
  obtain ⟨z, hzS, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSub
  have hOne : (1 : ℂ) ∈ S.toSubmodule := by
    have hScaled := S.toSubmodule.smul_mem z⁻¹ hzS
    simpa [inv_mul_cancel₀ hz0] using hScaled
  apply top_unique
  change (⊤ : Submodule ℂ ℂ) ≤ S.toSubmodule
  intro z _
  simpa using S.toSubmodule.smul_mem z hOne

def su2Trivial_highestWeightCertificate :
    SU2HighestWeightCertificate (trivialLine SU2) where
  highestWeight := 0
  highestWeightVector := 1
  highestWeightVector_ne_zero := one_ne_zero
  center_eigenvalue := by simp [trivialLine]
  dimension_formula := by simp
  trivial_action_of_highestWeight_eq_zero := by
    intro _ g
    ext
    simp [trivialLine]

def su3Trivial_highestWeightCertificate :
    SU3HighestWeightCertificate (trivialLine SU3) where
  firstWeight := 0
  secondWeight := 0
  dimension_formula := by
    simp [LowDimensionalIrreps.SU3TwiceDimension]
  trivial_action_of_highestWeights_eq_zero := by
    intro _ _ g
    ext
    simp [trivialLine]

/-- The defining representation of `SU(3)` on `C^3`. -/
def su3Defining : Representation ℂ SU3 ColorStd where
  toFun g := Matrix.toLin' ((g : SU3) : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := by
    change Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) ℂ) = LinearMap.id
    exact Matrix.toLin'_one
  map_mul' := by
    intro g h
    change
      Matrix.toLin'
          (((g : SU3) : Matrix (Fin 3) (Fin 3) ℂ) *
            ((h : SU3) : Matrix (Fin 3) (Fin 3) ℂ)) =
        (Matrix.toLin' ((g : SU3) : Matrix (Fin 3) (Fin 3) ℂ)).comp
          (Matrix.toLin' ((h : SU3) : Matrix (Fin 3) (Fin 3) ℂ))
    exact Matrix.toLin'_mul
      ((g : SU3) : Matrix (Fin 3) (Fin 3) ℂ)
      ((h : SU3) : Matrix (Fin 3) (Fin 3) ℂ)

/-- The diagonal `SU(3)` element which is `+1` in coordinate `i` and `-1`
in the other two coordinates. -/
def su3SignElement (i : Fin 3) : SU3 :=
  ⟨Matrix.diagonal (fun j : Fin 3 => if j = i then 1 else -1), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases i <;> fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [Matrix.det_diagonal]
      fin_cases i <;> simp [Fin.prod_univ_succ]⟩

theorem su3SignElement_zero_ne_one : su3SignElement 0 ≠ 1 := by
  intro h
  have hEntry := congrArg
    (fun g : SU3 => (((g : SU3) : Matrix (Fin 3) (Fin 3) ℂ) 1 1)) h
  norm_num [su3SignElement] at hEntry

theorem su3SignElement_action (i : Fin 3) (v : ColorStd) :
    su3Defining (su3SignElement i) v =
      fun j => (if j = i then 1 else -1) * v j := by
  ext j
  simp [su3Defining, su3SignElement, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal]

theorem sign_isolates_coordinate (i : Fin 3) (v : ColorStd) :
    v + su3Defining (su3SignElement i) v =
      (2 * v i) • Pi.basisFun ℂ (Fin 3) i := by
  rw [su3SignElement_action]
  ext j
  by_cases hji : j = i
  · subst j
    simp [Pi.basisFun_apply]
    ring
  · simp [Pi.basisFun_apply, hji]

/-- A determinant-one cyclic permutation of the three color coordinates. -/
def su3CycleElement : SU3 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [Matrix.det_fin_three]
      norm_num⟩

def cycleIndex : Fin 3 → Fin 3 := ![1, 2, 0]

theorem su3CycleElement_action (v : ColorStd) :
    su3Defining su3CycleElement v = ![v 2, v 0, v 1] := by
  ext i
  fin_cases i <;>
    simp [su3Defining, su3CycleElement, Matrix.toLin'_apply, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]

theorem su3CycleElement_basis (i : Fin 3) :
    su3Defining su3CycleElement (Pi.basisFun ℂ (Fin 3) i) =
      Pi.basisFun ℂ (Fin 3) (cycleIndex i) := by
  rw [su3CycleElement_action]
  ext j
  fin_cases i <;> fin_cases j <;> simp [cycleIndex, Pi.basisFun_apply]

/-- The concrete defining color triplet is irreducible. -/
theorem su3Defining_isIrreducible :
    Representation.IsIrreducible su3Defining := by
  let : Nontrivial (Subrepresentation su3Defining) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule ℂ ColorStd) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.ext
    exact h
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSub
  have hcoord : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  have hsign := S.apply_mem_toSubmodule (su3SignElement i) hvS
  have hsum := S.toSubmodule.add_mem hvS hsign
  rw [sign_isolates_coordinate] at hsum
  have hne : (2 : ℂ) * v i ≠ 0 := mul_ne_zero (by norm_num) hi
  have hei := S.toSubmodule.smul_mem (((2 : ℂ) * v i)⁻¹) hsum
  have hei' : Pi.basisFun ℂ (Fin 3) i ∈ S.toSubmodule := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at hei
    exact hei
  have hcycleOne := S.apply_mem_toSubmodule su3CycleElement hei'
  rw [su3CycleElement_basis] at hcycleOne
  have hcycleTwo := S.apply_mem_toSubmodule su3CycleElement hcycleOne
  rw [su3CycleElement_basis] at hcycleTwo
  have hbasis : ∀ j : Fin 3,
      Pi.basisFun ℂ (Fin 3) j ∈ S.toSubmodule := by
    intro j
    fin_cases i <;> fin_cases j <;>
      first | exact hei' | exact hcycleOne | exact hcycleTwo
  apply top_unique
  change (⊤ : Submodule ℂ ColorStd) ≤ S.toSubmodule
  intro w _
  have hw :
      w = w 0 • Pi.basisFun ℂ (Fin 3) 0 +
        w 1 • Pi.basisFun ℂ (Fin 3) 1 +
        w 2 • Pi.basisFun ℂ (Fin 3) 2 := by
    ext j
    fin_cases j <;> simp [Pi.basisFun_apply]
  rw [hw]
  exact S.toSubmodule.add_mem
    (S.toSubmodule.add_mem
      (S.toSubmodule.smul_mem (w 0) (hbasis 0))
      (S.toSubmodule.smul_mem (w 1) (hbasis 1)))
    (S.toSubmodule.smul_mem (w 2) (hbasis 2))

/-- The already concrete weak doublet carries the expected highest weight
one certificate. -/
def su2Defining_highestWeightCertificate :
    SU2HighestWeightCertificate su2Defining where
  highestWeight := 1
  highestWeightVector := Pi.basisFun ℂ (Fin 2) 0
  highestWeightVector_ne_zero := by
    intro h
    have h0 := congrFun h 0
    norm_num [Pi.basisFun_apply] at h0
  center_eigenvalue := by
    rw [su2Defining_center_action]
    simp
  dimension_formula := by
    simp [WeakStd]
  trivial_action_of_highestWeight_eq_zero := by simp

/-- The concrete color triplet carries the expected `(1,0)` dimension
certificate. -/
def su3Defining_highestWeightCertificate :
    SU3HighestWeightCertificate su3Defining where
  firstWeight := 1
  secondWeight := 0
  dimension_formula := by
    simp [ColorStd, LowDimensionalIrreps.SU3TwiceDimension]
  trivial_action_of_highestWeights_eq_zero := by simp

end

end LowDimensionalConcreteIrreps
end GUT

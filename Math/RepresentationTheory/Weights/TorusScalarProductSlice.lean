import Math.RepresentationTheory.Weights.TorusWeightProducts

/-! A unique scalar-weight summand is the whole actual weight space,
with every commuting group action retained. -/
namespace Math.TorusScalarProductSlice
set_option autoImplicit false
noncomputable section
open Representation TorusWeightSlice
variable {G K I : Type*} [Group G] [Group K] [DecidableEq I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (r : ∀ i, Representation ℂ (G × K) (V i)) (t : Circle →* G)
  (w : I → ℤ)
  (hw : ∀ i z x, r i (t z,1) x=(z : ℂ)^(w i) • x)
  (j : I) (hj : ∀ i, w i=w j → i=j)

abbrev source := action (FiniteBlockHom.action r) t (w j)
abbrev Carrier : Type _ := Space (FiniteBlockHom.action r) t (w j)

omit [DecidableEq I] in
include hw hj in
theorem off_weight (x : Carrier r t w j) (i : I) (hi : i≠j) : x.val i=0 := by
  apply eigen_zero_of_ne (show w i≠w j from fun he => hi (hj i he))
  intro z
  exact (hw i z (x.val i)).symm.trans (congrFun (x.property z) i)

def forward : IntertwiningMap (source r t w j) (residual (r j)) where
  toLinearMap := (LinearMap.proj j).comp (Space (FiniteBlockHom.action r) t (w j)).subtype
  isIntertwining' _ := rfl

include hw in
def backward : V j →ₗ[ℂ] Carrier r t w j :=
  LinearMap.codRestrict _ (LinearMap.single ℂ V j) (by
    intro x z
    funext i
    change r i (t z,1) (Pi.single j x i)=(z : ℂ)^(w j) • Pi.single j x i
    by_cases hi : i=j
    · subst i
      simpa only [Pi.single_eq_same] using hw j z x
    · simp only [Pi.single_eq_of_ne hi, map_zero, smul_zero])

include hw hj in
theorem backward_forward (x : Carrier r t w j) : backward r t w j (hw := hw) (forward r t w j x)=x := by
  apply Subtype.ext
  funext i
  by_cases hi : i=j
  · subst i
    change (Pi.single j (x.val j) : ∀ i, V i) j=x.val j
    exact Pi.single_eq_same j (x.val j)
  · change (Pi.single j (x.val j) : ∀ i, V i) i=x.val i
    rw [Pi.single_eq_of_ne hi, off_weight r t w j (hw := hw) (hj := hj) x i hi]

theorem forward_backward (x : V j) : forward r t w j (backward r t w j (hw := hw) x)=x := by
  change (Pi.single j x : ∀ i, V i) j=x
  exact Pi.single_eq_same j x

def equivalence : Representation.Equiv (source r t w j) (residual (r j)) where
  toLinearEquiv :=
    { toLinearMap := (forward r t w j).toLinearMap
      invFun := backward r t w j (hw := hw)
      left_inv := backward_forward r t w j (hw := hw) (hj := hj)
      right_inv := forward_backward r t w j (hw := hw) }
  isIntertwining' := (forward r t w j).isIntertwining'

omit [DecidableEq I] in
include hw in
theorem absent_zero (n : ℤ) (hn : ∀ i, w i≠n)
    (x : Space (FiniteBlockHom.action r) t n) : x=0 := by
  apply Subtype.ext
  funext i
  apply eigen_zero_of_ne (hn i)
  intro z
  exact (hw i z (x.val i)).symm.trans (congrFun (x.property z) i)

end
end Math.TorusScalarProductSlice

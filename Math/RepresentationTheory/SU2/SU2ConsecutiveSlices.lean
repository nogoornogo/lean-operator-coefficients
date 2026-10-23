import Math.RepresentationTheory.SU2.SU2StringSliceSum
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! A nonnegative SU2 weight slice is the corresponding whole multiplicity
plus the next weight slice. This is an actual retained-action equivalence,
not a difference of dimensions or characters. -/
namespace Math.SU2ConsecutiveSlices
set_option autoImplicit false
noncomputable section
open Representation TorusWeightSlice SplitRepresentationProjection
open scoped TensorProduct

theorem string_self (k : ℕ) : SU2WeightSlice.InString k (k : ℤ) := by
  dsimp [SU2WeightSlice.InString]
  omega

theorem string_step (m k : ℕ) : SU2WeightSlice.InString m (k : ℤ) ↔
    m=k ∨ SU2WeightSlice.InString m ((k : ℤ)+2) := by
  dsimp [SU2WeightSlice.InString]
  omega

variable {K : Type*} [Group K] (N : ℕ)
  {U : Fin (N+1) → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  (s : ∀ i, Representation ℂ K (U i)) (k : Fin (N+1))
@[reducible] local instance (i : Fin (N+1)) :
    AddCommGroup (Sym[ℂ]^i.val WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (i : Fin (N+1)) : AddCommGroup
    ((Sym[ℂ]^i.val WeakDoubletScalars.Doublet) ⊗[ℂ] U i) := inferInstance
abbrev degree (i : Fin (N+1)) := i.val
abbrev Selected (n : ℤ) := SU2StringSliceSum.Selected (degree N) n

def indexEquivalence : Option (Selected N ((k.val : ℤ)+2)) ≃ Selected N (k.val : ℤ) where
  toFun x := match x with
    | none => ⟨k, string_self k.val⟩
    | some i => ⟨i.val, (string_step i.val.val k.val).mpr (Or.inr i.property)⟩
  invFun i := if hi : i.val=k then none else
    some ⟨i.val, ((string_step i.val.val k.val).mp i.property).resolve_left (by
      intro h
      exact hi (Fin.ext h))⟩
  left_inv x := by
    cases x with
    | none => simp
    | some i =>
      have hn : i.val≠k := by
        intro h
        have hp := i.property
        change SU2WeightSlice.InString i.val.val ((k.val : ℤ)+2) at hp
        rw [h] at hp
        dsimp [SU2WeightSlice.InString] at hp
        omega
      simp [hn]
  right_inv i := by
    apply Subtype.ext
    by_cases hi : i.val=k <;> simp [hi]

def splitSelected : Representation.Equiv
    (SU2StringSliceSum.target s (degree N) (k.val : ℤ))
    ((s k).prod (SU2StringSliceSum.target s (degree N) ((k.val : ℤ)+2))) where
  toLinearEquiv :=
    (LinearEquiv.piCongrLeft' ℂ (fun i : Selected N (k.val : ℤ) => U i.val)
      (indexEquivalence N k).symm).trans (LinearEquiv.piOptionEquivProd ℂ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · funext i; rfl

abbrev total := SU2StringSliceSum.source s (degree N)

/-- Consecutive slices differ by exactly the actual multiplicity at k.
Both equivalence directions retain the independent K representation. -/
def equivalence : Representation.Equiv
    (action (total N s) TauCeti.SU2.torusHom (k.val : ℤ))
    ((s k).prod (action (total N s) TauCeti.SU2.torusHom ((k.val : ℤ)+2))) :=
  (SU2StringSliceSum.equivalence s (degree N) (k.val : ℤ)).trans
    ((splitSelected N s k).trans
      (prodEquiv (.refl (s k))
        (SU2StringSliceSum.equivalence s (degree N) ((k.val : ℤ)+2)).symm))

end
end Math.SU2ConsecutiveSlices

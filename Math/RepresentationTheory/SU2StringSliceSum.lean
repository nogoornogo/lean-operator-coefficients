import Math.RepresentationTheory.SU2WeightSlice
import Math.RepresentationTheory.TorusWeightProducts

/-! A complete SU2 isotypic sum has an actual weight-space equivalence
with the retained multiplicity representations whose strings contain the
selected weight. The selection condition is proved interval/parity. -/
namespace Math.SU2StringSliceSum
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor TorusWeightSlice
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {K I : Type*} [Group K]
  {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  (s : ∀ i, Representation ℂ K (U i)) (m : I → ℕ) (n : ℤ)
@[reducible] local instance (i : I) : AddCommGroup (Sym[ℂ]^(m i) WeakDoubletScalars.Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (i : I) : AddCommGroup
    ((Sym[ℂ]^(m i) WeakDoubletScalars.Doublet) ⊗[ℂ] U i) := inferInstance

abbrev Selected := {i : I // SU2WeightSlice.InString (m i) n}
abbrev piece (i : I) := SU2WeightSlice.source (s i) (m i)
abbrev source := FiniteBlockHom.action (piece s m)
abbrev target := FiniteBlockHom.action (fun i : Selected m n => s i.val)
abbrev allSlices := FiniteBlockHom.action (fun i => SU2WeightSlice.slice (s i) (m i) n)

abbrev AllCarrier := ∀ i, Space (piece s m i) TauCeti.SU2.torusHom n
abbrev SelectedCarrier := ∀ i : Selected m n, U i.val
local instance : DecidablePred (fun i : I => SU2WeightSlice.InString (m i) n) :=
  Classical.decPred _

def filterForward : IntertwiningMap (allSlices s m n) (target s m n) where
  toLinearMap := LinearMap.pi (fun i : Selected m n =>
    (SU2WeightSlice.equivalence (s i.val) (m i.val) n i.property).symm.toLinearEquiv.toLinearMap.comp
      (LinearMap.proj i.val))
  isIntertwining' k := by
    apply LinearMap.ext
    intro x
    funext i
    exact (SU2WeightSlice.equivalence (s i.val) (m i.val) n i.property).symm.isIntertwining _ _ k (x i.val)

def filterBackward : SelectedCarrier (U := U) m n →ₗ[ℂ] AllCarrier s m n :=
  LinearMap.pi (fun i => if hi : SU2WeightSlice.InString (m i) n then
    (SU2WeightSlice.equivalence (s i) (m i) n hi).toLinearEquiv.toLinearMap.comp
      (LinearMap.proj (⟨i,hi⟩ : Selected m n)) else 0)

theorem forward_apply (x : AllCarrier s m n) (i : Selected m n) :
    filterForward s m n x i=
      (SU2WeightSlice.equivalence (s i.val) (m i.val) n i.property).symm (x i.val) := rfl

theorem backward_present (i : I) (hi : SU2WeightSlice.InString (m i) n)
    (x : SelectedCarrier (U := U) m n) :
    filterBackward s m n x i=SU2WeightSlice.equivalence (s i) (m i) n hi (x ⟨i,hi⟩) := by
  simp only [filterBackward, LinearMap.pi_apply, dite_eq_left hi, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rfl

theorem backward_absent (i : I) (hi : ¬SU2WeightSlice.InString (m i) n)
    (x : SelectedCarrier (U := U) m n) : filterBackward s m n x i=0 := by
  simp only [filterBackward, LinearMap.pi_apply, dite_eq_right hi, LinearMap.zero_apply]

theorem backward_forward (x : AllCarrier s m n) :
    filterBackward s m n (filterForward s m n x)=x := by
  funext i
  by_cases hi : SU2WeightSlice.InString (m i) n
  · rw [backward_present s m n i hi, forward_apply]
    exact (SU2WeightSlice.equivalence (s i) (m i) n hi).apply_symm_apply _
  · rw [backward_absent s m n i hi]
    exact (SU2WeightSlice.absent_zero (s i) (m i) n hi (x i)).symm

theorem forward_backward (x : SelectedCarrier (U := U) m n) :
    filterForward s m n (filterBackward s m n x)=x := by
  funext i
  rw [forward_apply, backward_present s m n i.val i.property]
  exact (SU2WeightSlice.equivalence (s i.val) (m i.val) n i.property).symm_apply_apply _

def filterEquivalence : Representation.Equiv (allSlices s m n) (target s m n) where
  toLinearEquiv :=
    { toLinearMap := (filterForward s m n).toLinearMap
      invFun := filterBackward s m n
      left_inv := backward_forward s m n
      right_inv := forward_backward s m n }
  isIntertwining' := (filterForward s m n).isIntertwining'

/-- The whole weight space, with every commuting action, is the product of
the selected multiplicities. No dimension or numerical multiplicity occurs. -/
def equivalence : Representation.Equiv (action (source s m) TauCeti.SU2.torusHom n) (target s m n) :=
  (TorusWeightProducts.equivalence (piece s m) TauCeti.SU2.torusHom n).trans
    (filterEquivalence s m n)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {rho : Representation ℂ (WeakDoubletScalars.Group × K) V}

def ofEquiv (e : Representation.Equiv (source s m) rho) :
    Representation.Equiv (action rho TauCeti.SU2.torusHom n) (target s m n) :=
  (TorusWeightSlice.transport rho TauCeti.SU2.torusHom e.symm n).trans (equivalence s m n)

end
end Math.SU2StringSliceSum

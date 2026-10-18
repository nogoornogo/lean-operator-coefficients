import Math.RepresentationTheory.Characters.CompactHomSupport
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.InvariantCoefficientTransport

/-! Invariant coefficient support from constituent support, using compact Hom
symmetry. Continuity and equivalent finite normed models are explicit inputs;
no character integral or multiplicity is evaluated. -/
namespace Math.CompactCoefficientSupport
set_option autoImplicit false
noncomputable section
open Representation ContinuousRepresentationScope
variable {G A B C D : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]

def homEquiv {a : Representation ℂ G A} {b : Representation ℂ G B}
    {c : Representation ℂ G C} {d : Representation ℂ G D}
    (e : Representation.Equiv a c) (t : Representation.Equiv b d) :
    IntertwiningMap a b ≃ₗ[ℂ] IntertwiningMap c d where
  toFun f := t.toIntertwiningMap.comp (f.comp e.symm.toIntertwiningMap)
  invFun f := t.symm.toIntertwiningMap.comp (f.comp e.toIntertwiningMap)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by
    ext x
    change t (f (e.symm x) + g (e.symm x)) = _
    exact map_add t _ _
  map_smul' z f := by
    ext x
    change t (z • f (e.symm x)) = z • t (f (e.symm x))
    exact map_smul t z _

variable {V W : Type*} [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem reverse_models (a : Representation ℂ G A) (b : Representation ℂ G B)
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (ea : Representation.Equiv a rho) (eb : Representation.Equiv b sigma)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    SelectionCriteria.Allowed (IntertwiningMap a b) ↔
      SelectionCriteria.Allowed (IntertwiningMap b a) :=
  (SelectionCriteria.allowed_equiv (homEquiv ea eb)).trans
    ((CompactHomSupport.nonzero_iff rho sigma hr hs).trans
      (SelectionCriteria.allowed_equiv (homEquiv eb ea)).symm)

theorem coefficient_iff (a : Representation ℂ G A) (b : Representation ℂ G B)
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (ea : Representation.Equiv a rho) (eb : Representation.Equiv b sigma)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (selfDual : Representation.Equiv b b.dual) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b)) ↔
      SelectionCriteria.Allowed (IntertwiningMap b a) :=
  (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv a b)).trans
    ((SelectionCriteria.allowed_equiv
      (InvariantTensorCurry.postcompose a b.dual selfDual.symm)).trans
      (reverse_models a b rho sigma ea eb hr hs))

end
end Math.CompactCoefficientSupport

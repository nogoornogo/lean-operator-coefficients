import Math.RepresentationTheory.InvariantPairingTransport
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Nonzero invariant coefficients in field order, with contragredient slots. -/

set_option autoImplicit false

namespace Math.OrderedInvariantPairing

noncomputable section

open Representation SplitRepresentationProjection
open scoped TensorProduct

variable {H A B C D R S : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup R] [Module ℂ R] [AddCommGroup S] [Module ℂ S]

def swapMiddle (a : Representation ℂ H A) (b : Representation ℂ H B)
    (c : Representation ℂ H C) (d : Representation ℂ H D) :
    Representation.Equiv ((a.tprod b).tprod (c.tprod d))
      ((a.tprod c).tprod (b.tprod d)) where
  toLinearEquiv := TensorProduct.tensorTensorTensorComm ℂ A B C D
  isIntertwining' g := by
    ext x y z w
    rfl

theorem coefficient_comp_equiv_ne_zero
    {a : Representation ℂ H A} {b : Representation ℂ H B}
    (f : IntertwiningMap b (Representation.trivial ℂ H ℂ)) (hf : f ≠ 0)
    (e : Representation.Equiv a b) : f.comp e.toIntertwiningMap ≠ 0 := by
  intro he
  apply hf
  apply DFunLike.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he y

variable {a : Representation ℂ H A} {b : Representation ℂ H B}
  {c : Representation ℂ H C} {d : Representation ℂ H D}
  {r : Representation ℂ H R} {s : Representation ℂ H S}

/-- The order is A,C,B*,D*, with the evaluation pairs A/B* and C/D*. -/
theorem exists_ordered_coefficient [Nontrivial R] [Nontrivial S]
    (sa : Split a r) (sb : Split b r) (sc : Split c s) (sd : Split d s) :
    ∃ f : IntertwiningMap ((a.tprod c).tprod (b.dual.tprod d.dual))
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  let f := InvariantPairing.pulledCoefficient sa.project sb.dual.project
    sc.project sd.dual.project
  have hf : f ≠ 0 := InvariantPairing.pulledCoefficient_ne_zero _ _ _ _
    (fun x => ⟨sa.embed x, sa.left_inv x⟩)
    (fun x => ⟨sb.dual.embed x, sb.dual.left_inv x⟩)
    (fun x => ⟨sc.embed x, sc.left_inv x⟩)
    (fun x => ⟨sd.dual.embed x, sd.dual.left_inv x⟩)
  exact ⟨f.comp (swapMiddle a c b.dual d.dual).toIntertwiningMap,
    coefficient_comp_equiv_ne_zero f hf _⟩

/-- The order is D*,B*,A,C, for down*,up*,Q,L applications. -/
theorem exists_dual_first_coefficient [Nontrivial R] [Nontrivial S]
    (sa : Split a r) (sb : Split b r) (sc : Split c s) (sd : Split d s) :
    ∃ f : IntertwiningMap ((d.dual.tprod b.dual).tprod (a.tprod c))
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_ordered_coefficient sa sb sc sd
  let swap := (Representation.TensorProduct.comm d.dual b.dual).toIntertwiningMap.tensor
    (IntertwiningMap.id (a.tprod c))
  let e := Representation.TensorProduct.comm (b.dual.tprod d.dual) (a.tprod c)
  let g := (f.comp e.toIntertwiningMap).comp swap
  have hg : g ≠ 0 := by
    intro he
    apply hf
    apply DFunLike.ext
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    have hs : Function.Surjective swap := by
      exact TensorProduct.map_surjective
        (Representation.TensorProduct.comm d.dual b.dual).surjective Function.surjective_id
    obtain ⟨y, rfl⟩ := hs z
    exact DFunLike.congr_fun he y
  exact ⟨g, hg⟩

end
end Math.OrderedInvariantPairing

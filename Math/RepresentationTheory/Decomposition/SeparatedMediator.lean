import Math.RepresentationTheory.Decomposition.CommonIrreducible
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Deriving mediator support and mass-block constraints from equivariance
and actual constituent separation. No forbidden block is assumed zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Math.SeparatedMediator
noncomputable section
open Representation

variable {H V W X : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]
  (r : Representation ℂ H V) (s : Representation ℂ H W)

theorem map_zero (hr : IsSemisimpleRepresentation r) (hn : ¬ CommonIrreducible.Shares r s)
    (f : IntertwiningMap r s) : f = 0 :=
  (CommonIrreducible.all_zero_iff r s hr).mpr hn f

def coreBlock (f : IntertwiningMap (r.prod s) (r.prod s)) : IntertwiningMap r r :=
  (IntertwiningMap.fst ℂ r s).comp (f.comp (IntertwiningMap.inl ℂ r s))

theorem core_stable (hr : IsSemisimpleRepresentation r)
    (hn : ¬ CommonIrreducible.Shares r s)
    (f : IntertwiningMap (r.prod s) (r.prod s)) (x : V) :
    f (x, 0) = (coreBlock r s f x, 0) := by
  have hz := map_zero r s hr hn
    ((IntertwiningMap.snd ℂ r s).comp (f.comp (IntertwiningMap.inl ℂ r s)))
  apply Prod.ext
  · rfl
  · exact DFunLike.congr_fun hz x

theorem projection_stable (hs : IsSemisimpleRepresentation s)
    (hn : ¬ CommonIrreducible.Shares s r)
    (f : IntertwiningMap (r.prod s) (r.prod s)) (z : V × W) :
    (f z).1 = coreBlock r s f z.1 := by
  have hz := map_zero s r hs hn
    ((IntertwiningMap.fst ℂ r s).comp (f.comp (IntertwiningMap.inr ℂ r s)))
  have hzero : (f (0, z.2)).1 = 0 := DFunLike.congr_fun hz z.2
  have hsplit : f z = f (z.1, 0) + f (0, z.2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [hsplit]
  change (f (z.1, 0)).1 + (f (0, z.2)).1 = _
  rw [hzero, add_zero]
  rfl

theorem source_support (a : Representation ℂ H X) (ha : IsSemisimpleRepresentation a)
    (hn : ¬ CommonIrreducible.Shares a s) (J : IntertwiningMap a (r.prod s)) (x : X) :
    J x = ((J x).1, 0) := by
  have hz := map_zero a s ha hn ((IntertwiningMap.snd ℂ r s).comp J)
  exact Prod.ext rfl (DFunLike.congr_fun hz x)

theorem dual_support (a : Representation ℂ H X) (ha : IsSemisimpleRepresentation a)
    (hn : ¬ CommonIrreducible.Shares a s.dual)
    (K : IntertwiningMap a (r.prod s).dual) (y : X) (z : V × W) :
    K y z = K y (z.1, 0) := by
  have hz := map_zero a s.dual ha hn
    ((SplitRepresentationProjection.dualMap (IntertwiningMap.inr ℂ r s)).comp K)
  have hzero : K y (0, z.2) = 0 := DFunLike.congr_fun (DFunLike.congr_fun hz y) z.2
  have hsplit : K y z = K y (z.1, 0) + K y (0, z.2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [hsplit, hzero, add_zero]

def coreMass (hr : IsSemisimpleRepresentation r) (hn : ¬ CommonIrreducible.Shares r s)
    (N : Representation.Equiv (r.prod s) (r.prod s)) : Representation.Equiv r r where
  toLinearEquiv :=
    { toLinearMap := (coreBlock r s N.toIntertwiningMap).toLinearMap
      invFun := coreBlock r s N.symm.toIntertwiningMap
      left_inv := by
        intro x
        have h : (coreBlock r s N.symm.toIntertwiningMap
            (coreBlock r s N.toIntertwiningMap x), 0) = (x, (0 : W)) := by
          calc
            _ = N.symm (coreBlock r s N.toIntertwiningMap x, 0) :=
              (core_stable r s hr hn N.symm.toIntertwiningMap _).symm
            _ = N.symm (N (x, 0)) := congrArg N.symm
              (core_stable r s hr hn N.toIntertwiningMap x).symm
            _ = (x, 0) := N.symm_apply_apply _
        exact congrArg Prod.fst h
      right_inv := by
        intro x
        have h : (coreBlock r s N.toIntertwiningMap
            (coreBlock r s N.symm.toIntertwiningMap x), 0) = (x, (0 : W)) := by
          calc
            _ = N (coreBlock r s N.symm.toIntertwiningMap x, 0) :=
              (core_stable r s hr hn N.toIntertwiningMap _).symm
            _ = N (N.symm (x, 0)) := congrArg N
              (core_stable r s hr hn N.symm.toIntertwiningMap x).symm
            _ = (x, 0) := N.apply_symm_apply _
        exact congrArg Prod.fst h }
  isIntertwining' := (coreBlock r s N.toIntertwiningMap).isIntertwining'

theorem coreMass_apply (hr : IsSemisimpleRepresentation r)
    (hn : ¬ CommonIrreducible.Shares r s)
    (N : Representation.Equiv (r.prod s) (r.prod s)) (x : V) :
    coreMass r s hr hn N x = (N (x, 0)).1 := rfl

theorem coreMass_compat (hr : IsSemisimpleRepresentation r)
    (hn : ¬ CommonIrreducible.Shares r s)
    (N : Representation.Equiv (r.prod s) (r.prod s)) (x : V) :
    N (x, 0) = (coreMass r s hr hn N x, 0) :=
  core_stable r s hr hn N.toIntertwiningMap x

/-- Equal summands permit equivariant mixing. This invertible algebraic
control does not assert a positive physical mass-squared operator. -/
def repeatedSwap : Representation.Equiv (r.prod r) (r.prod r) where
  toLinearEquiv := LinearEquiv.prodComm ℂ V V
  isIntertwining' _g := LinearMap.ext (fun _ => rfl)

theorem repeatedSwap_core_zero : coreBlock r r (repeatedSwap r).toIntertwiningMap = 0 := by
  apply DFunLike.ext
  intro x
  rfl

theorem repeatedSwap_moves (x : V) : repeatedSwap r (x, 0) = (0, x) := rfl

end
end Math.SeparatedMediator

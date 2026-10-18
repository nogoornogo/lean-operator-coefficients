import Math.RepresentationTheory.OrderedInvariantPairing

/-! Nonzero invariant functionals for independent group actions, with
regrouping from field order to gauge/multiplicity order. -/

namespace Math.ExternalInvariantTensor
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G H : Type*} [Group G] [Group H]
  {A B C D X Y Z W : Type*}
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  [AddCommMonoid C] [Module ℂ C] [AddCommMonoid D] [Module ℂ D]
  [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
  [AddCommMonoid Z] [Module ℂ Z] [AddCommMonoid W] [Module ℂ W]

def external (a : Representation ℂ G A) (x : Representation ℂ H X) :=
  Representation.tprod (a.comp (MonoidHom.fst G H)) (x.comp (MonoidHom.snd G H))

def tensorEquiv {a : Representation ℂ G A} {b : Representation ℂ G B}
    {c : Representation ℂ G C} {d : Representation ℂ G D}
    (e : Representation.Equiv a b) (f : Representation.Equiv c d) :
    Representation.Equiv (a.tprod c) (b.tprod d) where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  isIntertwining' g := by
    ext v w
    exact congrArg₂ (fun v w => v ⊗ₜ[ℂ] w)
      (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)
      (IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g w)

def externalEquiv {a : Representation ℂ G A} {b : Representation ℂ G B}
    {x : Representation ℂ H X} {y : Representation ℂ H Y}
    (e : Representation.Equiv a b) (f : Representation.Equiv x y) :
    Representation.Equiv (external a x) (external b y) :=
  tensorEquiv (SplitRepresentationProjection.restrictEquiv e (MonoidHom.fst G H))
    (SplitRepresentationProjection.restrictEquiv f (MonoidHom.snd G H))

def regroupPair (a : Representation ℂ G A) (b : Representation ℂ G B)
    (x : Representation ℂ H X) (y : Representation ℂ H Y) :
    Representation.Equiv ((external a x).tprod (external b y))
      (external (a.tprod b) (x.tprod y)) where
  toLinearEquiv := TensorProduct.tensorTensorTensorComm ℂ A X B Y
  isIntertwining' g := by ext v w z t; rfl

/-- The same regrouping for a diagonal action of a single group. -/
def regroupPairDiagonal (a : Representation ℂ G A) (b : Representation ℂ G B)
    (x : Representation ℂ G X) (y : Representation ℂ G Y) :
    Representation.Equiv ((a.tprod x).tprod (b.tprod y))
      ((a.tprod b).tprod (x.tprod y)) where
  toLinearEquiv := TensorProduct.tensorTensorTensorComm ℂ A X B Y
  isIntertwining' g := by ext v w z t; rfl

def regroupFour (a : Representation ℂ G A) (b : Representation ℂ G B)
    (c : Representation ℂ G C) (d : Representation ℂ G D)
    (x : Representation ℂ H X) (y : Representation ℂ H Y)
    (z : Representation ℂ H Z) (w : Representation ℂ H W) :
    Representation.Equiv
      (((external a x).tprod (external b y)).tprod
        ((external c z).tprod (external d w)))
      (external ((a.tprod b).tprod (c.tprod d)) ((x.tprod y).tprod (z.tprod w))) :=
  (tensorEquiv (regroupPair a b x y) (regroupPair c d z w)).trans
    (regroupPair (a.tprod b) (c.tprod d) (x.tprod y) (z.tprod w))

def coefficient {a : Representation ℂ G A} {x : Representation ℂ H X}
    (f : IntertwiningMap a (Representation.trivial ℂ G ℂ))
    (p : IntertwiningMap x (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap (external a x) (Representation.trivial ℂ (G × H) ℂ) where
  toLinearMap := (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map f.toLinearMap p.toLinearMap)
  isIntertwining' g := by
    ext v w
    change f (a g.1 v) * p (x g.2 w) = f v * p w
    rw [IntertwiningMap.isIntertwining _ _ f, IntertwiningMap.isIntertwining _ _ p]
    rfl

@[simp] theorem coefficient_tmul {a : Representation ℂ G A} {x : Representation ℂ H X}
    (f : IntertwiningMap a (Representation.trivial ℂ G ℂ))
    (p : IntertwiningMap x (Representation.trivial ℂ H ℂ)) (v : A) (w : X) :
    coefficient f p (v ⊗ₜ[ℂ] w) = f v * p w := rfl

theorem coefficient_ne_zero {a : Representation ℂ G A} {x : Representation ℂ H X}
    (f : IntertwiningMap a (Representation.trivial ℂ G ℂ))
    (p : IntertwiningMap x (Representation.trivial ℂ H ℂ))
    (hf : f ≠ 0) (hp : p ≠ 0) : coefficient f p ≠ 0 := by
  have hfv : ∃ v, f v ≠ 0 := by
    by_contra h
    apply hf
    ext v
    simpa using not_exists.mp h v
  have hpw : ∃ w, p w ≠ 0 := by
    by_contra h
    apply hp
    ext w
    simpa using not_exists.mp h w
  obtain ⟨v, hv⟩ := hfv
  obtain ⟨w, hw⟩ := hpw
  intro he
  have hz := DFunLike.congr_fun he (v ⊗ₜ[ℂ] w)
  exact (mul_ne_zero hv hw) hz

theorem comp_equiv_ne_zero {a : Representation ℂ G A} {b : Representation ℂ G B}
    (f : IntertwiningMap b (Representation.trivial ℂ G ℂ)) (hf : f ≠ 0)
    (e : Representation.Equiv a b) : f.comp e.toIntertwiningMap ≠ 0 := by
  intro he
  apply hf
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he y

end
end Math.ExternalInvariantTensor

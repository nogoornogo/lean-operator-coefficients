import Physics.FieldTheory.Yukawa.WeylYukawaMass

/-! Invariant couplings from equivariant matter endomorphisms. -/
set_option autoImplicit false
namespace GUT.ProjectedYukawa
noncomputable section
open Representation WeylYukawaMass
variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup V] [Module ℂ V]
  {s : Representation ℂ G S} {r : Representation ℂ G V}

def diagonal (Y : EquivariantYukawa s r) (p : IntertwiningMap r r) : EquivariantYukawa s r where
  toLinearMap :=
    { toFun := fun v => (Y.toLinearMap v).compl₁₂ p.toLinearMap p.toLinearMap
      map_add' := by intros; ext x y; simp
      map_smul' := by intros; ext x y; simp }
  symmetric v := ⟨fun x y => (Y.symmetric v).eq (p x) (p y)⟩
  invariant g v x y := by
    change Y.toLinearMap (s g v) (p (r g x)) (p (r g y)) = _
    rw [p.isIntertwining r r, p.isIntertwining r r]
    exact Y.invariant g v (p x) (p y)

def mixed (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r) : EquivariantYukawa s r where
  toLinearMap :=
    { toFun := fun v => (Y.toLinearMap v).compl₁₂ p.toLinearMap q.toLinearMap +
        (Y.toLinearMap v).compl₁₂ q.toLinearMap p.toLinearMap
      map_add' := by intros; ext x y; simp; ring
      map_smul' := by intros; ext x y; simp }
  symmetric v := by
    constructor
    intro x y
    change Y.toLinearMap v (p x) (q y) + Y.toLinearMap v (q x) (p y) = _
    rw [(Y.symmetric v).eq (p x) (q y), (Y.symmetric v).eq (q x) (p y)]
    exact add_comm _ _
  invariant g v x y := by
    change Y.toLinearMap (s g v) (p (r g x)) (q (r g y)) +
      Y.toLinearMap (s g v) (q (r g x)) (p (r g y)) = _
    rw [p.isIntertwining r r, p.isIntertwining r r, q.isIntertwining r r,
      q.isIntertwining r r, Y.invariant, Y.invariant]
    rfl

def combine (Y Z : EquivariantYukawa s r) (a b : ℂ) : EquivariantYukawa s r where
  toLinearMap := a • Y.toLinearMap + b • Z.toLinearMap
  symmetric v := ((Y.symmetric v).smul a).add ((Z.symmetric v).smul b)
  invariant g v x y := by
    change a * Y.toLinearMap (s g v) (r g x) (r g y) +
      b * Z.toLinearMap (s g v) (r g x) (r g y) = _
    rw [Y.invariant, Z.invariant]
    rfl

theorem evaluated_combination {K : Type*} [Group K]
    (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v)
    (a b : ℂ) (x y : V) :
    (atVacuumOn (InvariantWeylMass.SymmetricMass.zero r)
      (combine (mixed Y p q) (diagonal Y q) a b) f v hv).form x y =
    a * (Y.toLinearMap v (p x) (q y) + Y.toLinearMap v (q x) (p y)) +
      b * Y.toLinearMap v (q x) (q y) := by
  change (0 : ℂ) + _ = _
  exact zero_add _

def family (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r) (a b : ℂ) :=
  combine (mixed Y p q) (diagonal Y q) a b

def projectedForm {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (B : LinearMap.BilinForm ℂ W) (p q : W →ₗ[ℂ] W) (a b : ℂ) :=
  a • (B.compl₁₂ p q + B.compl₁₂ q p) + b • B.compl₁₂ q q

def familyMass {K : Type*} [Group K]
    (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v) (a b : ℂ) :=
  atVacuumOn (InvariantWeylMass.SymmetricMass.zero r) (family Y p q a b) f v hv

theorem familyMass_form {K : Type*} [Group K]
    (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v) (a b : ℂ) :
    (familyMass Y p q f v hv a b).form =
      projectedForm (Y.toLinearMap v) p.toLinearMap q.toLinearMap a b := by
  ext x y
  unfold familyMass family
  rw [evaluated_combination]
  rfl

theorem generated_mass_eq_from_form {K : Type*} [Group K]
    (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v)
    (B C D : InvariantWeylMass.SymmetricMass (r.comp f))
    (hY : Y.toLinearMap v = B.form) (a b : ℂ)
    (hC : C = familyMass Y p q f v hv a b)
    (hD : projectedForm B.form p.toLinearMap q.toLinearMap a b = D.form) : C = D := by
  apply InvariantWeylMass.SymmetricMass.ext
  rw [hC, familyMass_form, hY]
  exact hD

theorem familyMass_congr {K : Type*} [Group K]
    (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v) (a b c d : ℂ)
    (h : family Y p q a b = family Y p q c d) :
    familyMass Y p q f v hv a b = familyMass Y p q f v hv c d := by
  unfold familyMass
  rw [h]

end
end GUT.ProjectedYukawa

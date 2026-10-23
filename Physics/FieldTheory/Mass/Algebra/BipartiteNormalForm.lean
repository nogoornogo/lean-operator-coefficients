import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Math.RepresentationTheory.Multiplicity.FiniteSpectrum

/-! An arbitrary symmetric mass with no same-side pairings has a derived
Dirac presentation. No bilinear normal-form certificate is assumed. -/
namespace Physics.BipartiteNormalForm
set_option autoImplicit false
noncomputable section
open Representation Math.SplitRepresentationProjection
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def NoPairings (r : Representation ℂ G V) (s : Representation ℂ G W) : Prop :=
  ∀ f : IntertwiningMap r s.dual, f = 0

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem prod_left {r : Representation ℂ G V} {s : Representation ℂ G W}
    {t : Representation ℂ G X} (hr : NoPairings r t) (hs : NoPairings s t) :
    NoPairings (r.prod s) t := by
  intro f
  have h1 := hr (f.comp (IntertwiningMap.inl ℂ r s))
  have h2 := hs (f.comp (IntertwiningMap.inr ℂ r s))
  apply DFunLike.ext
  rintro ⟨v,w⟩
  have he : (v,w) = (v,0) + (0,w) := by simp
  rw [he, map_add]
  have e1 := DFunLike.congr_fun h1 v
  have e2 := DFunLike.congr_fun h2 w
  change f (v,0) = 0 at e1
  change f (0,w) = 0 at e2
  simp [e1,e2]

theorem prod_right {r : Representation ℂ G X} {s : Representation ℂ G V}
    {t : Representation ℂ G W} (hs : NoPairings r s) (ht : NoPairings r t) :
    NoPairings r (s.prod t) := by
  intro f
  have h1 := hs ((dualMap (IntertwiningMap.inl ℂ s t)).comp f)
  have h2 := ht ((dualMap (IntertwiningMap.inr ℂ s t)).comp f)
  apply DFunLike.ext
  intro x
  apply LinearMap.ext
  rintro ⟨v,w⟩
  have he : (v,w) = (v,0) + (0,w) := by simp
  rw [he, map_add]
  have e1 := LinearMap.congr_fun (DFunLike.congr_fun h1 x) v
  have e2 := LinearMap.congr_fun (DFunLike.congr_fun h2 x) w
  change f x (v,0) = 0 at e1
  change f x (0,w) = 0 at e2
  simp [e1,e2]

theorem equiv {r : Representation ℂ G V} {s : Representation ℂ G W}
    {r' : Representation ℂ G X} {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {s' : Representation ℂ G Y} (er : Equiv r r') (es : Equiv s s')
    (h : NoPairings r' s') : NoPairings r s := by
  intro f
  have hz := h ((dualMap es.symm.toIntertwiningMap).comp (f.comp er.symm.toIntertwiningMap))
  apply DFunLike.ext
  intro x
  apply LinearMap.ext
  intro y
  have he := LinearMap.congr_fun (DFunLike.congr_fun hz (er x)) (es y)
  simpa using he


def copySlot (n : ℕ) (r : Representation ℂ G V) (i : Fin n) :
    IntertwiningMap r (Math.FiniteSpectrum.copies n r) where
  toLinearMap := LinearMap.single ℂ (fun _ : Fin n => V) i
  isIntertwining' g := by
    ext x j
    by_cases h : i = j
    · subst j; simp [Math.FiniteSpectrum.copies_apply]
    · simp [Math.FiniteSpectrum.copies_apply, Ne.symm h]

theorem copies_left {r : Representation ℂ G V} {s : Representation ℂ G W}
    (h : NoPairings r s) (n : ℕ) : NoPairings (Math.FiniteSpectrum.copies n r) s := by
  intro f
  apply DFunLike.ext
  intro x
  rw [← Finset.univ_sum_single x, map_sum]
  have hz (i : Fin n) : f (Pi.single i (x i)) = 0 :=
    DFunLike.congr_fun (h (f.comp (copySlot n r i))) (x i)
  simp [hz]

theorem copies_right {r : Representation ℂ G V} {s : Representation ℂ G W}
    (h : NoPairings r s) (n : ℕ) : NoPairings r (Math.FiniteSpectrum.copies n s) := by
  intro f
  apply DFunLike.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [← Finset.univ_sum_single y, map_sum]
  have hz (i : Fin n) : f x (Pi.single i (y i)) = 0 :=
    LinearMap.congr_fun (DFunLike.congr_fun
      (h ((dualMap (copySlot n s i)).comp f)) x) (y i)
  simp [hz]

def dualCopiesEquiv (n : ℕ) (r : Representation ℂ G V) :
    Equiv (Math.FiniteSpectrum.copies n r).dual (Math.FiniteSpectrum.copies n r.dual) where
  toLinearEquiv := {
    toFun := fun phi i => phi.comp (LinearMap.single ℂ (fun _ : Fin n => V) i)
    invFun := fun phi => ∑ i, (phi i).comp (LinearMap.proj i)
    left_inv := by
      intro phi; apply LinearMap.ext; intro x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      change (∑ i, phi (Pi.single i (x i))) = phi x
      rw [← map_sum, Finset.univ_sum_single]
    right_inv := by
      intro phi; funext i; ext x
      simp [Pi.single_apply, apply_ite]
    map_add' := by intro phi psi; rfl
    map_smul' := by intro z phi; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro phi
    funext i
    apply LinearMap.ext
    intro x
    change phi (Math.FiniteSpectrum.copies n r g⁻¹ (Pi.single i x)) =
      phi (Pi.single i (r g⁻¹ x))
    congr 1
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]

theorem of_comp {K : Type*} [Group K] {r : Representation ℂ G V}
    {s : Representation ℂ G W} (j : K →* G)
    (h : NoPairings (r.comp j) (s.comp j)) : NoPairings r s := by
  intro f
  let f' : IntertwiningMap (r.comp j) (Representation.dual (s.comp j)) := {
    toLinearMap := f.toLinearMap
    isIntertwining' k := by
      rw [← dual_comp]
      exact f.isIntertwining' (j k) }
  have hz := h f'
  exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun hz x)

variable (r : Representation ℂ G V) (s : Representation ℂ G W)
  [FiniteDimensional ℂ W]

def crossMap (B : InvariantWeylMass.SymmetricMass (r.prod s.dual)) :
    IntertwiningMap r s :=
  (bidualEquiv s).symm.toIntertwiningMap.comp
    ((dualMap (IntertwiningMap.inr ℂ r s.dual)).comp
      (B.toIntertwiningMap.comp (IntertwiningMap.inl ℂ r s.dual)))

theorem crossMap_evaluation (B : InvariantWeylMass.SymmetricMass (r.prod s.dual))
    (x : V) (phi : Module.Dual ℂ W) :
    phi (crossMap r s B x) = B.form (x,0) (0,phi) := by
  have he := (bidualEquiv s).toLinearEquiv.apply_symm_apply
    (((dualMap (IntertwiningMap.inr ℂ r s.dual)).comp
      (B.toIntertwiningMap.comp (IntertwiningMap.inl ℂ r s.dual))) x)
  exact LinearMap.congr_fun he phi

theorem form_eq_of_same_side_zero
    (B : InvariantWeylMass.SymmetricMass (r.prod s.dual))
    (h1 : ∀ x y : V, B.form (x,0) (y,0) = 0)
    (h2 : ∀ x y : Module.Dual ℂ W, B.form (0,x) (0,y) = 0) :
    B.form = (InvariantWeylMass.ofDirac (crossMap r s B)).form := by
  apply LinearMap.ext
  rintro ⟨x,phi⟩
  apply LinearMap.ext
  rintro ⟨y,psi⟩
  have hx : (x,phi) = (x,0) + (0,phi) := by simp
  have hy : (y,psi) = (y,0) + (0,psi) := by simp
  change B.form (x,phi) (y,psi) =
    psi (crossMap r s B x) + phi (crossMap r s B y)
  rw [hx,hy]
  simp only [map_add, LinearMap.add_apply]
  rw [h1,h2]
  rw [B.symmetric.eq (0,phi) (y,0)]
  simp only [zero_add, add_zero]
  rw [crossMap_evaluation, crossMap_evaluation]
  exact add_comm _ _

theorem normal_form (B : InvariantWeylMass.SymmetricMass (r.prod s.dual))
    (h1 : NoPairings r r) (h2 : NoPairings s.dual s.dual) :
    B.form = (InvariantWeylMass.ofDirac (crossMap r s B)).form := by
  apply form_eq_of_same_side_zero
  · have hz := h1 ((dualMap (IntertwiningMap.inl ℂ r s.dual)).comp
      (B.toIntertwiningMap.comp (IntertwiningMap.inl ℂ r s.dual)))
    intro x y
    exact LinearMap.congr_fun (DFunLike.congr_fun hz x) y
  · have hz := h2 ((dualMap (IntertwiningMap.inr ℂ r s.dual)).comp
      (B.toIntertwiningMap.comp (IntertwiningMap.inr ℂ r s.dual)))
    intro x y
    exact LinearMap.congr_fun (DFunLike.congr_fun hz x) y

end
end Physics.BipartiteNormalForm

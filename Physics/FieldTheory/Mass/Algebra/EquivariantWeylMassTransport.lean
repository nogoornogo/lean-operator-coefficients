import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass

/-! Pullback of an invariant symmetric mass along an actual representation
equivalence, preserving its radical as a representation and nonvanishing. -/

set_option autoImplicit false

namespace Physics.EquivariantWeylMassTransport

noncomputable section

open InvariantWeylMass

variable {G V W : Type*} [Group G]
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
variable (e : Representation.Equiv rho sigma) (B : SymmetricMass sigma)

def pullback : SymmetricMass rho where
  form := B.form.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap
  symmetric := ⟨fun x y => B.symmetric.eq (e x) (e y)⟩
  invariant g x y := by
    change B.form (e (rho g x)) (e (rho g y)) = B.form (e x) (e y)
    have he (z : V) : e (rho g z) = sigma g (e z) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g z
    rw [he, he]
    exact B.invariant g (e x) (e y)

@[simp] theorem pullback_apply (x y : V) : (pullback e B).form x y = B.form (e x) (e y) := rfl

theorem mem_radical_iff (x : V) :
    x ∈ (pullback e B).radical.toSubmodule ↔ e x ∈ B.radical.toSubmodule := by
  simp only [SymmetricMass.mem_radical, pullback_apply]
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective y
    exact h z
  · intro h y
    exact h (e y)

def radicalLinearEquiv : (pullback e B).radical.toSubmodule ≃ₗ[ℂ] B.radical.toSubmodule where
  toFun x := ⟨e x.val, (mem_radical_iff e B x.val).mp x.property⟩
  invFun y := ⟨e.symm y.val, (mem_radical_iff e B _).mpr (by simp)⟩
  left_inv x := by apply Subtype.ext; exact e.toLinearEquiv.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.toLinearEquiv.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact map_add e x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul e r x.val

def radicalEquiv : Representation.Equiv
    (pullback e B).radical.toRepresentation B.radical.toRepresentation where
  toLinearEquiv := radicalLinearEquiv e B
  isIntertwining' g := by
    apply LinearMap.ext; intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x.val

theorem pullback_nonzero (h : B.form ≠ 0) : (pullback e B).form ≠ 0 := by
  intro hz
  apply h
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective x
  obtain ⟨b, rfl⟩ := e.toLinearEquiv.surjective y
  exact LinearMap.congr_fun (LinearMap.congr_fun hz a) b

/-- A certificate keeps large chosen coordinate maps out of radical types,
while retaining equality with the original pullback form. -/
structure PullbackCertificate where
  mass : SymmetricMass rho
  form_eq : mass.form = (pullback e B).form
  radicalEquiv : Representation.Equiv mass.radical.toRepresentation B.radical.toRepresentation
  radicalEquiv_apply : ∀ x, (radicalEquiv x).val = e x.val
  nonzero_of : B.form ≠ 0 → mass.form ≠ 0

theorem PullbackCertificate.apply (C : PullbackCertificate e B) (x y : V) :
    C.mass.form x y = B.form (e x) (e y) := by
  rw [C.form_eq, pullback_apply]

/-- Radical membership follows from the certified form equality. -/
theorem PullbackCertificate.mem_radical_iff (C : PullbackCertificate e B) (x : V) :
    x ∈ C.mass.radical.toSubmodule ↔ e x ∈ B.radical.toSubmodule := by
  simp only [SymmetricMass.mem_radical]
  constructor
  · intro hx y
    obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective y
    exact (PullbackCertificate.apply (e := e) (B := B) C x z).symm.trans (hx z)
  · intro hx y
    exact (PullbackCertificate.apply (e := e) (B := B) C x y).trans (hx _)

theorem PullbackCertificate.symm_apply (C : PullbackCertificate e B) (x y : W) :
    C.mass.form (e.symm x) (e.symm y) = B.form x y := by
  rw [C.apply]
  simp

def certificate : PullbackCertificate e B :=
  Classical.choice ⟨{
    mass := pullback e B
    form_eq := rfl
    radicalEquiv := radicalEquiv e B
    radicalEquiv_apply := fun _ => rfl
    nonzero_of := pullback_nonzero e B }⟩

theorem certificate_apply (x y : V) :
    (certificate e B).mass.form x y = B.form (e x) (e y) := by
  rw [(certificate e B).form_eq, pullback_apply]

theorem certificate_symm_apply (x y : W) :
    (certificate e B).mass.form (e.symm x) (e.symm y) = B.form x y := by
  rw [certificate_apply]
  simp

/-- Restriction to a specified, provably equal action leaves the form
definitionally unchanged. This avoids transporting the underlying space. -/
def restrictTo {K : Type*} [Group K] (B : SymmetricMass rho) (f : K →* G)
    (tau : Representation ℂ K V) (h : rho.comp f = tau) : SymmetricMass tau where
  form := B.form
  symmetric := B.symmetric
  invariant g x y := by
    have hg : rho (f g) = tau g := DFunLike.congr_fun h g
    rw [← hg]
    exact B.invariant (f g) x y

theorem restrictTo_full_invariant {K : Type*} [Group K] (B : SymmetricMass rho)
    (f : K →* G) (tau : Representation ℂ K V) (h : rho.comp f = tau)
    (g : G) (x y : V) :
    (restrictTo B f tau h).form (rho g x) (rho g y) = (restrictTo B f tau h).form x y :=
  B.invariant g x y

def restrictToFullRadical {K : Type*} [Group K] (B : SymmetricMass rho)
    (f : K →* G) (tau : Representation ℂ K V) (h : rho.comp f = tau) :
    Representation ℂ G (restrictTo B f tau h).radical.toSubmodule :=
  B.radical.toRepresentation

def restrictToRadicalEquiv {K : Type*} [Group K] (B : SymmetricMass rho)
    (f : K →* G) (tau : Representation ℂ K V) (h : rho.comp f = tau) :
    Representation.Equiv (restrictTo B f tau h).radical.toRepresentation
      (B.radical.toRepresentation.comp f) :=
  .mk (LinearEquiv.refl ℂ _) (by
    intro g
    apply LinearMap.ext; intro x
    apply Subtype.ext
    exact (LinearMap.congr_fun (DFunLike.congr_fun h g) x.val).symm)

end

end Physics.EquivariantWeylMassTransport

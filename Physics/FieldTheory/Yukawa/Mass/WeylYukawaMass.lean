import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Yukawa.Mass.DiracYukawaMass

/-!
# Symmetric Weyl mass coefficients from Yukawa data

A scalar-linear Yukawa coefficient is symmetric and complex bilinear in its
two fermion arguments. Simultaneous invariance under an arbitrary group
(not necessarily Abelian) produces an invariant symmetric mass after an
invariant vacuum is inserted. No Grassmann algebra or quantum amplitude is
asserted. Restriction to an unbroken subgroup need not fix the vacuum under
the whole ultraviolet group.
-/

set_option autoImplicit false

namespace Physics.WeylYukawaMass

noncomputable section

open InvariantWeylMass
open scoped TensorProduct

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

structure EquivariantYukawa (rhoS : Representation ℂ G S) (rhoV : Representation ℂ G V) where
  toLinearMap : S →ₗ[ℂ] LinearMap.BilinForm ℂ V
  symmetric : ∀ s, (toLinearMap s).IsSymm
  invariant : ∀ g s x y, toLinearMap (rhoS g s) (rhoV g x) (rhoV g y) = toLinearMap s x y

namespace EquivariantYukawa

def zero : EquivariantYukawa rhoS rhoV where
  toLinearMap := 0
  symmetric := by intro s; constructor; intros; rfl
  invariant := by intros; rfl

/-- The actual trilinear coefficient as a linear map on the tensor product. -/
def tensor (Y : EquivariantYukawa rhoS rhoV) : ((S ⊗[ℂ] V) ⊗[ℂ] V) →ₗ[ℂ] ℂ :=
  TensorProduct.lift (TensorProduct.lift Y.toLinearMap)

@[simp] theorem tensor_tmul (Y : EquivariantYukawa rhoS rhoV) (s : S) (x y : V) :
    Y.tensor ((s ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) = Y.toLinearMap s x y := by
  simp [tensor]

/-- Full-group invariant tensor, including for non-Abelian gauge groups. -/
def tensorIntertwiner (Y : EquivariantYukawa rhoS rhoV) :
    Representation.IntertwiningMap ((rhoS.tprod rhoV).tprod rhoV)
      (Representation.trivial ℂ G ℂ) where
  toLinearMap := Y.tensor
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro sx y
    induction sx using TensorProduct.inductionOn with
    | tmul s x =>
        simpa [Representation.tprod_apply, TensorProduct.map_tmul] using Y.invariant g s x y
    | add a b ha hb => simpa [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb

/-- A neutral scalar can carry any already invariant symmetric coefficient. -/
def ofMass (B : SymmetricMass rhoV) :
    EquivariantYukawa (Representation.trivial ℂ G ℂ) rhoV where
  toLinearMap := LinearMap.toSpanSingleton ℂ (LinearMap.BilinForm ℂ V) B.form
  symmetric := by
    intro s
    constructor
    intro x y
    change s * B.form x y = s * B.form y x
    rw [B.symmetric.eq]
  invariant := by
    intro g s x y
    change s * B.form (rhoV g x) (rhoV g y) = s * B.form x y
    rw [B.invariant]

@[simp] theorem ofMass_one (B : SymmetricMass rhoV) : (ofMass B).toLinearMap 1 = B.form := by
  simp [ofMass]

theorem ofMass_nonzero (B : SymmetricMass rhoV) (hB : B.form ≠ 0) :
    (ofMass B).toLinearMap ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h 1
  exact hB (by simpa using he)

end EquivariantYukawa

structure Sector (rhoS : Representation ℂ G S) (rhoV : Representation ℂ G V) where
  bareMass : SymmetricMass rhoV
  yukawa : EquivariantYukawa rhoS rhoV
  vacuum : DiracYukawaMass.InvariantVacuum rhoS

namespace Sector

def mass (D : Sector rhoS rhoV) : SymmetricMass rhoV where
  form := D.bareMass.form + D.yukawa.toLinearMap D.vacuum.value
  symmetric := by
    constructor
    intro x y
    simp only [LinearMap.add_apply, D.bareMass.symmetric.eq,
      (D.yukawa.symmetric D.vacuum.value).eq]
  invariant := by
    intro g x y
    have hy := D.yukawa.invariant g D.vacuum.value x y
    rw [D.vacuum.fixed'] at hy
    simp only [LinearMap.add_apply, D.bareMass.invariant, hy]

@[simp] theorem mass_form_apply (D : Sector rhoS rhoV) (x y : V) :
    D.mass.form x y = D.bareMass.form x y + D.yukawa.toLinearMap D.vacuum.value x y := rfl

def ofBareMass (B : SymmetricMass rhoV) : Sector rhoS rhoV where
  bareMass := B
  yukawa := EquivariantYukawa.zero
  vacuum := DiracYukawaMass.InvariantVacuum.zero

@[simp] theorem ofBareMass_mass (B : SymmetricMass rhoV) :
    (ofBareMass (rhoS := rhoS) B).mass = B := by
  cases B
  simp [ofBareMass, mass, EquivariantYukawa.zero]

def zero : Sector rhoS rhoV := ofBareMass (SymmetricMass.zero rhoV)

/-- A purely Yukawa realization, with zero bare mass and nonzero singlet VEV.
This is an algebraic compatibility constructor, not a UV scalar-sector claim. -/
def ofMassAsYukawa (B : SymmetricMass rhoV) : Sector (Representation.trivial ℂ G ℂ) rhoV where
  bareMass := SymmetricMass.zero rhoV
  yukawa := EquivariantYukawa.ofMass B
  vacuum := ⟨1, fun _ => rfl⟩

@[simp] theorem ofMassAsYukawa_mass (B : SymmetricMass rhoV) : (ofMassAsYukawa B).mass = B := by
  cases B
  simp [ofMassAsYukawa, mass, SymmetricMass.zero]

end Sector

variable {K : Type*} [Group K]

/-- Evaluate an ambient invariant coupling at a vacuum fixed only by the
specified unbroken subgroup. No commutativity or injectivity is required. -/
def atVacuumOn (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) : SymmetricMass (rhoV.comp f) where
  form := B.form + Y.toLinearMap v
  symmetric := by
    constructor
    intro x y
    simp only [LinearMap.add_apply, B.symmetric.eq, (Y.symmetric v).eq]
  invariant := by
    intro k x y
    have hy := Y.invariant (f k) v x y
    rw [hv] at hy
    change B.form (rhoV (f k) x) (rhoV (f k) y) +
      Y.toLinearMap v (rhoV (f k) x) (rhoV (f k) y) = _
    rw [B.invariant, hy]
    rfl

def atVacuumStabilizer (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV) (v : S) :
    SymmetricMass (rhoV.comp (vacuumStabilizer rhoS v).subtype) :=
  atVacuumOn B Y _ v (fun g => g.property)

end

end Physics.WeylYukawaMass

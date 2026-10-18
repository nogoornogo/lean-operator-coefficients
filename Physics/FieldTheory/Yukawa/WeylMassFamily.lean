import Physics.FieldTheory.Mass.InvariantMassData

/-!
# Scalar-dependent symmetric mass families

Scalar dependence is an arbitrary equivariant function. Fermion dependence
remains complex bilinear. Fixed-vacuum evaluation needs no scalar-linearity,
continuity, unitarity, finite-dimensionality, or commutativity of the group.
Polynomial or physical admissibility of a family is a separate source issue.
-/

set_option autoImplicit false

namespace GUT.WeylMassFamily

open InvariantWeylMass
open DiracYukawaMass (InvariantVacuum)

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

structure EquivariantFamily (rhoS : Representation ℂ G S) (rhoV : Representation ℂ G V) where
  toFun : S → LinearMap.BilinForm ℂ V
  symmetric : ∀ s, (toFun s).IsSymm
  invariant : ∀ g s x y, toFun (rhoS g s) (rhoV g x) (rhoV g y) = toFun s x y

namespace EquivariantFamily

def zero : EquivariantFamily rhoS rhoV where
  toFun := fun _ => 0
  symmetric := fun _ => LinearMap.BilinForm.isSymm_zero
  invariant := by intros; rfl

def const (B : SymmetricMass rhoV) : EquivariantFamily rhoS rhoV where
  toFun := fun _ => B.form
  symmetric := fun _ => B.symmetric
  invariant := fun g _ => B.invariant g

def add (Y Z : EquivariantFamily rhoS rhoV) : EquivariantFamily rhoS rhoV where
  toFun s := Y.toFun s + Z.toFun s
  symmetric s := ⟨fun x y => congrArg₂ (· + ·) ((Y.symmetric s).eq x y)
    ((Z.symmetric s).eq x y)⟩
  invariant g s x y := congrArg₂ (· + ·) (Y.invariant g s x y) (Z.invariant g s x y)

def restrict {K : Type*} [Group K] (Y : EquivariantFamily rhoS rhoV) (f : K →* G) :
    EquivariantFamily (rhoS.comp f) (rhoV.comp f) where
  toFun := Y.toFun
  symmetric := Y.symmetric
  invariant k := Y.invariant (f k)

/-- Evaluate only after proving that the selected group fixes the vacuum. -/
def atVacuum (Y : EquivariantFamily rhoS rhoV) (v : InvariantVacuum rhoS) :
    SymmetricMass rhoV where
  form := Y.toFun v.value
  symmetric := Y.symmetric v.value
  invariant g x y := by
    have h := Y.invariant g v.value x y
    rw [v.fixed'] at h
    exact h

@[simp] theorem atVacuum_form (Y : EquivariantFamily rhoS rhoV) (v : InvariantVacuum rhoS) :
    (Y.atVacuum v).form = Y.toFun v.value := rfl

end EquivariantFamily

structure Sector (rhoS : Representation ℂ G S) (rhoV : Representation ℂ G V) where
  bareMass : SymmetricMass rhoV
  family : EquivariantFamily rhoS rhoV
  vacuum : InvariantVacuum rhoS

namespace Sector

def mass (D : Sector rhoS rhoV) : SymmetricMass rhoV :=
  ((EquivariantFamily.const D.bareMass).add D.family).atVacuum D.vacuum

@[simp] theorem mass_form (D : Sector rhoS rhoV) :
    D.mass.form = D.bareMass.form + D.family.toFun D.vacuum.value := rfl

def ofBareMass (B : SymmetricMass rhoV) : Sector rhoS rhoV where
  bareMass := B
  family := EquivariantFamily.zero
  vacuum := InvariantVacuum.zero

@[simp] theorem ofBareMass_mass (B : SymmetricMass rhoV) :
    (ofBareMass (rhoS := rhoS) B).mass = B := by
  apply SymmetricMass.ext
  exact add_zero B.form

def restrict {K : Type*} [Group K] (D : Sector rhoS rhoV) (f : K →* G) :
    Sector (rhoS.comp f) (rhoV.comp f) where
  bareMass := D.bareMass.restrict f
  family := D.family.restrict f
  vacuum := D.vacuum.restrict f

@[simp] theorem restrict_mass {K : Type*} [Group K]
    (D : Sector rhoS rhoV) (f : K →* G) :
    (D.restrict f).mass = D.mass.restrict f := rfl

end Sector

variable {K : Type*} [Group K]

/-- The homomorphism need not be injective and the ambient group need not
fix the vacuum. -/
def atVacuumOn (B : SymmetricMass rhoV) (Y : EquivariantFamily rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) : SymmetricMass (rhoV.comp f) :=
  (Sector.mk (B.restrict f) (Y.restrict f) ⟨v, hv⟩).mass

@[simp] theorem atVacuumOn_form (B : SymmetricMass rhoV) (Y : EquivariantFamily rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) :
    (atVacuumOn B Y f v hv).form = B.form + Y.toFun v := rfl

def atVacuumStabilizer (B : SymmetricMass rhoV) (Y : EquivariantFamily rhoS rhoV) (v : S) :
    SymmetricMass (rhoV.comp (WeylYukawaMass.vacuumStabilizer rhoS v).subtype) :=
  atVacuumOn B Y _ v (fun g => g.property)

@[simp] theorem atVacuumStabilizer_form (B : SymmetricMass rhoV)
    (Y : EquivariantFamily rhoS rhoV) (v : S) :
    (atVacuumStabilizer B Y v).form = B.form + Y.toFun v := rfl

end GUT.WeylMassFamily

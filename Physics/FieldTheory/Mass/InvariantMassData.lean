import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RepresentationTheory.Basic

/-!
# Algebraic mass and vacuum data

These primitives retain their original declaration names. They need no
ultraviolet group, topology, inner product, or finite-dimensionality.
-/

set_option autoImplicit false

namespace GUT

namespace InvariantWeylMass

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- A two-component mass coefficient invariant under the full unbroken group.
The symmetry here is complex bilinear, not Hermitian. -/
structure SymmetricMass (rho : Representation ℂ G V) where
  form : LinearMap.BilinForm ℂ V
  symmetric : form.IsSymm
  invariant : ∀ g x y, form (rho g x) (rho g y) = form x y

namespace SymmetricMass

variable {rho : Representation ℂ G V}

@[ext] theorem ext {B C : SymmetricMass rho} (h : B.form = C.form) : B = C := by
  cases B
  cases C
  cases h
  rfl

/-- The zero mass coefficient remains admissible; rank is not assumed. -/
def zero (rho : Representation ℂ G V) : SymmetricMass rho where
  form := 0
  symmetric := LinearMap.BilinForm.isSymm_zero
  invariant := by intros; rfl

def restrict {K : Type*} [Group K] (B : SymmetricMass rho) (f : K →* G) :
    SymmetricMass (rho.comp f) where
  form := B.form
  symmetric := B.symmetric
  invariant k := B.invariant (f k)

end SymmetricMass
end InvariantWeylMass

namespace DiracYukawaMass

variable {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable {rhoS : Representation ℂ G S}

/-- A vacuum expectation value fixed by the unbroken group. -/
structure InvariantVacuum (rhoS : Representation ℂ G S) where
  value : S
  fixed' : ∀ g, rhoS g value = value

namespace InvariantVacuum

/-- The zero vacuum is fixed by every linear action. -/
def zero : InvariantVacuum rhoS where
  value := 0
  fixed' := by intro g; simp

def restrict {K : Type*} [Group K] (v : InvariantVacuum rhoS) (f : K →* G) :
    InvariantVacuum (rhoS.comp f) := ⟨v.value, fun k => v.fixed' (f k)⟩

end InvariantVacuum
end DiracYukawaMass

namespace WeylYukawaMass

variable {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]

def vacuumStabilizer (rhoS : Representation ℂ G S) (v : S) : Subgroup G where
  carrier := {g | rhoS g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change rhoS a v = v at ha
    change rhoS b v = v at hb
    change rhoS (a * b) v = v
    simpa only [map_mul, Module.End.mul_apply, hb] using ha
  inv_mem' := by
    intro g hg
    change rhoS g v = v at hg
    change rhoS g⁻¹ v = v
    have he := congrArg (rhoS g⁻¹) hg
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he.symm

end WeylYukawaMass
end GUT

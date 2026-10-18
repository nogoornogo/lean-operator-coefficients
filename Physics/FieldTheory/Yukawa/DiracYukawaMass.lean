import Physics.FieldTheory.Mass.EquivariantMassIndex
import Physics.FieldTheory.Mass.InvariantMassData

open Math

/-!
# Dirac-type masses from Yukawa data and an invariant vacuum

This module is the finite-dimensional source bridge for a Dirac-type
linearized mass sector.  A symmetry-invariant bare mass, an equivariant
Yukawa family, and a fixed vacuum expectation value produce an equivariant
mass map.  Target unitarity then turns that map into the invariant Hermitian
mass-pairing interface used by the checked chiral-index theorem.

This is not a formalization of a general two-component Weyl or Majorana mass
bilinear.  Such a bridge requires a separate treatment of dual
representations and invariant symmetric bilinear forms.
-/

namespace GUT
namespace DiracYukawaMass

open CompactEmbeddingClassification

noncomputable section

universe u s v w

variable {G : Type u} [Group G]
variable {S : Type s} {V : Type v} {W : Type w}
variable [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {rhoS : Representation ℂ G S}
variable {rhoV : Representation ℂ G V}
variable {rhoW : Representation ℂ G W}

/-- A bare Dirac-type mass map invariant under the unbroken group. -/
structure InvariantBareMass
    (rhoV : Representation ℂ G V) (rhoW : Representation ℂ G W) where
  toLinearMap : V →ₗ[ℂ] W
  equivariant' : ∀ g x,
    toLinearMap (rhoV g x) = rhoW g (toLinearMap x)

namespace InvariantBareMass

/-- Package an intertwiner as an invariant bare mass. -/
def ofIntertwiningMap
    (f : Representation.IntertwiningMap rhoV rhoW) :
    InvariantBareMass rhoV rhoW where
  toLinearMap := f
  equivariant' g x :=
    Representation.IntertwiningMap.isIntertwining rhoV rhoW f g x

/-- The representation-theoretic intertwiner underlying an invariant bare
mass. -/
def toIntertwiningMap (M : InvariantBareMass rhoV rhoW) :
    Representation.IntertwiningMap rhoV rhoW where
  toLinearMap := M.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    exact M.equivariant' g

@[simp]
theorem ofIntertwiningMap_toIntertwiningMap
    (f : Representation.IntertwiningMap rhoV rhoW) :
    (ofIntertwiningMap f).toIntertwiningMap = f := by
  ext x
  rfl

/-- The zero bare mass is invariant under every pair of actions. -/
def zero : InvariantBareMass rhoV rhoW where
  toLinearMap := 0
  equivariant' := by
    intro g x
    simp

end InvariantBareMass

/-- A Yukawa family equivariant under simultaneous transformations of its
scalar and fermion arguments.  This is the pointwise form of
`Y(g * s) = rhoW(g) * Y(s) * rhoV(g)^(-1)`. -/
structure EquivariantYukawa
    (rhoS : Representation ℂ G S)
    (rhoV : Representation ℂ G V)
    (rhoW : Representation ℂ G W) where
  toLinearMap : S →ₗ[ℂ] V →ₗ[ℂ] W
  equivariant' : ∀ g s x,
    toLinearMap (rhoS g s) (rhoV g x) =
      rhoW g (toLinearMap s x)

namespace EquivariantYukawa

/-- The zero Yukawa family is equivariant. -/
def zero : EquivariantYukawa rhoS rhoV rhoW where
  toLinearMap := 0
  equivariant' := by
    intro g s x
    simp

end EquivariantYukawa

/-- Finite-dimensional Dirac-type mass data before evaluating the scalar at
its invariant vacuum.  Finite-dimensionality and Hilbert-space assumptions
are imposed only by downstream character-index applications. -/
structure Sector
    (rhoS : Representation ℂ G S)
    (rhoV : Representation ℂ G V)
    (rhoW : Representation ℂ G W) where
  bareMass : InvariantBareMass rhoV rhoW
  yukawa : EquivariantYukawa rhoS rhoV rhoW
  vacuum : InvariantVacuum rhoS

namespace Sector

/-- The identically zero Dirac sector exists for every triple of linear
actions.  This witnesses consistency of the primitive data type; it does not
by itself satisfy any prescribed chiral-index condition. -/
def zero : Sector rhoS rhoV rhoW where
  bareMass := InvariantBareMass.zero
  yukawa := EquivariantYukawa.zero
  vacuum := InvariantVacuum.zero

/-- The post-vacuum mass is the invariant bare mass plus the Yukawa family
evaluated at the vacuum expectation value. -/
def inducedMass (D : Sector rhoS rhoV rhoW) : V →ₗ[ℂ] W :=
  D.bareMass.toLinearMap + D.yukawa.toLinearMap D.vacuum.value

@[simp]
theorem inducedMass_apply (D : Sector rhoS rhoV rhoW) (x : V) :
    D.inducedMass x =
      D.bareMass.toLinearMap x +
        D.yukawa.toLinearMap D.vacuum.value x :=
  rfl

@[simp]
theorem zero_inducedMass :
    (zero : Sector rhoS rhoV rhoW).inducedMass = 0 := by
  ext x
  simp [inducedMass, zero, InvariantBareMass.zero,
    EquivariantYukawa.zero, InvariantVacuum.zero]

/-- Invariance of the primitive mass data implies equivariance of the induced
post-vacuum mass map. -/
theorem inducedMass_equivariant
    (D : Sector rhoS rhoV rhoW) (g : G) (x : V) :
    D.inducedMass (rhoV g x) = rhoW g (D.inducedMass x) := by
  rw [inducedMass_apply, D.bareMass.equivariant']
  have hYukawa := D.yukawa.equivariant' g D.vacuum.value x
  rw [D.vacuum.fixed'] at hYukawa
  rw [hYukawa, inducedMass_apply, map_add]

/-- The induced post-vacuum mass as the intertwiner required by the mass-index
theorem. -/
def massMap (D : Sector rhoS rhoV rhoW) :
    Representation.IntertwiningMap rhoV rhoW where
  toLinearMap := D.inducedMass
  isIntertwining' g := by
    apply LinearMap.ext
    exact D.inducedMass_equivariant g

/-- Target unitarity turns the induced equivariant mass into the invariant
Hermitian pairing used by the physical source layer. -/
def toInvariantMassPairing
    (D : Sector rhoS rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    EquivariantMassIndex.InvariantMassPairing rhoV rhoW :=
  EquivariantMassIndex.InvariantMassPairing.ofIntertwiningMap D.massMap hW

@[simp]
theorem toInvariantMassPairing_toIntertwiningMap
    (D : Sector rhoS rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    (D.toInvariantMassPairing hW).toIntertwiningMap hW = D.massMap :=
  EquivariantMassIndex.InvariantMassPairing.ofIntertwiningMap_toIntertwiningMap
    D.massMap hW

/-- Every already bundled invariant bare mass is a degenerate Yukawa sector
with zero Yukawa coupling and zero vacuum.  This compatibility constructor is
also a consistency witness for the new source interface. -/
def ofBareMass (M : InvariantBareMass rhoV rhoW) :
    Sector rhoS rhoV rhoW where
  bareMass := M
  yukawa := EquivariantYukawa.zero
  vacuum := InvariantVacuum.zero

@[simp]
theorem ofBareMass_inducedMass
    (M : InvariantBareMass rhoV rhoW) :
    (ofBareMass (rhoS := rhoS) M).inducedMass = M.toLinearMap := by
  ext x
  change M.toLinearMap x + 0 = M.toLinearMap x
  exact add_zero _

@[simp]
theorem ofBareMass_massMap
    (M : InvariantBareMass rhoV rhoW) :
    (ofBareMass (rhoS := rhoS) M).massMap = M.toIntertwiningMap := by
  ext x
  exact LinearMap.congr_fun (ofBareMass_inducedMass (rhoS := rhoS) M) x

end Sector

end
end DiracYukawaMass
end GUT

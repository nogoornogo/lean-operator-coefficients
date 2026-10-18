import Physics.FieldTheory.Yukawa.MultilinearWeylMass
import Physics.FieldTheory.Yukawa.WeylYukawaMass

/-! The scalar-linear interface is a mass-preserving special case.
Legacy imports are intentionally confined to this adapter. -/

set_option autoImplicit false

namespace GUT.WeylYukawaMass

open InvariantWeylMass

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

def EquivariantYukawa.toFamily (Y : EquivariantYukawa rhoS rhoV) :
    WeylMassFamily.EquivariantFamily rhoS rhoV where
  toFun := Y.toLinearMap
  symmetric := Y.symmetric
  invariant := Y.invariant

def EquivariantYukawa.toMultilinearCoupling (Y : EquivariantYukawa rhoS rhoV) :
    WeylMassFamily.MultilinearCoupling (fun _ : Fin 1 => rhoS) rhoV :=
  WeylMassFamily.MultilinearCoupling.ofLinear Y.toLinearMap Y.symmetric Y.invariant

@[simp] theorem EquivariantYukawa.toMultilinearCoupling_toFamily [Module ℝ S]
    (Y : EquivariantYukawa rhoS rhoV) :
    Y.toMultilinearCoupling.toFamily (fun _ => LinearMap.id) (fun _ _ _ => rfl) =
      Y.toFamily := rfl

def Sector.toFamilySector (D : Sector rhoS rhoV) : WeylMassFamily.Sector rhoS rhoV where
  bareMass := D.bareMass
  family := D.yukawa.toFamily
  vacuum := D.vacuum

@[simp] theorem Sector.toFamilySector_mass (D : Sector rhoS rhoV) :
    D.toFamilySector.mass = D.mass := rfl

@[simp] theorem Sector.ofBareMass_toFamilySector (B : SymmetricMass rhoV) :
    (ofBareMass (rhoS := rhoS) B).toFamilySector = WeylMassFamily.Sector.ofBareMass B := rfl

@[simp] theorem toFamily_atVacuumOn {K : Type*} [Group K]
    (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) :
    WeylMassFamily.atVacuumOn B Y.toFamily f v hv = atVacuumOn B Y f v hv := rfl

@[simp] theorem toFamily_atVacuumStabilizer
    (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV) (v : S) :
    WeylMassFamily.atVacuumStabilizer B Y.toFamily v = atVacuumStabilizer B Y v := rfl

@[simp] theorem toMultilinearCoupling_atVacuumOn [Module ℝ S] {K : Type*} [Group K]
    (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) :
    WeylMassFamily.atVacuumOn B
      (Y.toMultilinearCoupling.toFamily (fun _ => LinearMap.id) (fun _ _ _ => rfl)) f v hv =
      atVacuumOn B Y f v hv := rfl

end GUT.WeylYukawaMass

import Physics.FieldTheory.Yukawa.Mass.WeylMassFamilyCompatibility

/-! Legacy adapters are checked separately from the GUT-free core audit. -/

set_option autoImplicit false

namespace Physics.AuditWeylMassFamilyCompatibility

open InvariantWeylMass WeylYukawaMass

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

example (D : Sector rhoS rhoV) : D.toFamilySector.mass = D.mass := D.toFamilySector_mass

example (B : SymmetricMass rhoV) :
    (Sector.ofBareMass (rhoS := rhoS) B).toFamilySector.mass = B := by simp

example (B : SymmetricMass rhoV) : (Sector.ofMassAsYukawa B).toFamilySector.mass = B := by simp

example {K : Type*} [Group K] (B : SymmetricMass rhoV) (Y : EquivariantYukawa rhoS rhoV)
    (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v) :
    WeylMassFamily.atVacuumOn B Y.toFamily f v hv = atVacuumOn B Y f v hv :=
  toFamily_atVacuumOn B Y f v hv

#print axioms EquivariantYukawa.toFamily
#print axioms EquivariantYukawa.toMultilinearCoupling_toFamily
#print axioms toMultilinearCoupling_atVacuumOn
#print axioms Sector.toFamilySector_mass
#print axioms Sector.ofBareMass_toFamilySector
#print axioms toFamily_atVacuumOn
#print axioms toFamily_atVacuumStabilizer

end Physics.AuditWeylMassFamilyCompatibility

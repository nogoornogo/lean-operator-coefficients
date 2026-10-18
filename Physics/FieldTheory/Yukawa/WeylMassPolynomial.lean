import Physics.FieldTheory.Yukawa.MultilinearWeylMassContinuity

/-!
# Neutral scalar power sources

An invariant symmetric mass can be realized by a genuine finite multilinear
coefficient with neutral scalar slots. Diagonal evaluation gives s^n B, so
vacuum one recovers B. This is an existence/compatibility construction,
not a prediction of B or of the vacuum.
-/

set_option autoImplicit false

namespace GUT.WeylMassFamily

noncomputable section

open InvariantWeylMass

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
variable {rhoV : Representation ℂ G V}

/-- A witness that the coefficient is not additive in the original scalar field. -/
def EquivariantFamily.Nonadditive {S : Type*} [AddCommGroup S] [Module ℂ S]
    {rhoS : Representation ℂ G S} (Y : EquivariantFamily rhoS rhoV) : Prop :=
  ∃ s t, Y.toFun (s + t) ≠ Y.toFun s + Y.toFun t

def MultilinearCoupling.powerOfMass (B : SymmetricMass rhoV) (n : ℕ) :
    MultilinearCoupling (fun _ : Fin n => Representation.trivial ℂ G ℂ) rhoV where
  coefficient := MultilinearMap.mkPiRing ℂ (Fin n) B.form
  symmetric m := ⟨fun x y => by
    change (∏ i, m i) * B.form x y = (∏ i, m i) * B.form y x
    rw [B.symmetric.eq x y]⟩
  invariant g m x y := by
    change (∏ i, m i) * B.form (rhoV g x) (rhoV g y) = (∏ i, m i) * B.form x y
    rw [B.invariant]

def EquivariantFamily.powerOfMass (B : SymmetricMass rhoV) (n : ℕ) :
    EquivariantFamily (Representation.trivial ℂ G ℂ) rhoV :=
  (MultilinearCoupling.powerOfMass B n).toFamily
    (fun _ => LinearMap.id) (fun _ _ _ => rfl)

@[simp] theorem EquivariantFamily.powerOfMass_apply (B : SymmetricMass rhoV) (n : ℕ) (s : ℂ) :
    (powerOfMass B n).toFun s = s ^ n • B.form := by
  change MultilinearMap.mkPiRing ℂ (Fin n) B.form (fun _ => s) = _
  simp

theorem EquivariantFamily.powerOfMass_zero (B : SymmetricMass rhoV) (n : ℕ) :
    (powerOfMass B (n + 1)).toFun 0 = 0 := by simp

theorem EquivariantFamily.powerOfMass_nonzero (B : SymmetricMass rhoV) (n : ℕ)
    (hB : B.form ≠ 0) : (powerOfMass B n).toFun 1 ≠ 0 := by simpa using hB

/-- Nonzero B gives a genuinely nonlinear coefficient on the original scalar line. -/
theorem EquivariantFamily.quadratic_not_additive (B : SymmetricMass rhoV) (hB : B.form ≠ 0) :
    (powerOfMass B 2).toFun (1 + 1) ≠
      (powerOfMass B 2).toFun 1 + (powerOfMass B 2).toFun 1 := by
  intro h
  have he : (1 + 1 : ℂ) ^ 2 • B.form = (1 + 1 : ℂ) • B.form := by
    simpa only [powerOfMass_apply, one_pow, add_smul, one_smul] using h
  have heq := (smul_left_inj hB).mp he
  norm_num at heq

theorem EquivariantFamily.quadratic_nonadditive (B : SymmetricMass rhoV) (hB : B.form ≠ 0) :
    (powerOfMass B 2).Nonadditive :=
  ⟨1, 1, quadratic_not_additive B hB⟩

def Sector.ofMassAsPower (B : SymmetricMass rhoV) (n : ℕ) :
    Sector (Representation.trivial ℂ G ℂ) rhoV where
  bareMass := SymmetricMass.zero _
  family := EquivariantFamily.powerOfMass B n
  vacuum := ⟨1, fun _ => rfl⟩

@[simp] theorem Sector.ofMassAsPower_mass (B : SymmetricMass rhoV) (n : ℕ) :
    (ofMassAsPower B n).mass = B := by
  apply SymmetricMass.ext
  rw [mass_form]
  simp [ofMassAsPower, SymmetricMass.zero]

/-- The same nonzero coupling may have zero induced mass at a different VEV. -/
theorem Sector.ofMassAsPower_zeroVacuum (B : SymmetricMass rhoV) (n : ℕ) :
    ({ ofMassAsPower B (n + 1) with vacuum := DiracYukawaMass.InvariantVacuum.zero }).mass =
      SymmetricMass.zero rhoV := by
  apply SymmetricMass.ext
  rw [mass_form]
  simp [ofMassAsPower, DiracYukawaMass.InvariantVacuum.zero, SymmetricMass.zero]

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {rhoE : Representation ℂ G E}

theorem EquivariantFamily.continuous_powerOfMass (B : SymmetricMass rhoE) (n : ℕ) :
    Continuous (fun p : ℂ × E × E => (powerOfMass B n).toFun p.1 p.2.1 p.2.2) :=
  (MultilinearCoupling.powerOfMass B n).continuous_toFamily _ _

end Continuity
end
end GUT.WeylMassFamily

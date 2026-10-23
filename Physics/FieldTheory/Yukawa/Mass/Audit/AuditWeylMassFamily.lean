import Math.Audit.ImportOrigin
import Physics.FieldTheory.Yukawa.Mass.WeylMassFamily
import Mathlib.Tactic

/-! Persistent algebraic controls, with no actual SU(5)/SU(6) dependencies. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Generic mass-family audit imports a GUT-specific module: {mod}"

namespace Physics.AuditWeylMassFamily

noncomputable section

open WeylMassFamily InvariantWeylMass

def weight (n : ℤ) : Representation ℂ ℂˣ ℂ where
  toFun g := (g : ℂ) ^ n • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by apply LinearMap.ext; intro x; simp [mul_zpow, mul_assoc, mul_left_comm]

@[simp] theorem weight_apply (n : ℤ) (g : ℂˣ) (x : ℂ) :
    weight n g x = (g : ℂ) ^ n * x := rfl

/-- Scalar weight -2 compensates two fermion slots of weight 1. -/
def chargedFamily : EquivariantFamily (weight (-2)) (weight 1) where
  toFun s := s • LinearMap.mul ℂ ℂ
  symmetric s := ⟨fun x y => by simp [mul_comm]⟩
  invariant g s x y := by
    change ((g : ℂ) ^ (-2 : ℤ) * s) *
      (((g : ℂ) ^ (1 : ℤ) * x) * ((g : ℂ) ^ (1 : ℤ) * y)) = s * (x * y)
    simp only [zpow_one, zpow_neg, zpow_two]
    field_simp

def two : ℂˣ := Units.mk0 2 (by norm_num)

theorem one_not_fixed : weight (-2) two 1 ≠ 1 := by
  norm_num [weight_apply, two, zpow_neg]

/-- Dropping the fixed-vacuum premise genuinely loses mass invariance. -/
theorem evaluated_mass_not_invariant :
    ¬ ∀ g x y, chargedFamily.toFun 1 (weight 1 g x) (weight 1 g y) =
      chargedFamily.toFun 1 x y := by
  intro h
  have he := h two 1 1
  norm_num [chargedFamily, two] at he

def unbroken : Subgroup ℂˣ := WeylYukawaMass.vacuumStabilizer (weight (-2)) 1

theorem minus_one_mem : (-1 : ℂˣ) ∈ unbroken := by
  change weight (-2) (-1) 1 = 1
  norm_num

theorem two_not_mem : two ∉ unbroken := one_not_fixed

def subgroupMass : SymmetricMass ((weight 1).comp unbroken.subtype) :=
  atVacuumStabilizer (SymmetricMass.zero _) chargedFamily 1

theorem subgroupMass_nonzero : subgroupMass.form ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h 1) 1
  norm_num [subgroupMass, atVacuumStabilizer_form, chargedFamily, SymmetricMass.zero] at he

theorem subgroupMass_invariant (g : unbroken) (x y : ℂ) :
    subgroupMass.form (weight 1 g.val x) (weight 1 g.val y) = subgroupMass.form x y :=
  subgroupMass.invariant g x y

/-- The subgroup is nontrivial: its surviving element negates the fermion. -/
theorem surviving_action : weight 1 (-1) (1 : ℂ) = -1 := by simp

def zeroVacuumSector : Sector (weight (-2)) (weight 1) where
  bareMass := SymmetricMass.zero _
  family := chargedFamily
  vacuum := DiracYukawaMass.InvariantVacuum.zero

theorem chargedFamily_nonzero : chargedFamily.toFun 1 ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h 1) 1
  norm_num [chargedFamily] at he

theorem zeroVacuum_mass : zeroVacuumSector.mass.form = 0 := by
  simp [zeroVacuumSector, Sector.mass_form, SymmetricMass.zero,
    DiracYukawaMass.InvariantVacuum.zero, chargedFamily]

/-- No scalar-linearity is hidden in the general family interface. -/
def quadraticFamily : EquivariantFamily (Representation.trivial ℂ ℂˣ ℂ)
    (Representation.trivial ℂ ℂˣ ℂ) where
  toFun s := s ^ 2 • LinearMap.mul ℂ ℂ
  symmetric s := ⟨fun x y => by simp [mul_comm]⟩
  invariant := by intros; rfl

theorem quadraticFamily_not_additive :
    quadraticFamily.toFun (1 + 1) ≠ quadraticFamily.toFun 1 + quadraticFamily.toFun 1 := by
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h 1) 1
  norm_num [quadraticFamily] at he

def quadraticSector : Sector (Representation.trivial ℂ ℂˣ ℂ)
    (Representation.trivial ℂ ℂˣ ℂ) where
  bareMass := SymmetricMass.zero _
  family := quadraticFamily
  vacuum := ⟨1, fun _ => rfl⟩

theorem quadratic_mass_nonzero : quadraticSector.mass.form ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h 1) 1
  norm_num [quadraticSector, Sector.mass_form, quadraticFamily, SymmetricMass.zero] at he

def constantSector : Sector (weight (-2)) (Representation.trivial ℂ ℂˣ ℂ) where
  bareMass := SymmetricMass.zero _
  family := EquivariantFamily.const quadraticSector.mass
  vacuum := DiracYukawaMass.InvariantVacuum.zero

/-- An arbitrary family need not vanish at zero scalar, unlike a linear one. -/
theorem constant_zeroVacuum_nonzero : constantSector.mass.form ≠ 0 := by
  simpa [constantSector, Sector.mass_form, SymmetricMass.zero, EquivariantFamily.const]
    using quadratic_mass_nonzero

#print axioms EquivariantFamily.atVacuum
#print axioms Sector.mass
#print axioms Sector.ofBareMass_mass
#print axioms Sector.restrict_mass
#print axioms atVacuumOn
#print axioms atVacuumStabilizer
#print axioms one_not_fixed
#print axioms evaluated_mass_not_invariant
#print axioms minus_one_mem
#print axioms subgroupMass_nonzero
#print axioms subgroupMass_invariant
#print axioms surviving_action
#print axioms chargedFamily_nonzero
#print axioms zeroVacuum_mass
#print axioms quadraticFamily_not_additive
#print axioms quadratic_mass_nonzero
#print axioms constant_zeroVacuum_nonzero

end
end Physics.AuditWeylMassFamily

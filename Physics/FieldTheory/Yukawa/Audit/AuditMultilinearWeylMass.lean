import Math.Audit.ImportOrigin
import Physics.FieldTheory.Yukawa.MultilinearWeylMassContinuity
import Physics.FieldTheory.Yukawa.WeylMassPolynomial
import Mathlib.Tactic

/-! Persistent MASS-2 controls on actual finite coefficients. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "The multilinear mass core must not import SU(5) or SU(6): {mod}"

set_option autoImplicit false
noncomputable section

namespace GUT.AuditMultilinearWeylMass

open WeylMassFamily InvariantWeylMass

def trivial : Representation ℂ ℂˣ ℂ := Representation.trivial ℂ ℂˣ ℂ
def trivialPair : Representation ℂ ℂˣ (ℂ × ℂ) := Representation.trivial ℂ ℂˣ (ℂ × ℂ)

def productCoupling (n : ℕ) : MultilinearCoupling (fun _ : Fin n => trivial) trivial where
  coefficient := MultilinearMap.mkPiRing ℂ (Fin n) (LinearMap.mul ℂ ℂ)
  symmetric m := ⟨fun x y => by
    change (∏ i, m i) * (x * y) = (∏ i, m i) * (y * x)
    rw [mul_comm x y]⟩
  invariant _ _ _ _ := rfl

def powerFamily (n : ℕ) : EquivariantFamily trivial trivial :=
  (productCoupling n).toFamily (fun _ => LinearMap.id) (fun _ _ _ => rfl)

theorem powerFamily_apply (n : ℕ) (s x y : ℂ) :
    (powerFamily n).toFun s x y = s ^ n * (x * y) := by
  change ((MultilinearMap.mkPiRing ℂ (Fin n) (LinearMap.mul ℂ ℂ)) (fun _ => s)) x y = _
  simp

theorem powerFamily_zero (n : ℕ) : (powerFamily (n + 1)).toFun 0 = 0 :=
  (productCoupling (n + 1)).toFamily_zero _ _

theorem powerFamily_continuous (n : ℕ) :
    Continuous (fun p : ℂ × ℂ × ℂ => (powerFamily n).toFun p.1 p.2.1 p.2.2) :=
  (productCoupling n).continuous_toFamily _ _

theorem quadratic_not_additive :
    (powerFamily 2).toFun (1 + 1) 1 1 ≠
      (powerFamily 2).toFun 1 1 1 + (powerFamily 2).toFun 1 1 1 := by
  norm_num [powerFamily_apply]

def quadraticMass : SymmetricMass trivial :=
  (powerFamily 2).atVacuum ⟨1, fun _ => rfl⟩

theorem quadraticMass_nonzero : quadraticMass.form ≠ 0 := by
  intro h
  have hh := congrArg (fun B : LinearMap.BilinForm ℂ ℂ => B 1 1) h
  norm_num [quadraticMass, EquivariantFamily.atVacuum, powerFamily_apply] at hh

/-- Different degrees coexist in one finite source. -/
def polynomialFamily : EquivariantFamily trivial trivial :=
  EquivariantFamily.sum (fun n : Fin 3 => powerFamily n)

theorem polynomialFamily_apply (s x y : ℂ) :
    polynomialFamily.toFun s x y = (1 + s + s ^ 2) * (x * y) := by
  simp [polynomialFamily, powerFamily_apply, Fin.sum_univ_succ]
  ring

theorem polynomialFamily_continuous :
    Continuous (fun p : ℂ × ℂ × ℂ => polynomialFamily.toFun p.1 p.2.1 p.2.2) :=
  EquivariantFamily.continuous_sum _ (fun n => powerFamily_continuous n)

theorem degree_zero_survives : polynomialFamily.toFun 0 1 1 = 1 := by
  simp [polynomialFamily_apply]

theorem positive_degree_sum_zero :
    (EquivariantFamily.sum (fun n : Fin 3 => powerFamily (n + 1))).toFun 0 = 0 :=
  EquivariantFamily.sum_zero _ (fun n => powerFamily_zero n)

def mixedSlots (i : Fin 2) : (ℂ × ℂ) →ₗ[ℝ] ℂ :=
  if i = 0 then LinearMap.fst ℝ ℂ ℂ else LinearMap.snd ℝ ℂ ℂ

def mixedFamily : EquivariantFamily trivialPair trivial :=
  (productCoupling 2).toFamily mixedSlots (fun _ _ _ => rfl)

theorem mixedFamily_apply (s : ℂ × ℂ) (x y : ℂ) :
    mixedFamily.toFun s x y = s.1 * s.2 * (x * y) := by
  change ((MultilinearMap.mkPiRing ℂ (Fin 2) (LinearMap.mul ℂ ℂ))
    (fun i => mixedSlots i s)) x y = _
  simp [mixedSlots, Fin.prod_univ_two]

theorem mixedFamily_continuous :
    Continuous (fun p : (ℂ × ℂ) × ℂ × ℂ => mixedFamily.toFun p.1 p.2.1 p.2.2) :=
  (productCoupling 2).continuous_toFamily _ _

theorem mixed_two_fields_required :
    mixedFamily.toFun (1, 0) 1 1 = 0 ∧ mixedFamily.toFun (0, 1) 1 1 = 0 ∧
      mixedFamily.toFun (1, 1) 1 1 = 1 := by
  simp [mixedFamily_apply]

def conjugateSlots (i : Fin 2) : ℂ →ₗ[ℝ] ℂ :=
  if i = 0 then LinearMap.id else MultilinearCoupling.conjugateSlot

def conjugateFamily : EquivariantFamily trivial trivial :=
  (productCoupling 2).toFamily conjugateSlots (fun _ _ _ => rfl)

theorem conjugateFamily_apply (s x y : ℂ) :
    conjugateFamily.toFun s x y = s * star s * (x * y) := by
  change ((MultilinearMap.mkPiRing ℂ (Fin 2) (LinearMap.mul ℂ ℂ))
    (fun i => conjugateSlots i s)) x y = _
  simp [conjugateSlots, Fin.prod_univ_two]

theorem conjugateFamily_continuous :
    Continuous (fun p : ℂ × ℂ × ℂ => conjugateFamily.toFun p.1 p.2.1 p.2.2) :=
  (productCoupling 2).continuous_toFamily _ _

theorem conjugateSlot_not_complex_linear :
    MultilinearCoupling.conjugateSlot Complex.I ≠
      Complex.I * MultilinearCoupling.conjugateSlot 1 := by
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

/-- The degree-two scaling law of a holomorphic quadratic fails here. -/
theorem conjugateFamily_not_complex_quadratic :
    conjugateFamily.toFun Complex.I 1 1 ≠ Complex.I ^ 2 * conjugateFamily.toFun 1 1 1 := by
  norm_num [conjugateFamily_apply]

theorem conjugateFamily_zero : conjugateFamily.toFun 0 = 0 :=
  (productCoupling 2).toFamily_zero _ _

def weight (n : ℤ) : Representation ℂ ℂˣ ℂ where
  toFun g := (g : ℂ) ^ n • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by
    apply LinearMap.ext; intro x; simp [mul_zpow, mul_assoc, mul_left_comm]

def chargedCoefficient : MultilinearCoupling (fun _ : Fin 2 => weight (-1)) (weight 1) where
  coefficient := (productCoupling 2).coefficient
  symmetric := (productCoupling 2).symmetric
  invariant g m x y := by
    change (∏ i : Fin 2, (g : ℂ) ^ (-1 : ℤ) * m i) *
      (((g : ℂ) ^ (1 : ℤ) * x) * ((g : ℂ) ^ (1 : ℤ) * y)) =
      (∏ i : Fin 2, m i) * (x * y)
    simp only [Fin.prod_univ_two, zpow_neg_one, zpow_one]
    field_simp

def chargedFamily : EquivariantFamily (weight (-1)) (weight 1) :=
  chargedCoefficient.toFamily (fun _ => LinearMap.id) (fun _ _ _ => rfl)

def chargedMass := atVacuumStabilizer (SymmetricMass.zero (weight 1)) chargedFamily 1

theorem chargedMass_nonzero : chargedMass.form ≠ 0 := by
  intro h
  have hh := congrArg (fun B : LinearMap.BilinForm ℂ ℂ => B 1 1) h
  change (0 : ℂ) + (∏ _ : Fin 2, (1 : ℂ)) * (1 * 1) = 0 at hh
  norm_num at hh

theorem charged_zero_mass : chargedFamily.toFun 0 = 0 :=
  chargedCoefficient.toFamily_zero _ _

theorem chargedMass_invariant (g : WeylYukawaMass.vacuumStabilizer (weight (-1)) 1)
    (x y : ℂ) : chargedMass.form (weight 1 g.val x) (weight 1 g.val y) =
      chargedMass.form x y := chargedMass.invariant g x y

#print axioms MultilinearCoupling.toFamily
#print axioms MultilinearCoupling.toFamily_zero
#print axioms MultilinearCoupling.toFamily_realDiagonal
#print axioms MultilinearCoupling.toFamily_real_homogeneous
#print axioms MultilinearCoupling.constant_toFamily
#print axioms MultilinearCoupling.ofLinear_toFamily
#print axioms EquivariantFamily.sum
#print axioms EquivariantFamily.sum_zero
#print axioms multilinear_basis_expansion
#print axioms continuous_multilinear_scalar
#print axioms MultilinearCoupling.continuous_toFamily
#print axioms quadratic_not_additive
#print axioms quadraticMass_nonzero
#print axioms polynomialFamily_apply
#print axioms polynomialFamily_continuous
#print axioms degree_zero_survives
#print axioms positive_degree_sum_zero
#print axioms mixed_two_fields_required
#print axioms mixedFamily_continuous
#print axioms conjugateSlot_not_complex_linear
#print axioms conjugateFamily_not_complex_quadratic
#print axioms conjugateFamily_continuous
#print axioms conjugateFamily_zero
#print axioms chargedCoefficient
#print axioms chargedMass_nonzero
#print axioms charged_zero_mass
#print axioms chargedMass_invariant
#print axioms MultilinearCoupling.powerOfMass
#print axioms EquivariantFamily.quadratic_not_additive
#print axioms EquivariantFamily.continuous_powerOfMass
#print axioms Sector.ofMassAsPower_mass
#print axioms Sector.ofMassAsPower_zeroVacuum

end GUT.AuditMultilinearWeylMass

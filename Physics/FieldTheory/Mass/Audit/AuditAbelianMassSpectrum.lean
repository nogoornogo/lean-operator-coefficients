import Math.Audit.ImportOrigin
import Physics.FieldTheory.Mass.AbelianMassSpectrum
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

open Math

/-! Persistent CHAIN-1 controls: actual characters, zero/nonzero masses,
self-dual finite-group characters, and failure of negative-oriented support. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Shared Abelian mass spectrum imports a gauge-specific module: {mod}"

namespace GUT.AuditAbelianMassSpectrum

noncomputable section

open InvariantWeylMass AbelianActualSpectrum UnitaryCharacterSpectrum AbelianMassSpectrum

def scalar {H : Type*} [CommGroup H] (chi : H →* Circle) : Representation ℂ H ℂ where
  toFun h := (chi h : ℂ) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by apply LinearMap.ext; intro x; simp [mul_smul, mul_left_comm]

theorem scalar_unitary {H : Type*} [CommGroup H] (chi : H →* Circle) :
    UnitaryMultiplicity.IsUnitaryRepresentation (scalar chi) := by
  intro h x y
  change inner ℂ ((chi h : ℂ) • x) ((chi h : ℂ) • y) = inner ℂ x y
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, ← Circle.coe_inv_eq_conj,
    ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]

theorem scalar_character {H : Type*} [CommGroup H] (chi : H →* Circle) (h : H) :
    (scalar chi).character h = (chi h : ℂ) := by
  change LinearMap.trace ℂ ℂ ((chi h : ℂ) • LinearMap.id) = _
  simp

theorem scalar_spectrum {H : Type*} [CommGroup H] (chi : H →* Circle) :
    spectrum (scalar chi) (scalar_unitary chi) = Finsupp.single (complexCharacter chi) 1 := by
  apply eval_injective
  intro h
  rw [spectrum_eval, scalar_character]
  rw [eval_single]
  simp only [Int.cast_one, one_mul]
  rfl

def imaginaryUnit : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩

theorem circle_character_not_self_dual :
    Circle.coeHom ≠ dualCharacter Circle.coeHom := by
  intro he
  have hh := congrArg (fun chi : Circle →* ℂ => chi imaginaryUnit) he
  change Complex.I = Complex.I⁻¹ at hh
  have hi : (Complex.I : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  apply hi
  simpa using hh

def circleTarget : Polynomial Circle :=
  Finsupp.single Circle.coeHom 1 - dual (Finsupp.single Circle.coeHom 1)

theorem circle_target_character (h : Circle) :
    (scalar (MonoidHom.id Circle)).character h -
      (scalar (MonoidHom.id Circle)).dual.character h = eval circleTarget h := by
  simp only [circleTarget, eval_sub, eval_dual, eval_single, Representation.char_dual,
    scalar_character, Int.cast_one, one_mul]
  rfl

theorem circle_positive : circleTarget Circle.coeHom = 1 := by
  classical
  simp [circleTarget, dual, circle_character_not_self_dual]

theorem circle_negative : circleTarget (dualCharacter Circle.coeHom) = -1 := by
  classical
  simp [circleTarget, dual, Ne.symm circle_character_not_self_dual]

/-- The support theorem constructs a nonzero actual vector, not `True`. -/
theorem zero_mass_positive_mode :
    ∃ v : ℂ, v ≠ 0 ∧
      (∀ w, (SymmetricMass.zero (scalar (MonoidHom.id Circle))).form v w = 0) ∧
      ∀ h : Circle, scalar (MonoidHom.id Circle) h v = Circle.coeHom h • v := by
  apply exists_zeroMode_of_pos _ (scalar_unitary _) circleTarget circle_target_character
  rw [circle_positive]
  norm_num

theorem negative_coefficient_has_no_mode :
    ¬ ∃ v : ℂ, v ≠ 0 ∧
      ∀ h : Circle, scalar (MonoidHom.id Circle) h v = dualCharacter Circle.coeHom h • v := by
  rintro ⟨v, hv, he⟩
  apply circle_character_not_self_dual
  ext h
  exact mul_right_cancel₀ hv (he h)

abbrev PairSpace := WithLp 2 (ℂ × ℂ)

/-- One chiral line and one neutral line; only the neutral line is massive. -/
def pairAction : Representation ℂ Circle PairSpace where
  toFun h := (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).symm.conj
    (((scalar (MonoidHom.id Circle)).prod (Representation.trivial ℂ Circle ℂ)) h)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def pairEquiv : Representation.Equiv pairAction
    ((scalar (MonoidHom.id Circle)).prod (Representation.trivial ℂ Circle ℂ)) :=
  .mk (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)) (by
    intro h
    apply LinearMap.ext
    intro x
    simp [pairAction])

theorem pair_unitary : UnitaryMultiplicity.IsUnitaryRepresentation pairAction := by
  intro h x y
  change inner ℂ (scalar (MonoidHom.id Circle) h (WithLp.ofLp x).1)
      (scalar (MonoidHom.id Circle) h (WithLp.ofLp y).1) +
      inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).2 =
    inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).1 +
      inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).2
  rw [scalar_unitary]

theorem pair_character (h : Circle) : pairAction.character h = (h : ℂ) + 1 := by
  rw [congrFun (Representation.char_iso pairEquiv) h]
  have he := LinearMap.trace_prodMap'
    (scalar (MonoidHom.id Circle) h) (Representation.trivial ℂ Circle ℂ h)
  change ((scalar (MonoidHom.id Circle)).prod
    (Representation.trivial ℂ Circle ℂ)).character h = _
  calc
    _ = (scalar (MonoidHom.id Circle)).character h +
        (Representation.trivial ℂ Circle ℂ).character h := he
    _ = (h : ℂ) + 1 := by
      rw [scalar_character]
      change (h : ℂ) + LinearMap.trace ℂ ℂ LinearMap.id = _
      simp

def secondCoordinate : PairSpace →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ ℂ ℂ).comp (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).toLinearMap

def pairMass : SymmetricMass pairAction where
  form := (LinearMap.mul ℂ ℂ).compl₁₂ secondCoordinate secondCoordinate
  symmetric := ⟨fun _ _ => mul_comm _ _⟩
  invariant _ _ _ := rfl

theorem pairMass_nonzero : pairMass.form ≠ 0 := by
  intro he
  have hh := congrArg (fun f : LinearMap.BilinForm ℂ PairSpace =>
    f (WithLp.toLp 2 (0, 1)) (WithLp.toLp 2 (0, 1))) he
  change (1 : ℂ) * 1 = 0 at hh
  norm_num at hh

theorem pair_target_character (h : Circle) :
    pairAction.character h - pairAction.dual.character h = eval circleTarget h := by
  rw [Representation.char_dual, pair_character, pair_character]
  simp only [circleTarget, eval_sub, eval_dual, eval_single, Int.cast_one, one_mul]
  change (h : ℂ) + 1 - ((h⁻¹ : Circle) + 1 : ℂ) = (h : ℂ) - (h⁻¹ : Circle)
  ring

theorem nonzero_mass_positive_mode :
    ∃ v : PairSpace, v ≠ 0 ∧ (∀ w, pairMass.form v w = 0) ∧
      ∀ h : Circle, pairAction h v = Circle.coeHom h • v := by
  apply exists_zeroMode_of_pos pairMass pair_unitary circleTarget pair_target_character
  rw [circle_positive]
  norm_num

def signCharacter : ℤˣ →* Circle where
  toFun z := ⟨((z : ℤ) : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rcases Int.units_eq_one_or z with rfl | rfl <;> norm_num⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change (((g * h : ℤˣ) : ℤ) : ℂ) = ((g : ℤ) : ℂ) * ((h : ℤ) : ℂ)
    simp

theorem sign_self_dual :
    dualCharacter (complexCharacter signCharacter) = complexCharacter signCharacter := by
  ext z
  change ((↑z⁻¹ : ℤ) : ℂ) = ((z : ℤ) : ℂ)
  rcases Int.units_eq_one_or z with rfl | rfl <;> norm_num

def signMass : SymmetricMass (scalar signCharacter) where
  form := LinearMap.mul ℂ ℂ
  symmetric := ⟨mul_comm⟩
  invariant z x y := by
    change (((z : ℤ) : ℂ) * x) * (((z : ℤ) : ℂ) * y) = x * y
    rcases Int.units_eq_one_or z with rfl | rfl <;> simp

theorem signMass_nonzero : signMass.form ≠ 0 := by
  intro he
  have hh := congrArg (fun f : LinearMap.BilinForm ℂ ℂ => f 1 1) he
  norm_num [signMass] at hh

theorem signMass_radical_zero : signMass.radical.toSubmodule = ⊥ := by
  ext x
  simp only [SymmetricMass.mem_radical, Submodule.mem_bot]
  constructor
  · intro hx
    simpa [signMass] using hx 1
  · rintro rfl
    simp

theorem sign_dual_index_zero :
    spectrum (scalar signCharacter) (scalar_unitary signCharacter) -
      dual (spectrum (scalar signCharacter) (scalar_unitary signCharacter)) = 0 := by
  classical
  rw [scalar_spectrum]
  simp [dual, sign_self_dual]

#print axioms AbelianActualSpectrum.eval_injective
#print axioms SymmetricMass.quotientSelfDualEquiv
#print axioms SymmetricMass.radical_dual_character_eq
#print axioms UnitaryCharacterSpectrum.spectrum_eval
#print axioms UnitaryCharacterSpectrum.spectrum_nonneg
#print axioms UnitaryCharacterSpectrum.spectrum_apply_complexCharacter
#print axioms UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
#print axioms UnitaryCharacterSpectrum.exists_eigenvector_of_dual_coeff_pos
#print axioms AbelianMassSpectrum.radical_dual_spectrum_eq
#print axioms AbelianMassSpectrum.radical_dual_spectrum_eq_target
#print axioms AbelianMassSpectrum.source_target_of_radical_target
#print axioms AbelianMassSpectrum.coefficient_lower_bound
#print axioms AbelianMassSpectrum.exists_radical_vector_of_pos
#print axioms AbelianMassSpectrum.exists_zeroMode_of_pos
#print axioms scalar_spectrum
#print axioms zero_mass_positive_mode
#print axioms circle_negative
#print axioms negative_coefficient_has_no_mode
#print axioms pairMass_nonzero
#print axioms pair_target_character
#print axioms nonzero_mass_positive_mode
#print axioms sign_self_dual
#print axioms signMass_nonzero
#print axioms signMass_radical_zero
#print axioms sign_dual_index_zero

end

end GUT.AuditAbelianMassSpectrum

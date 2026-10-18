import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylBenchmark
import GUT.SU6.SelectionRules.Models.AbelianActualSpectrum
import Physics.FieldTheory.Mass.InvariantLineMass

open Math

/-!
# A nonzero mass on the original standard Weyl benchmark

The actual fields remain 15 + 2 bar6. Restricted torus characters prove
that a neutral invariant line exists in the canonical, sector-refined field
space. A rank-one symmetric bilinear lifts that line. This does not claim
that all vectorlike modes are lifted or that the full radical is the SM.
-/

set_option autoImplicit false

namespace GUT.ConcreteWeylNonzeroMass

noncomputable section

open StandardSMCharacterTarget StandardWeylMassSource InvariantWeylMass
open ConcreteWeylBenchmark ConcreteSU6PhysicalTarget ConcreteSU6Branching

variable {H : Type*} [CommGroup H]

def weightHom (e : Fin 4 → ℤ) : CombinedGroup H →* ℂ :=
  (PhysicalTorusCharacterBridge.Fourier.exponentMonoidHom e).comp (MonoidHom.fst _ _)

@[simp] theorem weightHom_apply (e : Fin 4 → ℤ) (g : CombinedGroup H) :
    weightHom e g = UnitAddTorus.mFourier e g.1.toAdd := rfl

@[simp] theorem weightHom_zero : weightHom (H := H) 0 = 1 := by
  ext g
  simp [UnitAddTorus.mFourier_zero]

def fieldPolynomial : AbelianActualSpectrum.Polynomial (CombinedGroup H) :=
  (∑ i : Fin 15, Finsupp.single
    (weightHom (fundamentalExponent (pairIndices i).1 +
      fundamentalExponent (pairIndices i).2)) 1) +
    ∑ i : Fin 6, Finsupp.single (weightHom (-fundamentalExponent i)) 2

theorem fieldPolynomial_eval (g : CombinedGroup H) :
    AbelianActualSpectrum.eval (fieldPolynomial (H := H)) g =
      (ordinaryFields (matter H)).rho.character g := by
  classical
  change _ = (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd g.1.toAdd, g.2)
  rw [ConcreteWeylBenchmark.fields_character, PhysicalSMTorusTarget.embedding_ofAdd,
    exteriorTwo_character, antifundamental_character]
  simp_rw [physicalDiagonalPoint_coords]
  unfold fieldPolynomial
  rw [AbelianActualSpectrum.eval_add]
  unfold AbelianActualSpectrum.eval
  rw [← Finsupp.sum_finsetSum_index, ← Finsupp.sum_finsetSum_index]
  · simp [UnitAddTorus.mFourier_add, mFourier_neg_eq_inv, Finset.mul_sum]
  all_goals (intros; simp [add_mul])

theorem fieldPolynomial_trivial_pos : 0 < fieldPolynomial (H := H) 1 := by
  classical
  have hn (chi : CombinedGroup H →* ℂ) (n : ℤ) (h : 0 ≤ n) :
      0 ≤ (Finsupp.single chi n : AbelianActualSpectrum.Polynomial (CombinedGroup H)) 1 := by
    simp only [Finsupp.single_apply]
    split <;> omega
  have he : 0 ≤ (∑ i : Fin 15, Finsupp.single
      (weightHom (H := H) (fundamentalExponent (pairIndices i).1 +
        fundamentalExponent (pairIndices i).2)) (1 : ℤ)) 1 := by
    simp only [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun i _ => hn _ 1 (by omega))
  have ha := Finset.single_le_sum
    (s := Finset.univ) (a := (5 : Fin 6))
    (f := fun i => (Finsupp.single (weightHom (H := H) (-fundamentalExponent i)) (2 : ℤ)) 1)
    (fun i _ => hn _ 2 (by omega)) (Finset.mem_univ _)
  have hlast : weightHom (H := H) (-fundamentalExponent 5) = 1 := by
    change weightHom (H := H) (-0) = 1
    simp
  simp only [hlast, Finsupp.single_eq_same] at ha
  simp only [fieldPolynomial, Finsupp.add_apply, Finsupp.finsetSum_apply] at he ⊢
  omega

theorem fields_have_invariant_vector :
    ∃ v : (ordinaryFields (matter H)).V, v ≠ 0 ∧
      ∀ g, (ordinaryFields (matter H)).rho g v = v := by
  have he : AbelianActualSpectrum.spectrum (ordinaryFields (matter H)) = fieldPolynomial :=
    AbelianActualSpectrum.eval_injective _ _ (fun g =>
      (AbelianActualSpectrum.spectrum_eval _ g).trans (fieldPolynomial_eval g).symm)
  obtain ⟨v, hv, hi⟩ := AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero
    (ordinaryFields (matter H)) 1 (by rw [he]; exact ne_of_gt fieldPolynomial_trivial_pos)
  exact ⟨v, hv, fun g => by simpa using hi g⟩

def invariantVector : (ordinaryFields (matter H)).V := fields_have_invariant_vector.choose

theorem invariantVector_ne_zero : invariantVector (H := H) ≠ 0 :=
  fields_have_invariant_vector.choose_spec.1

theorem invariantVector_fixed (g : CombinedGroup H) :
    (ordinaryFields (matter H)).rho g invariantVector = invariantVector :=
  fields_have_invariant_vector.choose_spec.2 g

def nonzeroMass : SymmetricMass (ordinaryFields (matter H)).rho :=
  InvariantLineMass.mass _ invariantVector invariantVector_fixed

theorem nonzeroMass_form_ne_zero : (nonzeroMass (H := H)).form ≠ 0 :=
  InvariantLineMass.form_ne_zero _ invariantVector invariantVector_ne_zero

/-- Direct refutation of the proposed uniqueness of the zero mass for the
actual invariance group in the model interface. -/
theorem not_all_symmetric_masses_zero :
    ¬ ∀ B : SymmetricMass (ordinaryFields (matter H)).rho, B.form = 0 := by
  intro h
  exact nonzeroMass_form_ne_zero (h nonzeroMass)

theorem nonzeroMass_radical_finrank :
    Module.finrank ℂ (nonzeroMass (H := H)).radical.toSubmodule = 26 := by
  have h := InvariantLineMass.radical_finrank_add_one
    (ordinaryFields (matter H)) invariantVector invariantVector_ne_zero invariantVector_fixed
  rw [fields_finrank] at h
  change Module.finrank ℂ (nonzeroMass (H := H)).radical.toSubmodule + 1 = 27 at h
  omega

def model (H : Type*) [CommGroup H] : StandardWeylModel H where
  matter := matter H
  nonnegative := matter_nonnegative
  mass := nonzeroMass
  generations := 1
  generations_ne := by norm_num
  charges := uniformCharges 0
  singlets := 0
  lightTarget := mass_hasDualSMTarget _

theorem exists_one_generation_nonzero_mass (H : Type*) [CommGroup H] :
    ∃ M : StandardWeylModel H, M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 26 :=
  ⟨model H, rfl, nonzeroMass_form_ne_zero, nonzeroMass_radical_finrank⟩

end

end GUT.ConcreteWeylNonzeroMass

import Physics.FieldTheory.Jets.Weyl.Equations.WeylLinearEquation
import Math.Algebra.Jets.LinearJetAlgebra

/-! Explicit Weyl source equations, wave consequences and retained higher jets. -/
namespace Physics.WeylLinearEquation
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections Math.LinearJetEquation MvPolynomial
open scoped BigOperators

def row (b : Fin 2) : Equations := LinearMap.proj b

theorem field_expansion (v : Spinor) : LorentzJetIBP.spinorBasis.symm v =
    v 0 • Finsupp.single 0 (1 : ℂ) + v 1 • Finsupp.single 1 (1 : ℂ) := by
  apply LorentzJetIBP.spinorBasis.injective
  ext i
  fin_cases i <;> simp [LorentzJetIBP.spinorBasis]

theorem shift_field (i : Fin 4) (v : Spinor) :
    JetLinear.shift i (atOrder 0 (LorentzJetIBP.spinorBasis.symm v)) =
      v 0 • ofSymbols (0 : Fin 2) (X i) + v 1 • ofSymbols (1 : Fin 2) (X i) := by
  rw [field_expansion]
  simp [map_add, X, ScalarJetAlgebra.shift]

theorem seed_row_zero : seed (row 0) =
    ofSymbols (0 : Fin 2) (X (0 : Fin 4) + X 3) +
      ofSymbols (1 : Fin 2) (X (1 : Fin 4) + Complex.I • X 2) := by
  change (∑ i : Fin 4, JetLinear.shift i (atOrder 0 (LorentzJetIBP.spinorBasis.symm
    (fun a => LorentzDirections.pauli (Pi.single i 1) a 0)))) = _
  simp [Fin.sum_univ_succ, shift_field, LorentzDirections.pauli, Pi.single_apply]
  abel

theorem seed_row_one : seed (row 1) =
    ofSymbols (0 : Fin 2) (X (1 : Fin 4) - Complex.I • X 2) +
      ofSymbols (1 : Fin 2) (X (0 : Fin 4) - X 3) := by
  change (∑ i : Fin 4, JetLinear.shift i (atOrder 0 (LorentzJetIBP.spinorBasis.symm
    (fun a => LorentzDirections.pauli (Pi.single i 1) a 1)))) = _
  simp [Fin.sum_univ_succ, shift_field, LorentzDirections.pauli, Pi.single_apply]
  abel

theorem seed_row_ne_zero (b : Fin 2) : seed (row b) ≠ 0 := by
  intro hz
  have hh : (Finsupp.single (3 : Fin 4) 1 : Fin 4 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have he := congrArg (fun a : Fin 4 →₀ ℕ => a 3) h
    norm_num at he
  have he := congrArg (fun v : Jets => v (b, Finsupp.single (0 : Fin 4) 1)) hz
  fin_cases b
  · change (seed (row 0)) (0, Finsupp.single (0 : Fin 4) 1) = 0 at he
    rw [seed_row_zero] at he
    norm_num [X, ofSymbols_monomial, Finsupp.single_apply, hh] at he
  · change (seed (row 1)) (1, Finsupp.single (0 : Fin 4) 1) = 0 at he
    rw [seed_row_one] at he
    norm_num [X, ofSymbols_monomial, Finsupp.single_apply, hh] at he

theorem wave_zero_relation : ofSymbols (0 : Fin 2) LorentzDirections.wave ∈ relations := by
  have h0 := descendant_mem seed (X 0 - X 3) (row 0)
  have h1 := descendant_mem seed (X 1 + Complex.I • X 2) (row 1)
  have he : multiple (X 0 - X 3) (seed (row 0)) - multiple (X 1 + Complex.I • X 2) (seed (row 1)) =
      ofSymbols (0 : Fin 2) LorentzDirections.wave := by
    rw [seed_row_zero, seed_row_one]
    rw [(multiple _).map_add, (multiple _).map_add]
    simp only [multiple_ofSymbols]
    rw [add_sub_add_comm, ← (ofSymbols (0 : Fin 2)).map_sub, ← (ofSymbols (1 : Fin 2)).map_sub]
    have hq : (X 0 - X 3) * (X 0 + X 3) - (X 1 + Complex.I • X 2) * (X 1 - Complex.I • X 2) =
        LorentzDirections.wave := by
      apply MvPolynomial.funext
      intro x
      simp only [LorentzDirections.wave, map_add, map_sub, map_mul, map_pow, eval_X]
      ring_nf
      simp only [smul_eq_C_mul, map_mul, eval_C, eval_X, mul_pow, Complex.I_sq, neg_one_mul]
      ring
    rw [hq, show (X 0 - X 3) * (X 1 + Complex.I • X 2) -
      (X 1 + Complex.I • X 2) * (X 0 - X 3) = (0 : Symbols (Fin 4)) by ring, map_zero, add_zero]
  exact he ▸ Submodule.sub_mem _ h0 h1

theorem wave_one_relation : ofSymbols (1 : Fin 2) LorentzDirections.wave ∈ relations := by
  have h1 := descendant_mem seed (X 0 + X 3) (row 1)
  have h0 := descendant_mem seed (X 1 - Complex.I • X 2) (row 0)
  have he : multiple (X 0 + X 3) (seed (row 1)) - multiple (X 1 - Complex.I • X 2) (seed (row 0)) =
      ofSymbols (1 : Fin 2) LorentzDirections.wave := by
    rw [seed_row_zero, seed_row_one]
    rw [(multiple _).map_add, (multiple _).map_add]
    simp only [multiple_ofSymbols]
    rw [add_sub_add_comm, ← (ofSymbols (0 : Fin 2)).map_sub, ← (ofSymbols (1 : Fin 2)).map_sub]
    rw [show (X 0 + X 3) * (X 1 - Complex.I • X 2) -
      (X 1 - Complex.I • X 2) * (X 0 + X 3) = (0 : Symbols (Fin 4)) by ring, map_zero, zero_add]
    congr 1
    apply MvPolynomial.funext
    intro x
    simp only [LorentzDirections.wave, map_add, map_sub, map_mul, map_pow, eval_X]
    ring_nf
    simp only [smul_eq_C_mul, map_mul, eval_C, eval_X, mul_pow, Complex.I_sq, neg_one_mul]
    ring
  exact he ▸ Submodule.sub_mem _ h1 h0

theorem wave_descendants (b : Fin 2) (p : Symbols (Fin 4)) :
    ofSymbols b (p * LorentzDirections.wave) ∈ relations := by
  have hb : ofSymbols b LorentzDirections.wave ∈ relations := by
    fin_cases b
    · exact wave_zero_relation
    · exact wave_one_relation
  have h := multiple_stable seed p hb
  change multiple p (ofSymbols b LorentzDirections.wave) ∈ relations at h
  rwa [multiple_ofSymbols] at h

def nullPoint : Fin 4 → ℂ := ![1, 0, 0, 1]

def probe : Jets →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ
  (fun j => if j.1 = 1 then eval nullPoint (monomial j.2 1) else 0)

theorem probe_ofSymbols (b : Fin 2) (p : Symbols (Fin 4)) :
    probe (ofSymbols b p) = if b = 1 then eval nullPoint p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ofSymbols_monomial]
    simp only [probe, Finsupp.linearCombination_single]
    rw [show monomial α c = c • monomial α (1 : ℂ) by simp [smul_monomial]]
    by_cases hb : b = 1 <;> simp [hb]
  | add p q hp hq => rw [map_add, map_add, hp, hq]; by_cases hb : b = 1 <;> simp [hb]

theorem probe_multiple (p : Symbols (Fin 4)) (v : Jets) :
    probe (multiple p v) = eval nullPoint p * probe v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]
  | single j c =>
    obtain ⟨b, α⟩ := j
    rw [← ofSymbols_monomial, multiple_ofSymbols, probe_ofSymbols, probe_ofSymbols]
    by_cases hb : b = 1 <;> simp [hb]

theorem probe_shift (i : Fin 4) (v : Spinor) :
    probe (JetLinear.shift i (atOrder 0 (LorentzJetIBP.spinorBasis.symm v))) = nullPoint i * v 1 := by
  rw [shift_field]
  simp [probe_ofSymbols, mul_comm]

theorem probe_seed (f : Equations) : probe (seed f) = 0 := by
  change probe (∑ i : Fin 4, JetLinear.shift i (atOrder 0 (LorentzJetIBP.spinorBasis.symm
    (fun a => f (fun b => LorentzDirections.pauli (Pi.single i 1) a b))))) = 0
  rw [map_sum]
  simp [probe_shift, Fin.sum_univ_succ, nullPoint, LorentzDirections.pauli, Pi.single_apply,
    ← map_add]
  have hz : (![0, 0] : Spinor) = 0 := by ext i; fin_cases i <;> rfl
  rw [hz, map_zero]

theorem probe_annihilates : relations ≤ probe.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, f, rfl⟩
  change probe (multiple p (seed f)) = 0
  rw [probe_multiple, probe_seed, mul_zero]

def onShellProbe : Generator →ₗ[ℂ] ℂ := relations.liftQ probe probe_annihilates

theorem higher_jet_survives (k : ℕ) :
    relations.mkQ (ofSymbols (1 : Fin 2) (X (0 : Fin 4) ^ k)) ≠ 0 := by
  intro hz
  have he := congrArg onShellProbe hz
  change probe (ofSymbols (1 : Fin 2) (X (0 : Fin 4) ^ k)) = 0 at he
  simp [probe_ofSymbols, nullPoint] at he

theorem odd_higher_jet_survives (k : ℕ) :
    ExteriorAlgebra.ι ℂ (relations.mkQ (ofSymbols (1 : Fin 2) (X (0 : Fin 4) ^ k))) ≠ 0 := by
  exact (not_congr (ExteriorAlgebra.ι_eq_zero_iff _)).mpr (higher_jet_survives k)

end
end Physics.WeylLinearEquation

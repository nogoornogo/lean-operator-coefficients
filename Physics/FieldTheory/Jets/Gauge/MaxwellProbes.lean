import Physics.FieldTheory.Jets.Gauge.MaxwellLinearEquation

/-! Two independent transverse null-symbol probes retain arbitrary jet orders.
This is a source-module control before IBP, not a helicity classification. -/
namespace Physics.AbelianFieldStrength
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections LorentzDirections
open scoped TensorProduct BigOperators

def momentum : V := ![1, 0, 0, 1]
def raised : V := ![1, 0, 0, -1]
def charge (v : V) : ℂ := v 0 - v 3
def dot (v w : V) : ℂ := ∑ i : Fin 4, v i * w i
def amplitude (a : V) (ij : Component) : ℂ := raised ij.1 * a ij.2 - a ij.1 * raised ij.2

def probe (a : V) : Jets →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ
  (fun j => amplitude a j.1 * MvPolynomial.eval momentum (MvPolynomial.monomial j.2 1))

theorem probe_ofSymbols (a : V) (ij : Component) (p : Symbols (Fin 4)) :
    probe a (ofSymbols ij p) = amplitude a ij * MvPolynomial.eval momentum p := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ofSymbols_monomial]
    simp [probe, MvPolynomial.eval_monomial, mul_left_comm]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]

theorem probe_multiple (a : V) (p : Symbols (Fin 4)) (v : Jets) :
    probe a (LinearJetEquation.multiple p v) = MvPolynomial.eval momentum p * probe a v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]
  | single j c =>
    obtain ⟨ij, α⟩ := j
    rw [← ofSymbols_monomial, LinearJetEquation.multiple_ofSymbols,
      probe_ofSymbols, probe_ofSymbols, map_mul]
    ring

theorem probe_shift (a : V) (i : Fin 4) (v : Jets) :
    probe a (JetLinear.shift i v) = momentum i * probe a v := by
  rw [← LinearJetEquation.multiple_X, probe_multiple]
  simp

private theorem probe_pair_basis (a : V) (i j : Fin 4) :
    probe a (atOrder 0 (pair (basis i) (basis j))) = amplitude a (i, j) := by
  rw [pair_basis, atOrder_single]
  simp [probe]

theorem probe_zeroPair (a v w : V) : probe a (zeroPair v w) = charge v * dot a w - dot a v * charge w := by
  conv_lhs => rw [← vector_expand v, ← vector_expand w]
  simp only [zeroPair, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, probe_pair_basis, smul_eq_mul]
  simp [amplitude, raised, charge, dot, Fin.sum_univ_succ]
  ring

theorem probe_directional (a v : V) (x : Jets) :
    probe a (directional (metric v) x) = charge v * probe a x := by
  rw [directional_apply, map_sum]
  simp only [map_smul, probe_shift, metric_apply, smul_eq_mul]
  simp [Fin.sum_univ_succ, sign, momentum, charge]
  ring

theorem probe_antisymmetry (a : V) (x : Pair) : probe a (antisymmetry x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul v w =>
    rw [antisymmetry_tmul, map_add, probe_zeroPair, probe_zeroPair]
    ring

theorem probe_maxwell (a : V) (h0 : a 0 = 0) (h3 : a 3 = 0) (v : V) : probe a (maxwell v) = 0 := by
  rw [maxwell_apply, map_sum]
  simp only [probe_shift, probe_zeroPair]
  simp [Fin.sum_univ_succ, momentum, charge, dot, basis, Pi.single_apply, h0, h3]

theorem probe_bianchi (a : V) (x : Triple) : probe a (bianchi x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul v t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy, add_zero]
    | tmul w z =>
      simp only [bianchi_tmul, map_add, probe_directional, probe_zeroPair]
      ring

theorem probe_seed (a : V) (h0 : a 0 = 0) (h3 : a 3 = 0) (x : Equations) : probe a (seed x) = 0 := by
  simp only [seed, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_add, probe_antisymmetry, probe_maxwell a h0 h3, probe_bianchi,
    add_zero]

theorem probe_annihilates (a : V) (h0 : a 0 = 0) (h3 : a 3 = 0) : relations ≤ (probe a).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, x, rfl⟩
  change probe a (LinearJetEquation.multiple p (seed x)) = 0
  rw [probe_multiple, probe_seed a h0 h3, mul_zero]

def transverseDirection (t : Fin 2) : Fin 4 := if t = 0 then 1 else 2

def onShellProbe (t : Fin 2) : Generator →ₗ[ℂ] ℂ :=
  relations.liftQ (probe (basis (transverseDirection t)))
    (probe_annihilates _ (by fin_cases t <;> simp [transverseDirection, basis])
      (by fin_cases t <;> simp [transverseDirection, basis]))

def transverseJet (t : Fin 2) (k : ℕ) : Generator :=
  relations.mkQ (ofSymbols (0, transverseDirection t) (MvPolynomial.X (0 : Fin 4) ^ k))

theorem onShellProbe_transverseJet (t s : Fin 2) (k : ℕ) :
    onShellProbe t (transverseJet s k) = if t = s then 1 else 0 := by
  change probe (basis (transverseDirection t))
    (ofSymbols (0, transverseDirection s) (MvPolynomial.X (0 : Fin 4) ^ k)) = _
  rw [probe_ofSymbols]
  fin_cases t <;> fin_cases s <;> simp [amplitude, raised, basis, transverseDirection, momentum]

theorem transverse_independent (k : ℕ) (a b : ℂ)
    (h : a • transverseJet 0 k + b • transverseJet 1 k = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (onShellProbe 0) h
  have h1 := congrArg (onShellProbe 1) h
  norm_num [map_add, map_smul, onShellProbe_transverseJet] at h0 h1
  exact ⟨h0, h1⟩

theorem higher_jet_survives (t : Fin 2) (k : ℕ) : transverseJet t k ≠ 0 := by
  intro h
  have he := congrArg (onShellProbe t) h
  rw [onShellProbe_transverseJet, ite_eq_left rfl, map_zero] at he
  exact one_ne_zero he

theorem symmetric_higher_jet_survives (t : Fin 2) (k : ℕ) :
    SymmetricAlgebra.ι ℂ Generator (transverseJet t k) ≠ 0 := by
  intro h
  have he := congrArg (SymmetricAlgebra.lift (onShellProbe t)) h
  rw [SymmetricAlgebra.lift_ι_apply, onShellProbe_transverseJet, ite_eq_left rfl, map_zero] at he
  exact one_ne_zero he

end
end Physics.AbelianFieldStrength

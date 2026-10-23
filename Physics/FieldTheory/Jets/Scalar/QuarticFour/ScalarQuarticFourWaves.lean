import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourTensors
import Math.Algebra.Waves.FourWavePolarization

/-! Null, conserving wave functionals annihilate the whole free relation module. -/
namespace Physics.ScalarQuarticFourWaves
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM FourWaveEvaluation FourWavePolarization
open ScalarQuarticFourTensors LorentzFiniteControls
variable (k : Fin 4 → Fin 4 → ℂ)

theorem evaluation_field : evaluation k field = linear (fun _ => 1) := by
  simp [field,MasslessScalarEOM.field,jet,wave,linear]

theorem d_linear (i : Fin 4) (u : Fin 4 → ℂ) :
    d k i (linear u) = linear (fun s => k s i*u s) := by
  simp only [linear,map_sum,Derivation.map_smul,d_X,smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem evaluation_j1 (i : Fin 4) : evaluation k (j1 (E i)) = linear (fun s => k s i) := by
  simp only [j1,E,dirD_single,one_smul]
  rw [derivative,evaluation_field,d_linear]
  simp only [mul_one]

theorem evaluation_j2 (i j : Fin 4) :
    evaluation k (j2 (E i) (E j)) = linear (fun s => k s i*k s j) := by
  simp only [j2,E,dirD_single,one_smul]
  rw [derivative,evaluation_j1,d_linear]

theorem evaluation_j3 (i j l : Fin 4) :
    evaluation k (j3 (E i) (E j) (E l)) = linear (fun s => k s i*k s j*k s l) := by
  simp only [j3,E,dirD_single,one_smul]
  rw [derivative,evaluation_j2,d_linear]
  simp only [mul_assoc]

theorem evaluation_j4 (i j l m : Fin 4) :
    evaluation k (j4 (E i) (E j) (E l) (E m)) = linear (fun s => k s i*k s j*k s l*k s m) := by
  simp only [j4,E,dirD_single,one_smul]
  rw [derivative,evaluation_j3,d_linear]
  simp only [mul_assoc]

theorem evaluation_wave : evaluation k LorentzJetIBP.waveField =
    linear (fun s => (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2) := by
  rw [MasslessScalarEOM.waveField_formula]
  simp [jet,wave,linear,Fin.sum_univ_succ,Finsupp.single_apply,MvPolynomial.smul_eq_C_mul]
  ring

theorem ideal_zero (hn : ∀ s, (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2 = 0)
    {p : OffShell} (hp : p ∈ ideal 0) : evaluation k p = 0 := by
  have hle : ideal 0 ≤ RingHom.ker (evaluation k).toRingHom := by
    apply DifferentialEquation.minimal
    · intro q hq
      change q ∈ {seed 0} at hq
      rw [Set.mem_singleton_iff] at hq
      rw [hq]
      change evaluation k (seed 0) = 0
      simp [seed,evaluation_wave,hn,linear]
    · intro i q hq
      change evaluation k (D i q) = 0
      rw [derivative,show evaluation k q = 0 from hq,map_zero]
  exact hle hp

theorem annihilates
    (hc : ∀ i, ∑ s : Fin 4, k s i = 0)
    (hn : ∀ s, (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2 = 0) :
    (ScalarDerivativeInterface.scalar 0).relations ≤ (onJets k).ker := by
  apply sup_le
  · intro p hp
    change coefficient (evaluation k p) = 0
    rw [ideal_zero k hn hp,map_zero]
  · rintro _ ⟨v,rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simpa only [map_add] using (onJets k).ker.add_mem hu hv
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      exact divergence_zero k hc i p

theorem word_value (r : Fin 5) (a b c d : Fin 4) :
    onJets k (word r (E a) (E b) (E c) (E d)) = moment k r a b c d := by
  change coefficient (evaluation k (word r (E a) (E b) (E c) (E d))) = _
  fin_cases r
  all_goals simp only [word,map_mul,evaluation_field,evaluation_j1,evaluation_j2,
    evaluation_j3,evaluation_j4,moment,pow_succ,pow_zero,one_mul,coefficient_product]

end
end Physics.ScalarQuarticFourWaves

import Math.Algebra.Waves.FourWavePolarization

/-! Four-wave evaluation for any finite family of commuting field species.
The amplitudes are arbitrary; relation annihilation does not require symmetry. -/
namespace Math.ColoredFourWaveEvaluation
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetAlgebra FourWaveEvaluation FourWavePolarization
variable {S : Type*} (k : Fin 4 → Fin 4 → ℂ) (v : S → Fin 4 → ℂ)
abbrev A (S : Type*) := ScalarJetAlgebra.Algebra S (Fin 4)

def jet (j : Index S (Fin 4)) : P := linear (fun s => v j.1 s*wave k s j.2)
def evaluation : A S →ₐ[ℂ] P := aeval (jet k v)

@[simp] theorem evaluation_X (j : Index S (Fin 4)) :
    evaluation k v (X j) = jet k v j := by simp [evaluation]

theorem d_linear (i : Fin 4) (u : Fin 4 → ℂ) :
    d k i (linear u) = linear (fun s => k s i*u s) := by
  simp only [linear,map_sum,Derivation.map_smul,d_X,smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

theorem jet_shift (i : Fin 4) (j : Index S (Fin 4)) :
    jet k v (shift i j) = d k i (jet k v j) := by
  simp only [jet,d_linear,shift]
  apply congrArg linear
  funext s
  rw [add_comm j.2,wave_shift]
  ring

theorem derivative (i : Fin 4) (p : A S) :
    evaluation k v (totalDerivative i p) = d k i (evaluation k v p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [totalDerivative_mul,map_add,map_mul,totalDerivative_X,evaluation_X,jet_shift,hp]
    exact (Derivation.leibniz (d k i) (evaluation k v p) (jet k v j)).symm

theorem field_value (j : S) : evaluation k v (X (j,0)) = linear (v j) := by
  simp [jet,wave]

theorem first_value (i : Fin 4) (j : S) :
    evaluation k v (totalDerivative i (X (j,0))) = linear (fun s => k s i*v j s) := by
  rw [derivative,field_value,d_linear]

def onJets : A S →ₗ[ℂ] ℂ := coefficient.comp (evaluation k v).toLinearMap

theorem divergence_zero (hc : ∀ i, ∑ s : Fin 4, k s i = 0) (i : Fin 4) (p : A S) :
    onJets k v (totalDerivative i p) = 0 := by
  change coefficient (evaluation k v (totalDerivative i p)) = 0
  rw [derivative,coefficient_derivative,hc,zero_mul]

end
end Math.ColoredFourWaveEvaluation

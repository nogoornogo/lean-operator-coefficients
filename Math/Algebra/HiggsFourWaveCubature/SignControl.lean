import Math.Algebra.HiggsFourWaveCubature.FlipChecks0
import Math.Algebra.HiggsFourWaveCubature.FlipChecks1
import Math.Algebra.HiggsFourWaveCubature.FlipChecks2

/-! Sign cancellation reduces finite moments to the paired coordinate cases. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem flip_involutive (r : Fin 3) (i : Fin 4) :
    Function.Involutive (flipIndex r i) := by
  fin_cases r
  · exact flip_involutive0 i
  · exact flip_involutive1 i
  · exact flip_involutive2 i
theorem flip_value (r : Fin 3) (i : Fin 4) (a : Fin (count r)) (s j : Fin 4) :
    raw r (flipIndex r i a) s j = flipPhase r i a*sign i j*raw r a s j := by
  fin_cases r
  · exact flip_value0 i a s j
  · exact flip_value1 i a s j
  · exact flip_value2 i a s j

def flipEquiv (r : Fin 3) (i : Fin 4) : Fin (count r) ≃ Fin (count r) where
  toFun := flipIndex r i
  invFun := flipIndex r i
  left_inv := flip_involutive r i
  right_inv := flip_involutive r i

theorem sign_moment (r : Fin 3) (axis s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l =
      (sign axis i*sign axis j*sign axis k*sign axis l)*sumMoment r s t u v i j k l := by
  have hs := Equiv.sum_comp (flipEquiv r axis)
    (fun a => raw r a s i*raw r a t j*raw r a u k*raw r a v l)
  change (∑ a, raw r (flipIndex r axis a) s i*raw r (flipIndex r axis a) t j*
    raw r (flipIndex r axis a) u k*raw r (flipIndex r axis a) v l) = sumMoment r s t u v i j k l at hs
  calc
    _ = ∑ a, raw r (flipIndex r axis a) s i*raw r (flipIndex r axis a) t j*
        raw r (flipIndex r axis a) u k*raw r (flipIndex r axis a) v l := hs.symm
    _ = _ := by
      unfold sumMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [flip_value]
      calc
        _ = (flipPhase r axis a)^4*(sign axis i*sign axis j*sign axis k*sign axis l)*
            (raw r a s i*raw r a t j*raw r a u k*raw r a v l) := by ring
        _ = _ := by rw [phase_four,one_mul]

def Paired (i j k l : Fin 4) : Prop := (i = j ∧ k = l) ∨ (i = k ∧ j = l) ∨ (i = l ∧ j = k)
instance pairedDecidable (i j k l : Fin 4) : Decidable (Paired i j k l) := by
  unfold Paired
  infer_instance

theorem unpaired_axis : ∀ i j k l : Fin 4, ¬Paired i j k l →
    ∃ a : Fin 4, sign a i*sign a j*sign a k*sign a l = -1 := by decide +kernel

theorem off_pair_zero (r : Fin 3) (s t u v i j k l : Fin 4) (hb : ¬Paired i j k l) :
    sumMoment r s t u v i j k l = 0 := by
  obtain ⟨axis,ha⟩ := unpaired_axis i j k l hb
  have he := sign_moment r axis s t u v i j k l
  rw [ha] at he
  have hz : (2 : GaussianInt)*sumMoment r s t u v i j k l = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (by decide)

theorem unpaired_metrics : ∀ i j k l : Fin 4, ¬Paired i j k l →
    metric i j*metric k l = 0 ∧ metric i k*metric j l = 0 ∧ metric i l*metric j k = 0 := by
  decide +kernel

theorem expected_off_pair_zero (r : Fin 3) (s t u v i j k l : Fin 4) (hb : ¬Paired i j k l) :
    expected r s t u v i j k l = 0 := by
  obtain ⟨h1,h2,h3⟩ := unpaired_metrics i j k l hb
  simp only [expected,mul_assoc,h1,h2,h3,mul_zero,zero_add]

end Math.HiggsFourWaveCubature

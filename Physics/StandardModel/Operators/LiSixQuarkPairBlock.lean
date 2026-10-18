import Physics.StandardModel.Operators.LiSixQuarkExtension

/-! A four-dimensional color/spin product resolved as 1 + 1 + 2.
All reconstruction identities are symbolic in four arbitrary coefficients;
no selected 25-vector matrix or numerical inverse is imported. -/
namespace GUT.LiSixQuarkPairBlock
noncomputable section
open LiSixQuarkExtension
abbrev LocalArray := Fin 5 → Fin 5 → ℂ

/-- Coefficients of AX, AY, BX and BY in the two displayed local blocks. -/
def encode (a b c d : ℂ) : LocalArray := fun p q =>
  a * extraColorFirst p * extraSpinFirst q +
  b * extraColorFirst p * extraSpinSecond q +
  c * extraColorSecond p * extraSpinFirst q +
  d * extraColorSecond p * extraSpinSecond q

/-- Four scalar evaluations determine all four product coefficients. -/
theorem encode_zero_iff (a b c d : ℂ) :
    encode a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    have h20 := congrFun (congrFun h 2) 0
    have h21 := congrFun (congrFun h 2) 1
    norm_num [encode] at h10 h11 h20 h21
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (1 / 3 : ℂ) * h10 - (1 / 6 : ℂ) * h11
    · linear_combination (1 / 6 : ℂ) * h10 + (1 / 6 : ℂ) * h11
    · linear_combination (1 / 3 : ℂ) * h20 - (1 / 6 : ℂ) * h21
    · linear_combination (1 / 6 : ℂ) * h20 + (1 / 6 : ℂ) * h21
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    ext p q
    simp [encode]

/-- Trace, alternating character and a two-dimensional remaining component. -/
def traceCoefficient (a d : ℂ) : ℂ := (a + d) / 2
def alternatingCoefficient (a b c d : ℂ) : ℂ := (2*b - a + d - 2*c) / 6
def standardFirst (a b d : ℂ) : ℂ := b - a + d
def standardSecond (a c d : ℂ) : ℂ := a - d + c

def alternatingSeed : LocalArray := encode 1 2 (-2) (-1)
def standardSeed : LocalArray := encode (-1/3) (1/3) (2/3) (1/3)
def exchangedSeed : LocalArray := encode (1/3) (2/3) (1/3) (-1/3)

/-- Explicit small-block reconstruction, with its scalar coefficients visible. -/
theorem reconstruction (a b c d : ℂ) :
    encode a b c d = traceCoefficient a d • extra +
      alternatingCoefficient a b c d • alternatingSeed +
      standardFirst a b d • standardSeed + standardSecond a c d • exchangedSeed := by
  ext p q
  simp only [encode, extra, traceCoefficient, alternatingCoefficient,
    standardFirst, standardSecond, alternatingSeed, standardSeed, exchangedSeed,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The normalized separating probe reads half the trace in this block. -/
theorem probe_encode (a b c d : ℂ) : extraProbe (encode a b c d) = (a + d) / 2 := by
  simp [extraProbe, encode]
  ring

/-- The probe kernel in this product needs just three symbolic generators. -/
theorem kernel_reconstruction (a b c d : ℂ) (h : extraProbe (encode a b c d) = 0) :
    encode a b c d = alternatingCoefficient a b c d • alternatingSeed +
      standardFirst a b d • standardSeed + standardSecond a c d • exchangedSeed := by
  have ht : traceCoefficient a d = 0 := by
    simpa only [probe_encode, traceCoefficient] using h
  rw [reconstruction, ht, zero_smul, zero_add]

end
end GUT.LiSixQuarkPairBlock

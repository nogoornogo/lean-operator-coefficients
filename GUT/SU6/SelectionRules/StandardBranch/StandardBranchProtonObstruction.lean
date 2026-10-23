import Physics.StandardModel.Operators.Selection.AbelianProtonCharge

open Physics

/-!
# Continuous anomaly cross-check for one Standard Model charge assignment

The group-independent charge algebra is re-exported from AbelianProtonCharge.
The rational identities below do not imply a discrete-symmetry obstruction.
-/

namespace GUT
namespace StandardBranchProtonObstruction
open Physics.StandardBranchProtonObstruction

/-!
## Mixed-anomaly identities for one charge assignment
-/

/-- The `SU(3)^2-K` coefficient, with a common harmless normalization
suppressed. -/
def colorAnomaly (k : Charges ℚ) : ℚ :=
  2 * k.quark + k.up + k.down

/-- The `SU(2)^2-K` coefficient in the normalization compatible with
`colorAnomaly`. -/
def weakAnomaly (k : Charges ℚ) : ℚ :=
  3 * k.quark + k.lepton

/-- The `Y^2-K` coefficient for
`Y=(1/6,-2/3,1/3,-1/2,1)` and the Standard Model multiplicities. -/
def hyperchargeSquareAnomaly (k : Charges ℚ) : ℚ :=
  (1 / 6 : ℚ) * k.quark + (4 / 3 : ℚ) * k.up +
    (1 / 3 : ℚ) * k.down + (1 / 2 : ℚ) * k.lepton + k.electron

/-- The second proton functional is the difference of the weak and color
mixed anomalies. -/
theorem protonSecond_eq_weakAnomaly_sub_colorAnomaly (k : Charges ℚ) :
    protonSecond k = weakAnomaly k - colorAnomaly k := by
  simp [protonSecond, weakAnomaly, colorAnomaly]
  ring

/-- The first proton functional is the stated linear combination of all three
mixed anomalies. -/
theorem protonFirst_eq_anomaly_combination (k : Charges ℚ) :
    protonFirst k =
      (1 / 3 : ℚ) * colorAnomaly k +
        (1 / 2 : ℚ) * weakAnomaly k - hyperchargeSquareAnomaly k := by
  simp [protonFirst, colorAnomaly, weakAnomaly,
    hyperchargeSquareAnomaly]
  ring

/-- An anomaly-free rational charge assignment cannot charge either of the
two gauge-mediated proton-decay contractions. -/
theorem proton_functionals_eq_zero_of_anomaly_free
    (k : Charges ℚ)
    (hColor : colorAnomaly k = 0)
    (hWeak : weakAnomaly k = 0)
    (hYY : hyperchargeSquareAnomaly k = 0) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  constructor
  · rw [protonFirst_eq_anomaly_combination, hColor, hWeak, hYY]
    norm_num
  · rw [protonSecond_eq_weakAnomaly_sub_colorAnomaly, hColor, hWeak]
    norm_num

end StandardBranchProtonObstruction
end GUT

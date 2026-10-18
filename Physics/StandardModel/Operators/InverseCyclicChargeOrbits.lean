import Math.RepresentationTheory.CyclicChargeOrbits
import Physics.StandardModel.Operators.InverseCyclicSMCharges

namespace GUT.InverseCyclicChargeOrbits
set_option autoImplicit false
open Math.CyclicChargeOrbits
variable {k : ℕ} [NeZero k]

omit [NeZero k] in
theorem preserves_bnv (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    3*(scale u x).1+(scale u x).2 ≠ 0 ↔ 3*x.1+x.2 ≠ 0 := by
  simpa using not_congr (linear_test u x 3 1)
omit [NeZero k] in
theorem preserves_b2 (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    6*(scale u x).1 ≠ 0 ↔ 6*x.1 ≠ 0 := by
  simpa using not_congr (linear_test u x 6 0)
omit [NeZero k] in
theorem preserves_llhh (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    2*(scale u x).2 ≠ 0 ↔ 2*x.2 ≠ 0 := by
  simpa using not_congr (linear_test u x 0 2)

def orbitClasses (k : ℕ) [NeZero k] : Finset (Finset (ZMod k × ZMod k)) :=
  (InverseCyclicSMCharges.candidates k).image orbit

theorem orbit_counts :
    ∀ i : Fin 11, (orbitClasses (i.val+2)).card =
      (![2,3,7,5,16,7,18,14,24,11,44] : Fin 11 → ℕ) i := by
  decide +kernel

theorem total_orbits : (∑ i : Fin 11, (orbitClasses (i.val+2)).card) = 151 := by
  rw [show (fun i : Fin 11 => (orbitClasses (i.val+2)).card) =
    (![2,3,7,5,16,7,18,14,24,11,44] : Fin 11 → ℕ) from funext orbit_counts]
  decide +kernel

def effectiveCount (k : ℕ) [NeZero k] (n : ℕ) : ℕ :=
  ((InverseCyclicSMCharges.candidates k).filter (fun x => effectiveOrder x = n)).card

theorem effective_counts : ∀ j : Fin 11,
    (∑ i : Fin 11, effectiveCount (i.val+2) (j.val+2)) =
      (![12,24,30,40,44,42,44,66,68,110,92] : Fin 11 → ℕ) j := by
  decide +kernel
end GUT.InverseCyclicChargeOrbits

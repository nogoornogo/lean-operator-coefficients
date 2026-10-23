import Mathlib.Tactic

/-!
# Abelian charges of Standard Model proton-operator signatures

The charge algebra uses any additive commutative group, including torsion.
It requires no UV gauge group, anomaly constraint, or physical-source model.
Declaration namespaces are retained for compatibility.
-/

namespace Physics.StandardBranchProtonObstruction

/-- Charges of the five chiral Standard Model multiplet types.  The names
`up` and `electron` refer to the left-handed conjugate multiplets appearing in
the chiral spectrum. -/
@[ext]
structure Charges (A : Type*) where
  quark : A
  up : A
  down : A
  lepton : A
  electron : A

section AdditiveCharges

variable {A : Type*} [AddCommGroup A]

/-- Charge of the first gauge-mediated proton-decay contraction, in the sign
convention `2*k_Q-k_u-k_e`. -/
def protonFirst (k : Charges A) : A :=
  k.quark + k.quark - k.up - k.electron

/-- Charge of the second contraction, in the sign convention
`k_Q+k_L-k_u-k_d`. -/
def protonSecond (k : Charges A) : A :=
  k.quark + k.lepton - k.up - k.down

/-- Charge equalities forced when `Q,u^c,e^c` occupy one charged `10` sector
and `d^c,L` occupy one charged anti-fundamental sector. -/
def SU5OrbitCompatible (k : Charges A) : Prop :=
  k.quark = k.up ∧ k.quark = k.electron ∧ k.down = k.lepton

/-- The `SU(5)` orbit charge equalities make both proton-decay functionals
neutral in any ordinary Abelian charge group. -/
theorem proton_functionals_eq_zero_of_su5OrbitCompatible
    (k : Charges A) (h : SU5OrbitCompatible k) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  rcases h with ⟨hQU, hQE, hDL⟩
  have hUE : k.up = k.electron := hQU.symm.trans hQE
  constructor
  · simp [protonFirst, hQU, hUE]
  · simp [protonSecond, hQU, hDL]

end AdditiveCharges


end Physics.StandardBranchProtonObstruction

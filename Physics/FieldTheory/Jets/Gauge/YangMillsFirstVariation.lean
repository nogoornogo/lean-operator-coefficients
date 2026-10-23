import Math.Algebra.Variational.JetFirstVariation
import Math.Algebra.Variational.ConnectionFirstVariation
import Physics.FieldTheory.Jets.Gauge.YangMillsGaugeTrace

/-! Actual evolutionary variation of the normalized matrix Yang–Mills
polynomial Lagrangian, with its boundary and trace-dual component convention. -/
namespace Physics.YangMillsFirstVariation
set_option autoImplicit false
noncomputable section
open Math Math.FormalConnection FormalYangMills
variable (N : Type*) [Fintype N] [DecidableEq N]

def delta (eta : Fin 4 → Mat N) : Derivation ℂ (OffShell N) (OffShell N) :=
  JetFirstVariation.variation (fun j : Components N => eta j.1 j.2.1 j.2.2)

def matrixDelta (eta : Fin 4 → Mat N) : Mat N →ₗ[ℂ] Mat N := (delta N eta).toLinearMap.mapMatrix

omit [Fintype N] [DecidableEq N] in
theorem delta_connection (eta : Fin 4 → Mat N) (i : Fin 4) :
    matrixDelta N eta (connection N i) = eta i := by
  apply Matrix.ext
  intro a b
  change JetFirstVariation.variation
    (fun j : Components N => eta j.1 j.2.1 j.2.2) (MvPolynomial.X ((i, a, b), 0)) = eta i a b
  exact JetFirstVariation.variation_field _ _

omit [Fintype N] [DecidableEq N] in
theorem delta_derivative (eta : Fin 4 → Mat N) (i : Fin 4) (p : OffShell N) :
    delta N eta (D N i p) = D N i (delta N eta p) :=
  JetFirstVariation.variation_derivative _ _ _

def lagrangian : OffShell N := MatrixFirstVariation.lagrangian (D N)
  ScalarJetAlgebra.totalDerivative_commute (connection N) sign

def current (eta : Fin 4 → Mat N) (i : Fin 4) : OffShell N :=
  -∑ j, (sign i * sign j) • Matrix.trace (eta j * F N i j)

def eomPairing (eta : Fin 4 → Mat N) : OffShell N :=
  ∑ j, sign j • Matrix.trace (eta j * equation N j)

theorem ordinary_bridge : MatrixTraceIBP.ordinary (D N) ScalarJetAlgebra.totalDerivative_commute = ordinary N := by
  rfl

theorem curvature_variation (eta : Fin 4 → Mat N) (i j : Fin 4) :
    matrixDelta N eta (F N i j) = nabla N i (eta j) - nabla N j (eta i) := by
  have h := MatrixFirstVariation.variation_curvature (D N)
    ScalarJetAlgebra.totalDerivative_commute (connection N) (delta N eta) (delta_derivative N eta) i j
  change matrixDelta N eta (F N i j) =
    nabla N i (matrixDelta N eta (connection N j)) - nabla N j (matrixDelta N eta (connection N i)) at h
  simpa only [delta_connection] using h

theorem first_variation (eta : Fin 4 → Mat N) :
    delta N eta (lagrangian N) = eomPairing N eta + ∑ i, D N i (current N eta i) := by
  have h := MatrixFirstVariation.first_variation (D N)
    ScalarJetAlgebra.totalDerivative_commute (connection N) (delta N eta) (delta_derivative N eta) sign
  simpa only [MatrixFirstVariation.bulk, MatrixFirstVariation.boundary,
    MatrixFirstVariation.eta, show MatrixFirstVariation.matrixVariation (delta N eta) = matrixDelta N eta from rfl,
    delta_connection, lagrangian, eomPairing, current, MatrixFirstVariation.F,
    MatrixFirstVariation.P, ordinary_bridge, FormalYangMills.F, FormalYangMills.equation,
    FormalConnection.signedEquation, nabla] using h

theorem eomPairing_mem (eta : Fin 4 → Mat N) : eomPairing N eta ∈ ideal N := by
  apply (DifferentialEquation.relations (D N) (equations N)).sum_mem
  intro j hj
  apply (DifferentialEquation.relations (D N) (equations N)).smul_mem
  change (∑ a, (eta j * equation N j) a a) ∈ ideal N
  exact (ideal N).sum_mem (fun a _ => entries_mul_left N _ _ (equation_mem N j) a a)

theorem first_variation_mod_ibp (eta : Fin 4 → Mat N) :
    (DifferentialEquation.ibp (D N)).mkQ (delta N eta (lagrangian N)) =
      (DifferentialEquation.ibp (D N)).mkQ (eomPairing N eta) := by
  rw [first_variation, map_add]
  have h : (DifferentialEquation.ibp (D N)).mkQ (∑ i, D N i (current N eta i)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.sum_mem _ (fun i _ => DifferentialEquation.derivative_mem_ibp (D N) i _)
  rw [h, add_zero]

theorem first_variation_onShell (eta : Fin 4 → Mat N) :
    DifferentialEquation.integrated (D N) (equations N) (delta N eta (lagrangian N)) = 0 := by
  rw [first_variation, map_add, map_sum,
    DifferentialEquation.integrated_equation _ _ (eomPairing_mem N eta)]
  simp only [DifferentialEquation.integrated_derivative, Finset.sum_const_zero, add_zero]

theorem substitution_first (eta : Fin 4 → Mat N) :
    (JetFirstVariation.substitution (fun j : Components N => eta j.1 j.2.1 j.2.2) (lagrangian N)).coeff 1 =
      eomPairing N eta + ∑ i, D N i (current N eta i) := by
  rw [JetFirstVariation.substitution_first]
  exact first_variation N eta

def componentVariation (j : Fin 4) (a b : N) : Fin 4 → Mat N :=
  fun i => if i = j then Matrix.single a b 1 else 0

theorem component_pairing (j : Fin 4) (a b : N) :
    eomPairing N (componentVariation N j a b) = sign j • equation N j b a := by
  simp [eomPairing, componentVariation, apply_ite, Matrix.trace_single_mul]

theorem component_eom_iff (j : Fin 4) (a b : N) :
    eomPairing N (componentVariation N j a b) = 0 ↔ equation N j b a = 0 := by
  rw [component_pairing]
  by_cases h : j = 0 <;> simp [sign, h]

theorem component_first_variation_mod_ibp (j : Fin 4) (a b : N) :
    (DifferentialEquation.ibp (D N)).mkQ
      (delta N (componentVariation N j a b) (lagrangian N)) =
      (DifferentialEquation.ibp (D N)).mkQ (sign j • equation N j b a) := by
  rw [first_variation_mod_ibp, component_pairing]

def eulerSeeds : Set (OffShell N) := Set.range (fun j : Components N =>
  eomPairing N (componentVariation N j.1 j.2.1 j.2.2))

theorem euler_ideal_eq : DifferentialEquation.ideal (D N) (eulerSeeds N) = ideal N := by
  apply le_antisymm
  · apply DifferentialEquation.minimal
    · rintro p ⟨j, rfl⟩
      exact eomPairing_mem N _
    · intro i p hp
      exact DifferentialEquation.stable _ _ i hp
  · apply DifferentialEquation.minimal
    · rintro p ⟨⟨j, a, b⟩, rfl⟩
      have he : eomPairing N (componentVariation N j b a) ∈
          DifferentialEquation.ideal (D N) (eulerSeeds N) :=
        DifferentialEquation.seed_mem _ _ ⟨(j, b, a), rfl⟩
      rw [component_pairing] at he
      have hs := (DifferentialEquation.relations (D N) (eulerSeeds N)).smul_mem (sign j) he
      have hj : sign j * sign j = 1 := by
        by_cases h : j = 0 <;> simp [sign, h]
      change equation N j a b ∈ DifferentialEquation.ideal (D N) (eulerSeeds N)
      change sign j • (sign j • equation N j a b) ∈
        DifferentialEquation.ideal (D N) (eulerSeeds N) at hs
      rw [smul_smul, hj, one_smul] at hs
      exact hs
    · intro i p hp
      exact DifferentialEquation.stable _ _ i hp

end
end Physics.YangMillsFirstVariation

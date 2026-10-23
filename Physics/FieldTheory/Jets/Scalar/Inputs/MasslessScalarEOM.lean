import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP
import Math.RepresentationTheory.Jets.JetEquationComparison
import Math.Algebra.Jets.JetEquationProbe

/-! The four-dimensional free massless scalar equation, with all descendants,
Lorentz covariance, the actual EOM/IBP source and retained higher jets. -/
namespace Physics.MasslessScalarEOM
set_option autoImplicit false
noncomputable section
open Math Math.JetDirections Math.JetLinear MvPolynomial

abbrev equation := LorentzDirections.wave
abbrev Generator := JetEquation.Generator Unit equation
abbrev Algebra := JetEquation.Algebra Unit equation
abbrev projection := JetEquation.projection (S := Unit) equation

theorem trace_zero : (JetEquation.relations Unit equation).mkQ (ofSymbols () equation) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  simpa only [one_mul] using JetEquation.descendant_mem equation () (1 : Symbols (Fin 4))

theorem descendants_zero (p : Symbols (Fin 4)) :
    (JetEquation.relations Unit equation).mkQ (ofSymbols () (p * equation)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (JetEquation.descendant_mem equation () p)

theorem waveField_zero : projection LorentzJetIBP.waveField = 0 := by
  change JetEquation.projection equation (JetLinear.linearForm (ofSymbols () equation)) = 0
  rw [JetEquation.projection_linearForm, trace_zero, map_zero]

def nullPoint : Fin 4 → ℂ := ![1, 1, 0, 0]

theorem nullPoint_wave : eval nullPoint equation = 0 := by
  norm_num [equation, LorentzDirections.wave, nullPoint]

theorem higher_time_jet_survives (k : ℕ) :
    (JetEquation.relations Unit equation).mkQ
      (Finsupp.single ((), Finsupp.single (0 : Fin 4) k) (1 : ℂ)) ≠ 0 := by
  have h := JetEquation.generator_survives equation nullPoint nullPoint_wave (X (0 : Fin 4) ^ k)
    (by simp [nullPoint])
  simpa only [X_pow_eq_monomial, ofSymbols_monomial] using h

theorem higher_time_field_survives (k : ℕ) :
    projection (X ((), Finsupp.single (0 : Fin 4) k)) ≠ 0 := by
  let f : Algebra →ₐ[ℂ] ℂ := SymmetricAlgebra.lift (JetEquation.onShellProbe equation nullPoint nullPoint_wave)
  have hf : f (projection (X ((), Finsupp.single (0 : Fin 4) k))) = 1 := by
    rw [JetEquation.projection_X]
    dsimp only [f]
    rw [SymmetricAlgebra.lift_ι_apply, JetEquation.onShellProbe_mk]
    simp only [JetEquation.symbolProbe, Finsupp.linearCombination_single, one_smul]
    rw [← X_pow_eq_monomial]
    simp [nullPoint]
  intro h
  have he := congrArg f h
  rw [hf, map_zero] at he
  exact one_ne_zero he

def presentationEquiv := JetEquation.presentationEquiv (S := Unit) equation

def action := JetEquation.action equation LorentzJetIBP.scalarField
  LorentzDirections.direction LorentzDirections.wave_invariant

theorem derivative_covariance (g : LorentzDirections.Group) (i : Fin 4) (p : Algebra) :
    action g (JetEquation.derivative equation i p) =
      ∑ j, (LorentzDirections.direction g (Finsupp.single i 1)) j •
        JetEquation.derivative equation j (action g p) :=
  JetEquation.covariance equation LorentzJetIBP.scalarField
    LorentzDirections.direction LorentzDirections.wave_invariant g i p

def coefficientEquiv (n d : ℕ) := JetEquation.coefficientEquiv equation LorentzJetIBP.scalarField
  LorentzDirections.direction LorentzDirections.wave_invariant n d

def combinedSourceEquiv (n d : ℕ) := JetEquation.combinedQuotientEquiv (S := Unit) equation n d

def combinedRepresentationEquiv (n d : ℕ) :=
  JetEquation.combinedRepresentationEquiv equation LorentzJetIBP.scalarField
    LorentzDirections.direction LorentzDirections.wave_invariant n d

def field : ScalarJetAlgebra.Algebra Unit (Fin 4) := X ((), 0)
def firstJet (i : Fin 4) : ScalarJetAlgebra.Algebra Unit (Fin 4) := X ((), Finsupp.single i 1)
def current (i : Fin 4) : ScalarJetAlgebra.Algebra Unit (Fin 4) :=
  if i = 0 then field * firstJet i else -(field * firstJet i)

theorem waveField_formula : LorentzJetIBP.waveField =
    X ((), Finsupp.single (0 : Fin 4) 2) - X ((), Finsupp.single (1 : Fin 4) 2) -
      X ((), Finsupp.single (2 : Fin 4) 2) - X ((), Finsupp.single (3 : Fin 4) 2) := by
  simp [LorentzJetIBP.waveField, JetSymbolEvaluation.linearized, LorentzDirections.wave,
    X_pow_eq_monomial, JetLinear.linearForm]

theorem divergence_current : (∑ i, ScalarJetAlgebra.totalDerivative i (current i)) =
    LorentzJetIBP.kinetic + field * LorentzJetIBP.waveField := by
  rw [LorentzJetIBP.kinetic_formula, waveField_formula]
  simp [Fin.sum_univ_succ, current, field, firstJet,
    ScalarJetAlgebra.shift, ← Finsupp.single_add]
  ring

def fullRelations : Submodule ℂ Algebra :=
  (Finsupp.lsum ℂ (fun i : Fin 4 => JetEquation.derivative (S := Unit) equation i)).range

theorem kinetic_mem_relations : projection LorentzJetIBP.kinetic ∈ fullRelations := by
  let c : Fin 4 →₀ Algebra := Finsupp.equivFunOnFinite.symm (fun i => projection (current i))
  refine ⟨c, ?_⟩
  change c.sum (fun i p => JetEquation.derivative equation i p) = _
  rw [Finsupp.sum_fintype c (fun i p => JetEquation.derivative equation i p) (fun _ => map_zero _)]
  have hc (i : Fin 4) : c i = projection (current i) := by simp [c]
  simp only [hc, ← JetEquation.projection_derivative, ← map_sum]
  rw [divergence_current, map_add, map_mul, waveField_zero, mul_zero, add_zero]

theorem kinetic_zero_mod_ibp : fullRelations.mkQ (projection LorentzJetIBP.kinetic) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr kinetic_mem_relations

end
end Physics.MasslessScalarEOM

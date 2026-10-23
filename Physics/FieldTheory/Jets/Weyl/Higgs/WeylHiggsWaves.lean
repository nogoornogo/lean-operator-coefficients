import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsSelection
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves
import Math.Algebra.Waves.MixedFourWaveEvaluation
import Math.RepresentationTheory.Color.Diagrams.ColoredWavePairing
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Grassmann-valued conserving Higgs waves kill the full C5 relations.
Individual probes need not be invariant under the group. -/
namespace Physics.WeylHiggsWaves
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput
open scoped TensorProduct
abbrev Odd0 := ExteriorAlgebra ℂ (JetLinear.Field Label)

def momenta (p : Fin 4 → ℂ) (s : Fin 4) (i : Fin 4) : ℂ :=
  if s = 0 ∨ s = 1 then p i else -p i

theorem conserving (p : Fin 4 → ℂ) (i : Fin 4) :
    ∑ s : Fin 4, momenta p s i = 0 := by
  simp [momenta,Fin.sum_univ_succ]

theorem null (p : Fin 4 → ℂ)
    (hp : (p 0)^2-(p 1)^2-(p 2)^2-(p 3)^2 = 0) (s : Fin 4) :
    (momenta p s 0)^2-(momenta p s 1)^2-
      (momenta p s 2)^2-(momenta p s 3)^2 = 0 := by
  fin_cases s <;> simpa [momenta] using hp

abbrev evaluation (p : Fin 4 → ℂ) (x y : Fin 2) :=
  MixedFourWaveEvaluation.evaluation (F := Label) (momenta p) (ColoredWavePairing.amplitudes x y)

theorem odd_derivative_zero (p : Fin 4 → ℂ) (x y : Fin 2)
    (i : Fin 4) (c : Bool) (a : Fin 2) : evaluation p x y (D i (psi c a)) = 0 := by
  change evaluation p x y (MixedJetAlgebra.totalDerivative i (MixedJetAlgebra.odd ((c,a),0))) = 0
  rw [MixedJetAlgebra.totalDerivative_odd]
  simp [evaluation,MixedJetAlgebra.odd,Math.ScalarJetAlgebra.shift]

theorem component_zero (p : Fin 4 → ℂ)
    (hp : (p 0)^2-(p 1)^2-(p 2)^2-(p 3)^2 = 0)
    (x y : Fin 2) (j : Label ⊕ Label) :
    evaluation p x y (WeylHiggsRelations.componentSeed j) = 0 := by
  cases j with
  | inl j =>
    rcases j with ⟨c,a⟩
    cases c <;> fin_cases a <;>
      simp [WeylHiggsRelations.componentSeed,seed,left,right,odd_derivative_zero]
  | inr j =>
    change evaluation p x y ((1 : MixedJetAlgebra.Odd Label (Fin 4)) ⊗ₜ[ℂ]
      DerivativeLiteratureHiggs.seed 0 0 j) = 0
    rw [MixedFourWaveEvaluation.evaluation_tmul,map_one]
    change (1 : Odd0) ⊗ₜ[ℂ]
      ColoredFourWaveEvaluation.evaluation (momenta p) (ColoredWavePairing.amplitudes x y)
        (DerivativeLiteratureHiggs.seed 0 0 j) = 0
    rw [HiggsQuarticFourWaves.seed_zero _ _ (null p hp),TensorProduct.tmul_zero]

def augmentation : Odd0 →ₐ[ℂ] ℂ := ExteriorAlgebra.lift ℂ
  ⟨(0 : JetLinear.Field Label →ₗ[ℂ] ℂ), by intro v; simp⟩
def oddProbe (a b : Fin 2) : Odd0 →ₗ[ℂ] ℂ := augmentation.toLinearMap.comp
  ((CliffordAlgebra.contractLeft (Finsupp.lapply (true,b))).comp
    (CliffordAlgebra.contractLeft (Finsupp.lapply (false,a))))

theorem odd_pair (a b : Fin 2) (j k : Label) :
    oddProbe a b (ExteriorAlgebra.ι ℂ (Finsupp.single j 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single k 1)) =
      (if j = (false,a) then 1 else 0) * (if k = (true,b) then 1 else 0) -
      (if j = (true,b) then 1 else 0) * (if k = (false,a) then 1 else 0) := by
  classical
  by_cases hj : j = (false,a) <;> by_cases hk : k = (false,a) <;>
    simp [oddProbe,LinearMap.comp_apply,CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι,augmentation,Finsupp.single_apply,eq_comm,hj,hk]

def probe (p : Fin 4 → ℂ) (a b x y : Fin 2) : A →ₗ[ℂ] ℂ :=
  MixedFourWaveEvaluation.probe (momenta p) (ColoredWavePairing.amplitudes x y) (oddProbe a b)

theorem annihilates (p : Fin 4 → ℂ)
    (hp : (p 0)^2-(p 1)^2-(p 2)^2-(p 3)^2 = 0) (a b x y : Fin 2) :
    input.relations ≤ (probe p a b x y).ker := by
  have h := MixedFourWaveEvaluation.annihilates (momenta p) (ColoredWavePairing.amplitudes x y)
    (oddProbe a b) (conserving p) (Set.range WeylHiggsRelations.componentSeed)
    (by rintro _ ⟨j,rfl⟩; exact component_zero p hp x y j)
  change TwoSidedDifferential.relations D (Set.range WeylHiggsRelations.componentSeed) ⊔ _ ≤ _ at h
  rw [WeylHiggsRelations.component_closure] at h
  exact h

end
end Physics.WeylHiggsWaves

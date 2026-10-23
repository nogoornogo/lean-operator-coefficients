import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenValue
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveSum
import Math.RepresentationTheory.Tensors.MarkedFieldPairing

/-! Whole first-word moments of the full-relation Grassmann wave sum. -/
namespace Physics.WeylHiggsWaveWords
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsWaves
open WeylHiggsEvenValue
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def quartic (x y : Fin 2) (b : Fin 4 → Label) : ℂ :=
  FourWavePolarization.permanent (ColoredWavePairing.amplitudes x y (b 0))
    (ColoredWavePairing.amplitudes x y (b 1)) (ColoredWavePairing.amplitudes x y (b 2))
    (ColoredWavePairing.amplitudes x y (b 3))
def color (b : Fin 4 → Label) : ℂ := ∑ x : Fin 2, ∑ y : Fin 2, quartic x y b

theorem color_pairing (b : Fin 4 → Label) : color b =
    ∑ p : Fin 24, ColoredWavePairing.tensor p (fun t => Finsupp.single (b t) 1) := by
  simp only [color,quartic,ColoredFourWavePolarization.permanent_sum]
  change (∑ x : Fin 2, ∑ y : Fin 2, ∑ p : Fin 24,
    ColoredFourWavePolarization.amplitudeProduct (ColoredWavePairing.amplitudes x y) b p) = _
  calc
    _ = ∑ x : Fin 2, ∑ p : Fin 24, ∑ y : Fin 2,
        ColoredFourWavePolarization.amplitudeProduct (ColoredWavePairing.amplitudes x y) b p := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ p : Fin 24, ∑ x : Fin 2, ∑ y : Fin 2,
        ColoredFourWavePolarization.amplitudeProduct (ColoredWavePairing.amplitudes x y) b p := Finset.sum_comm
    _ = _ := by simp only [ColoredWavePairing.amplitude_sum_pairing]

theorem boson_value (p : Fin 4 → ℂ) (x y : Fin 2) (b : Fin 4 → Label) (i : Fin 4) :
    ColoredFourWaveEvaluation.onJets (momenta p) (ColoredWavePairing.amplitudes x y) (scalarMono b i) =
      (MarkedFieldPairing.sign (b 0)*p i)*quartic x y b := by
  change FourWaveEvaluation.coefficient (WeylHiggsWaveValues.ev p x y (scalarMono b i)) = _
  simp only [scalarMono,map_mul,WeylHiggsWaveValues.first]
  simp only [DerivativeLiteratureHiggs.h,ColoredFourWaveEvaluation.field_value,
    smul_mul_assoc,map_smul,FourWavePolarization.coefficient_product,Prod.eta]
  cases hc : (b 0).1 <;> simp [MarkedFieldPairing.sign,hc,quartic]

def delta (a e : Fin 2) (j k : Label) : ℂ :=
  (if j = (false,a) then 1 else 0)*(if k = (true,e) then 1 else 0)-
    (if j = (true,e) then 1 else 0)*(if k = (false,a) then 1 else 0)

theorem delta_left (aa ee a e : Fin 2) :
    delta aa ee (false,a) (true,e) = if aa = a then if ee = e then 1 else 0 else 0 := by
  by_cases ha : aa = a <;> by_cases he : ee = e <;> simp [delta,ha,he,eq_comm]

theorem delta_same (aa ee : Fin 2) (c : Bool) (a e : Fin 2) : delta aa ee (c,a) (c,e) = 0 := by
  cases c <;> simp [delta]

theorem probe_scalar (p : Fin 4 → ℂ) (a e x y : Fin 2) (c d : Bool) (j k : Fin 2)
    (q : DerivativeLiteratureHiggs.A) :
    probe p a e x y (psi c j*psi d k*scalarEmbed q) = delta a e (c,j) (d,k)*
      ColoredFourWaveEvaluation.onJets (momenta p) (ColoredWavePairing.amplitudes x y) q := by
  simp [probe,psi,MixedJetAlgebra.odd,MixedScalarInclusion.embed,
    Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,
    MixedFourWaveEvaluation.probe_tmul,odd_pair,delta]

theorem functional_scalar_left (a e : Fin 2) (q : DerivativeLiteratureHiggs.A) :
    WeylHiggsWaveSum.functional (psi false a*psi true e*scalarEmbed q) =
      ∑ s : Fin 4, WeylHiggsWaveSum.weight a e s *
        ∑ x : Fin 2, ∑ y : Fin 2,
          ColoredFourWaveEvaluation.onJets (momenta (WeylHiggsWaveSum.momentum s))
            (ColoredWavePairing.amplitudes x y) q := by
  have hi (aa ee : Fin 2) : WeylHiggsWaveSum.bySpin aa ee (psi false a*psi true e*scalarEmbed q) =
      if aa = a then if ee = e then
        ∑ s : Fin 4, WeylHiggsWaveSum.weight a e s *
          ∑ x : Fin 2, ∑ y : Fin 2, ColoredFourWaveEvaluation.onJets
            (momenta (WeylHiggsWaveSum.momentum s)) (ColoredWavePairing.amplitudes x y) q
      else 0 else 0 := by
    by_cases ha : aa = a <;> by_cases he : ee = e <;>
      simp only [WeylHiggsWaveSum.bySpin,LinearMap.sum_apply,LinearMap.smul_apply,
        probe_scalar,delta_left,ha,he,ite_true,ite_false,one_mul,zero_mul,
        Finset.sum_const_zero,mul_zero,smul_eq_mul]
  simp only [WeylHiggsWaveSum.functional,LinearMap.sum_apply,hi]
  simp

theorem functional_scalar_same (c : Bool) (a e : Fin 2) (q : DerivativeLiteratureHiggs.A) :
    WeylHiggsWaveSum.functional (psi c a*psi c e*scalarEmbed q) = 0 := by
  simp only [WeylHiggsWaveSum.functional,WeylHiggsWaveSum.bySpin,
    LinearMap.sum_apply,LinearMap.smul_apply,probe_scalar,delta_same,zero_mul,
    Finset.sum_const_zero,smul_zero]

theorem probe_positive_odd (p : Fin 4 → ℂ) (a e x y : Fin 2) (c : Bool) (j : Fin 2)
    (i : Fin 4) (u v : A) : probe p a e x y (u*D i (psi c j)*v) = 0 := by
  change ((LinearMap.mul' ℂ ℂ).comp
    (TensorProduct.map (oddProbe a e) FourWaveEvaluation.coefficient))
      (evaluation p x y (u*D i (psi c j)*v)) = 0
  have hz : evaluation p x y (u*D i (psi c j)*v) = 0 := by
    rw [map_mul,map_mul,odd_derivative_zero,mul_zero,zero_mul]
  rw [hz,map_zero]

theorem functional_positive_odd (c : Bool) (j : Fin 2) (i : Fin 4) (u v : A) :
    WeylHiggsWaveSum.functional (u*D i (psi c j)*v) = 0 := by
  simp only [WeylHiggsWaveSum.functional,WeylHiggsWaveSum.bySpin,LinearMap.sum_apply,
    LinearMap.smul_apply,probe_positive_odd,Finset.sum_const_zero,smul_zero]

end
end Physics.WeylHiggsWaveWords

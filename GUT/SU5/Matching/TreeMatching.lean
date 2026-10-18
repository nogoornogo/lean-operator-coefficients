import GUT.SU5.Matching.HeavyCurrents
import Physics.FieldTheory.Matching.PairedVector
import Physics.StandardModel.Operators.QqueSpinorExterior

open Math

/-! Derivative-free tree matching in an explicitly normalized paired-field
model. `orderedWilson` uses the current order (q,u,q,e); no Grassmann
reordering sign, S-matrix normalization or decay rate is claimed here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.TreeMatching
noncomputable section
open SMEpsilonTensor StandardSMGaugeTensor HeavyCurrents
open scoped TensorProduct

def upSource (i : Fin 3) (w : Fin 2) (q : Quark) (u : Color)
    (s v : WeylSpinor.Space) : PairedVector.Vector :=
  upCurrent i w q u • PairedVector.rankOne s v

def electronSource (i : Fin 3) (w : Fin 2) (q : Quark) (e : ℂ)
    (t l : WeylSpinor.Space) : PairedVector.Vector :=
  electronCurrent i w q e • PairedVector.rankOne t l

def orderedWilson (g v : ℝ) : ℂ := -( (g : ℂ) ^ 2 / (AdjointMass.massSquared g v : ℂ))

def eliminated (g v : ℝ) (q r : Quark) (u : Color) (e : ℂ)
    (s t z l : WeylSpinor.Space) : ℂ :=
  ∑ i : Fin 3, ∑ w : Fin 2,
    let J := upSource i w q u s z
    let K := electronSource i w r e t l
    PairedQuadraticElimination.action PairedVector.pairing
      (AdjointMass.massSquared g v : ℂ) (g : ℂ) J K
      (PairedQuadraticElimination.solution (AdjointMass.massSquared g v : ℂ) (g : ℂ) J)
      (PairedQuadraticElimination.solution (AdjointMass.massSquared g v : ℂ) (g : ℂ) K)

theorem eliminated_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (q r : Quark) (u : Color) (e : ℂ) (s t z l : WeylSpinor.Space) :
    eliminated g v q r u e s t z l =
      orderedWilson g v * qque ((q ⊗ₜ[ℂ] r) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) *
        (eps2 s t * eps2 z l) := by
  have hm := AdjointMass.massSquared_ne_zero hg hv
  simp only [eliminated, PairedVector.eliminate _ _ hm, upSource, electronSource,
    map_smul, LinearMap.smul_apply, smul_eq_mul, PairedVector.pairing_rankOne]
  rw [← contraction_eq_qque]
  simp only [contraction, orderedWilson, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem orderedWilson_ne_zero {g v : ℝ} (hg : g ≠ 0) (hv : v ≠ 0) :
    orderedWilson g v ≠ 0 := by
  apply neg_ne_zero.mpr
  exact div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hg))
    (AdjointMass.massSquared_ne_zero hg hv)

theorem orderedWilson_value {g v : ℝ} (hg : g ≠ 0) (hv : v ≠ 0) :
    orderedWilson g v = -1 / (25 * (v : ℂ) ^ 2) := by
  have hg' : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  simp only [orderedWilson, AdjointMass.massSquared, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  field_simp

theorem eliminated_probe (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    eliminated g v (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0)
      (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) (colorBasis 2) 1
      (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1) = orderedWilson g v := by
  rw [eliminated_eq g v hg hv, qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem eliminated_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    eliminated g v (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0)
      (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) (colorBasis 2) 1
      (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1) ≠ 0 := by
  rw [eliminated_probe g v hg hv]
  exact orderedWilson_ne_zero hg hv

/-- The ordered tensor identified by `eliminated_eq`, in the existing
external-field convention. This is not a Grassmann reordering theorem. -/
def matchedInternal (g v : ℝ) : Representation.IntertwiningMap
    ((quark.tprod quark).tprod (upRight.tprod electronRight))
    (Representation.trivial ℂ GaugeGroup ℂ) := orderedWilson g v • qqueIntertwiner

theorem matchedOrdered_eq_eliminated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (q r : Quark) (u : Color) (e : ℂ) (s t z l : WeylSpinor.Space) :
    QqueSpinorExterior.ordered quark upRight electronRight (matchedInternal g v)
      (((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (r ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
        ((u ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] l))) =
      eliminated g v q r u e s t z l := by
  rw [QqueSpinorExterior.ordered_apply, eliminated_eq g v hg hv]
  rfl

def matchedExterior (g v : ℝ) :=
  QqueSpinorExterior.exterior quark upRight electronRight (matchedInternal g v)

theorem matchedExterior_probe (g v : ℝ) :
    matchedExterior g v (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      ((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakBasis 0)
      ((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] weakBasis 1)
      (colorBasis 2 ⊗ₜ[ℂ] weakBasis 0)
      ((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1))) = 2 * orderedWilson g v := by
  simp only [matchedExterior, QqueSpinorExterior.exterior, FourSlotAlternation.coefficient_slots]
  simp only [QqueSpinorExterior.ordered_apply]
  change orderedWilson g v * qque _ * _ - orderedWilson g v * qque _ * _ = _
  rw [qque_tmul, qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]
  ring

theorem matchedExterior_nonzero {g v : ℝ} (hg : g ≠ 0) (hv : v ≠ 0) :
    matchedExterior g v ≠ 0 := by
  intro h
  have hp := matchedExterior_probe g v
  rw [h] at hp
  have hz : 2 * orderedWilson g v = 0 := by simpa using hp.symm
  exact (mul_ne_zero (by norm_num) (orderedWilson_ne_zero hg hv)) hz

end
end GUT.SU5.TreeMatching

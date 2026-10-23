import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFlavorComponents

open Math

/-! Normalized interpretation of Heeck–Le 2604.25134v2, Section 6, Q³L.
The printed order is Q,Q,Q,L. Brackets mean the algebraic epsilon pairing;
this file makes no claim about amplitudes or LSZ normalization. -/
namespace Physics.HeeckLeQqqlConvention
set_option autoImplicit false
noncomputable section
open FourDoubletInvariant FourDoubletProductExchange FourDoubletProductComponents

/-- Literal weak and Weyl contraction in Q,Q,Q,L order. -/
def paperLocal (a b c d s t v w : Space) : ℂ :=
  eps a d * eps b c * (eps s t * eps v w)

def seed : Coordinates := ![![-1, 0], ![1, 0]]

theorem literal (a b c d s t v w : Space) :
    paperLocal a b c d s t v w = evaluate seed a b c d s t v w := by
  simp [paperLocal, seed, evaluate, eps]
  ring

/-- All three flavor symmetry types have nonzero local projections. -/
theorem seed_components : extract seed = ![-1/6, -1/2, -2/3, 1/3] := by
  ext i
  fin_cases i <;> norm_num [seed, extract]

theorem seed_symmetric_nonzero : extract seed 0 ≠ 0 := by
  rw [seed_components]
  norm_num

theorem seed_alternating_nonzero : extract seed 1 ≠ 0 := by
  rw [seed_components]
  norm_num

theorem seed_mixed_nonzero : extract seed 2 ≠ 0 := by
  rw [seed_components]
  norm_num

/-- Local part of the unnormalized six-term orbit. The color epsilon's
permutation sign cancels the fermionic permutation sign. -/
def orbit (a b c d e f : ℂ) : Coordinates :=
  a • seed + b • exchange01 seed + c • exchange12 seed +
    d • exchange01 (exchange12 seed) + e • exchange12 (exchange01 seed) +
    f • exchange01 (exchange12 (exchange01 seed))

/-- An explicit right inverse for the published seed orbit. The symmetric
and alternating components require factors -1 and -1/3, respectively. -/
theorem orbit_inverse (t u v w z : ℂ) (hc : v+w+z=0) :
    orbit (-t-u/3+v) (-t+u/3+w) (-t+u/3+v)
      (-t-u/3+w) (-t-u/3+z) (-t+u/3+z) =
      assemble ![t,u,w,v] := by
  have hz : z = -v-w := by linear_combination hc
  rw [hz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbit, seed, exchange01, exchange12, assemble, smul_eq_mul] <;> ring

open Representation
open scoped TensorProduct
variable {H Q L : Type*} [Group H] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ H Q) (l : Representation ℂ H L)

def source (f : QqqlFlavorComponents.residualSpace q l) : QqqlExchange.Residual q l :=
  -f.val 0 - (1/3 : ℂ) • f.val 1 + f.val 3

theorem source_apply (f : QqqlFlavorComponents.residualSpace q l)
    (p : (Q ⊗[ℂ] Q) ⊗[ℂ] (Q ⊗[ℂ] L)) :
    source q l f p = -f.val 0 p - f.val 1 p / 3 + f.val 3 p := by
  simp [source, smul_eq_mul]
  ring

theorem source_orbit (f : QqqlFlavorComponents.residualSpace q l)
    (x y z : Q) (h : L) :
    orbit (source q l f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)))
      (source q l f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)))
      (source q l f ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] h)))
      (source q l f ((y ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] h)))
      (source q l f ((z ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] h)))
      (source q l f ((z ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] h))) =
    assemble (QqqlFlavorComponents.values q l f.val x y z h) := by
  let v := QqqlFlavorComponents.values q l f.val
  have hr := QqqlFlavorComponents.component_relations q l f x y z h
  have hr' := QqqlFlavorComponents.component_relations q l f y x z h
  have hr'' := QqqlFlavorComponents.component_relations q l f z x y h
  have ht01 := hr.1
  have ht12 := hr.2.1
  have ht23 := hr'.2.1
  have ht31 := hr''.1.symm
  have ht32 := hr''.2.1
  have hu01 := hr.2.2.1
  have hu12 := hr.2.2.2.1
  have hu23 := hr'.2.2.2.1
  have hu31 := hr''.2.2.1
  have hu31' : QqqlFlavorComponents.values q l f.val z x y h 1 =
      -QqqlFlavorComponents.values q l f.val x z y h 1 := by linear_combination hu31
  have hu32 := hr''.2.2.2.1
  have hv12 := hr.2.2.2.2.2.1
  have hv23 := hr'.2.2.2.2.2.1
  have hv32 := hr''.2.2.2.2.2.1
  have hc := hr.2.2.2.2.2.2
  have hs := hr.2.2.2.2.1
  simp only [source_apply]
  change orbit (-v x y z h 0 - v x y z h 1 / 3 + v x y z h 3)
    (-v y x z h 0 - v y x z h 1 / 3 + v y x z h 3)
    (-v x z y h 0 - v x z y h 1 / 3 + v x z y h 3)
    (-v y z x h 0 - v y z x h 1 / 3 + v y z x h 3)
    (-v z x y h 0 - v z x y h 1 / 3 + v z x y h 3)
    (-v z y x h 0 - v z y x h 1 / 3 + v z y x h 3) = _
  dsimp only [v]
  rw [ht23, ht01, ht32, ht31, ht12,
    hu23, hu01, hu32, hu31', hu12, hv12, hv23, hv32]
  have hh := orbit_inverse (v x y z h 0) (v x y z h 1)
    (v x y z h 3) (v y x z h 3) (v z x y h 3) hc
  convert hh using 1
  · simp only [v, neg_neg, neg_div, sub_neg_eq_add]
  · congr 1
    ext i
    fin_cases i <;> simp [v, hs]

end
end Physics.HeeckLeQqqlConvention

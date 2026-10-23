import Math.RepresentationTheory.Unitary.FourDoubletProductExchange
import Physics.StandardModel.Gauge.Tensors.SMEpsilonTensor
import Math.LinearAlgebra.Selection.StatisticalCompleteness

open Math

/-! Explicit necessary and sufficient adjacent-exchange equations for the
four weak/Weyl contractions of qqql. Local exhaustiveness and exterior descent
are separate obligations; this file does not assume or assert them. -/
namespace Physics.QqqlExchange
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor FourDoubletInvariant FourDoubletProductExchange
open scoped TensorProduct

variable {R Q L : Type*} [Group R] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

abbrev Residual := IntertwiningMap ((q.tprod q).tprod (q.tprod l))
  (Representation.trivial ℂ R ℂ)
abbrev Family := Fin 2 → Fin 2 → Residual q l

def values (k : Family q l) (x y z : Q) (h : L) : Coordinates :=
  fun i j => k i j ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))

def contraction (k : Family q l) (a b c : Color) (v w : Fin 4 → Space)
    (x y z : Q) (h : L) : ℂ :=
  eps3 a b c * evaluate (values q l k x y z h)
    (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3)

def Condition (k : Family q l) : Prop := ∀ x y z h,
  exchange01 (values q l k y x z h) = values q l k x y z h ∧
  exchange12 (values q l k x z y h) = values q l k x y z h

/-- An explicit residual subspace, containing no local gauge or Lorentz condition. -/
def residualSpace : Submodule ℂ (Family q l) where
  carrier := {k | Condition q l k}
  zero_mem' := by
    intro x y z h
    constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [values, exchange01, exchange12]
  add_mem' := by
    intro k m hk hm x y z h
    constructor
    · change exchange01 (values q l k y x z h + values q l m y x z h) =
        values q l k x y z h + values q l m x y z h
      rw [exchange01_add, (hk x y z h).1, (hm x y z h).1]
    · change exchange12 (values q l k x z y h + values q l m x z y h) =
        values q l k x y z h + values q l m x y z h
      rw [exchange12_add, (hk x y z h).2, (hm x y z h).2]
  smul_mem' := by
    intro c k hk x y z h
    constructor
    · change exchange01 (c • values q l k y x z h) = c • values q l k x y z h
      rw [exchange01_smul, (hk x y z h).1]
    · change exchange12 (c • values q l k x z y h) = c • values q l k x y z h
      rw [exchange12_smul, (hk x y z h).2]

def Antisymmetric (k : Family q l) : Prop :=
  ∀ (a b c : Color) (v w : Fin 4 → Space) x y z h,
    contraction q l k b a c (v ∘ Equiv.swap 0 1) (w ∘ Equiv.swap 0 1) y x z h =
      -contraction q l k a b c v w x y z h ∧
    contraction q l k a c b (v ∘ Equiv.swap 1 2) (w ∘ Equiv.swap 1 2) x z y h =
      -contraction q l k a b c v w x y z h

/-- The local reconstruction is independent of flavor multiplicity. Its probes
make it injective; exchange equations are transported through this map. -/
def reconstructLinear : Coordinates →ₗ[ℂ]
    (Color → Color → Color → (Fin 4 → Space) → (Fin 4 → Space) → ℂ) where
  toFun k a b c v w := eps3 a b c * evaluate k
    (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3)
  map_add' k m := by
    funext a b c v w
    simp [evaluate]
    ring
  map_smul' t k := by
    funext a b c v w
    simp [evaluate, smul_eq_mul]
    ring

theorem reconstruct_injective : Function.Injective reconstructLinear := by
  intro k m h
  funext i j
  have hp := congrFun (congrFun (congrFun (congrFun (congrFun h
    (colorBasis 0)) (colorBasis 1)) (colorBasis 2)) (probe i)) (probe j)
  simpa [reconstructLinear, evaluate_probe, eps3, colorBasis, Fin.ext_iff] using hp

/-- Both independently computed local exchange matrices satisfy the common
injective-reconstruction statistics criterion. The color sign is retained. -/
theorem local_statistics_iff (k n m : Coordinates) :
    (exchange01 k = m ∧ exchange12 n = m) ↔
      (∀ a b c v w,
        reconstructLinear k b a c (v ∘ Equiv.swap 0 1) (w ∘ Equiv.swap 0 1) =
          -reconstructLinear m a b c v w) ∧
      (∀ a b c v w,
        reconstructLinear n a c b (v ∘ Equiv.swap 1 2) (w ∘ Equiv.swap 1 2) =
          -reconstructLinear m a b c v w) := by
  have compat01 (k : Coordinates) : reconstructLinear (exchange01 k) =
      (fun a b c v w => -reconstructLinear k b a c
        (v ∘ Equiv.swap 0 1) (w ∘ Equiv.swap 0 1)) := by
    funext a b c v w
    simp only [reconstructLinear, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def]
    norm_num [Equiv.swap_apply_def, Fin.ext_iff]
    rw [evaluate_exchange01]
    rw [exchange01_involutive]
    have hc : eps3 b a c = -eps3 a b c := by unfold eps3; ring
    rw [hc]
    ring
  have compat12 (k : Coordinates) : reconstructLinear (exchange12 k) =
      (fun a b c v w => -reconstructLinear k a c b
        (v ∘ Equiv.swap 1 2) (w ∘ Equiv.swap 1 2)) := by
    funext a b c v w
    simp only [reconstructLinear, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def]
    norm_num [Equiv.swap_apply_def, Fin.ext_iff]
    rw [evaluate_exchange12]
    rw [exchange12_involutive]
    have hc : eps3 a c b = -eps3 a b c := by unfold eps3; ring
    rw [hc]
    ring
  have h01 := StatisticalCompleteness.relation_iff reconstructLinear reconstruct_injective
    (fun f a b c v w => -f b a c (v ∘ Equiv.swap 0 1) (w ∘ Equiv.swap 0 1))
    exchange01 compat01 (1 : ℂ) k m
  have h12 := StatisticalCompleteness.relation_iff reconstructLinear reconstruct_injective
    (fun f a b c v w => -f a c b (v ∘ Equiv.swap 1 2) (w ∘ Equiv.swap 1 2))
    exchange12 compat12 (1 : ℂ) n m
  simp only [one_smul, funext_iff, neg_eq_iff_eq_neg] at h01 h12
  simpa only [funext_iff] using and_congr h01 h12

theorem swap01 (k : Family q l) (a b c : Color) (v w : Fin 4 → Space) (x y z : Q) (h : L) :
    contraction q l k b a c (v ∘ Equiv.swap 0 1) (w ∘ Equiv.swap 0 1) y x z h =
      -eps3 a b c * evaluate (exchange01 (values q l k y x z h))
        (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3) := by
  simp only [contraction, Function.comp_def]
  norm_num [Equiv.swap_apply_def, Fin.ext_iff]
  rw [evaluate_exchange01]
  have hc : eps3 b a c = -eps3 a b c := by unfold eps3; ring
  rw [hc, neg_mul]

theorem swap12 (k : Family q l) (a b c : Color) (v w : Fin 4 → Space) (x y z : Q) (h : L) :
    contraction q l k a c b (v ∘ Equiv.swap 1 2) (w ∘ Equiv.swap 1 2) x z y h =
      -eps3 a b c * evaluate (exchange12 (values q l k x z y h))
        (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3) := by
  simp only [contraction, Function.comp_def]
  norm_num [Equiv.swap_apply_def, Fin.ext_iff]
  rw [evaluate_exchange12]
  have hc : eps3 a c b = -eps3 a b c := by unfold eps3; ring
  rw [hc, neg_mul]

theorem antisymmetric_iff (k : Family q l) : Antisymmetric q l k ↔ Condition q l k := by
  constructor
  · intro hk x y z h
    apply (local_statistics_iff (values q l k y x z h)
      (values q l k x z y h) (values q l k x y z h)).mpr
    constructor
    · intro a b c v w
      exact (hk a b c v w x y z h).1
    · intro a b c v w
      exact (hk a b c v w x y z h).2
  · intro hk a b c v w x y z h
    obtain ⟨h01, h12⟩ := (local_statistics_iff (values q l k y x z h)
      (values q l k x z y h) (values q l k x y z h)).mp (hk x y z h)
    exact ⟨h01 a b c v w, h12 a b c v w⟩

end
end Physics.QqqlExchange

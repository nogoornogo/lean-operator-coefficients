import GUT.SU6.Adapters.StandardSMContragredient
import Physics.StandardModel.Gauge.ExteriorPairing
import Mathlib.LinearAlgebra.ExteriorPower.Basis

open Math

/-!
# Actual standard branching of the exterior square

The alternating contraction below is defined on actual vectors. Its
components are color epsilon, the mixed tensor, weak epsilon, and wedges
with the fixed sixth coordinate. Hypercharges are in units of 6Y.
-/

set_option autoImplicit false

namespace GUT.StandardSMExterior

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

abbrev Six := StandardSMFullGaugeMass.Heavy
abbrev Blocks := Module.Dual ℂ Color × (Quark × (Module.Dual ℂ ℂ × (Color × Weak)))

def blocksRho : Representation ℂ GaugeGroup Blocks :=
  upRight.dual.prod (quark.prod (electronRight.dual.prod
    ((twist color (-2)).prod (twist weak 3))))

def pair (a b : Six) : Blocks :=
  (eps3Trilin a.1 b.1,
    (a.1 ⊗ₜ[ℂ] b.2.1 - b.1 ⊗ₜ[ℂ] a.2.1,
      (eps2 a.2.1 b.2.1 • (LinearMap.id : ℂ →ₗ[ℂ] ℂ),
        (b.2.2 • a.1 - a.2.2 • b.1, b.2.2 • a.2.1 - a.2.2 • b.2.1))))

theorem pair_add_left (a b c : Six) : pair (a + b) c = pair a c + pair b c := by
  simp only [pair, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply,
    TensorProduct.add_tmul, TensorProduct.tmul_add, smul_add, add_smul]
  have he : eps2 (a.2.1 + b.2.1) c.2.1 = eps2 a.2.1 c.2.1 + eps2 b.2.1 c.2.1 := by
    simp [eps2]; ring
  rw [he, add_smul]
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  repeat' constructor
  all_goals abel

theorem pair_add_right (a b c : Six) : pair a (b + c) = pair a b + pair a c := by
  simp only [pair, Prod.fst_add, Prod.snd_add, map_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add, smul_add, add_smul]
  have he : eps2 a.2.1 (b.2.1 + c.2.1) = eps2 a.2.1 b.2.1 + eps2 a.2.1 c.2.1 := by
    simp [eps2]; ring
  rw [he, add_smul]
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  repeat' constructor
  all_goals abel

theorem pair_smul_left (r : ℂ) (a b : Six) : pair (r • a) b = r • pair a b := by
  simp [pair, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_sub, smul_smul, mul_comm]

theorem pair_smul_right (r : ℂ) (a b : Six) : pair a (r • b) = r • pair a b := by
  simp [pair, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_sub, smul_smul, mul_comm]

theorem pair_self (a : Six) : pair a a = 0 := by
  have hc : eps3Trilin a.1 a.1 = 0 := by
    apply LinearMap.ext; intro c
    change eps3 a.1 a.1 c = 0
    simp [eps3]; ring
  simp [pair, hc, eps2, mul_comm]

def alternating : Six [⋀^Fin 2]→ₗ[ℂ] Blocks where
  toFun v := pair (v 0) (v 1)
  map_update_add' v i a b := by
    fin_cases i <;> simp [pair_add_left, pair_add_right]
  map_update_smul' v i r a := by
    fin_cases i <;> simp [pair_smul_left, pair_smul_right]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      rw [hij]; exact pair_self _
    · change v 1 = v 0 at hij
      rw [hij]; exact pair_self _
    · exact (hne rfl).elim

def branch : (⋀[ℂ]^2 (Fin 6 → ℂ)) →ₗ[ℂ] Blocks :=
  exteriorPower.alternatingMapLinearEquiv
    (alternating.compLinearMap StandardSMGroup.splitEquiv.toLinearMap)

@[simp] theorem branch_wedge (v : Fin 2 → (Fin 6 → ℂ)) :
    branch (exteriorPower.ιMulti ℂ 2 v) =
      pair (StandardSMGroup.splitEquiv (v 0)) (StandardSMGroup.splitEquiv (v 1)) := by
  rw [branch, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem pair_covariant (g : GaugeGroup) (a b : Six) :
    pair (StandardSMGroup.heavy g a) (StandardSMGroup.heavy g b) = blocksRho g (pair a b) := by
  apply Prod.ext
  · apply LinearMap.ext; intro c
    change eps3 (twist color (-2) g a.1) (twist color (-2) g b.1) c =
      eps3 a.1 b.1 (upRight g⁻¹ c)
    simpa only [Representation.self_inv_apply] using
      color_pair_invariant g a.1 b.1 (upRight g⁻¹ c)
  · apply Prod.ext
    · change (twist color (-2) g a.1 ⊗ₜ[ℂ] twist weak 3 g b.2.1) -
        (twist color (-2) g b.1 ⊗ₜ[ℂ] twist weak 3 g a.2.1) =
        quark g (a.1 ⊗ₜ[ℂ] b.2.1 - b.1 ⊗ₜ[ℂ] a.2.1)
      rw [map_sub, ← mixed_pair_covariant, ← mixed_pair_covariant]
    · apply Prod.ext
      · apply LinearMap.ext; intro z
        change eps2 (twist weak 3 g a.2.1) (twist weak 3 g b.2.1) * z =
          eps2 a.2.1 b.2.1 * electronRight g⁻¹ z
        simpa only [Representation.self_inv_apply] using
          weak_pair_invariant g a.2.1 b.2.1 (electronRight g⁻¹ z)
      · apply Prod.ext
        · change b.2.2 • twist color (-2) g a.1 - a.2.2 • twist color (-2) g b.1 =
            twist color (-2) g (b.2.2 • a.1 - a.2.2 • b.1)
          simp
        · change b.2.2 • twist weak 3 g a.2.1 - a.2.2 • twist weak 3 g b.2.1 =
            twist weak 3 g (b.2.2 • a.2.1 - a.2.2 • b.2.1)
          simp

def exteriorRho : Representation ℂ GaugeGroup (⋀[ℂ]^2 (Fin 6 → ℂ)) :=
  (CertifiedConstructions.exteriorActual FundamentalRepresentation.actual 2).rho.comp
    StandardSMGroup.hom

def branchIntertwiner : Representation.IntertwiningMap exteriorRho blocksRho where
  toLinearMap := branch
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext; intro v
    change branch (exteriorPower.map 2 (FundamentalRepresentation.rho (StandardSMGroup.hom g))
      (exteriorPower.ιMulti ℂ 2 v)) = blocksRho g (branch (exteriorPower.ιMulti ℂ 2 v))
    rw [exteriorPower.map_apply_ιMulti, branch_wedge, branch_wedge]
    simpa only [Function.comp_apply, StandardSMGroup.splitEquiv_action] using
      pair_covariant g (StandardSMGroup.splitEquiv (v 0)) (StandardSMGroup.splitEquiv (v 1))

def wedge (a b : Six) : ⋀[ℂ]^2 (Fin 6 → ℂ) :=
  exteriorPower.ιMulti ℂ 2 ![StandardSMGroup.splitEquiv.symm a, StandardSMGroup.splitEquiv.symm b]

@[simp] theorem branch_wedge_split (a b : Six) : branch (wedge a b) = pair a b := by
  simp [wedge]

@[simp] theorem pair_color_color (a b : Color) :
    pair (a, (0, 0)) (b, (0, 0)) = (eps3Trilin a b, 0) := by
  simp [pair, eps2]

@[simp] theorem pair_color_weak (a : Color) (b : Weak) :
    pair (a, (0, 0)) (0, (b, 0)) = (0, (a ⊗ₜ[ℂ] b, 0)) := by
  simp [pair, eps2]

@[simp] theorem pair_weak_weak (a b : Weak) :
    pair (0, (a, 0)) (0, (b, 0)) = (0, (0, (eps2 a b • (LinearMap.id : ℂ →ₗ[ℂ] ℂ), 0))) := by
  simp [pair]

@[simp] theorem pair_color_singlet (a : Color) :
    pair (a, (0, 0)) (0, (0, 1)) = (0, (0, (0, (a, 0)))) := by
  simp [pair, eps2]

@[simp] theorem pair_weak_singlet (a : Weak) :
    pair (0, (a, 0)) (0, (0, 1)) = (0, (0, (0, (0, a)))) := by
  simp [pair, eps2]

theorem range_color (a : Color) : (0, (0, (0, (a, 0)))) ∈ LinearMap.range branch :=
  ⟨wedge (a, (0, 0)) (0, (0, 1)), by simp⟩

theorem range_weak (a : Weak) : (0, (0, (0, (0, a)))) ∈ LinearMap.range branch :=
  ⟨wedge (0, (a, 0)) (0, (0, 1)), by simp⟩

theorem range_quark (q : Quark) : (0, (q, 0)) ∈ LinearMap.range branch := by
  induction q using TensorProduct.inductionOn with
  | tmul a b => exact ⟨wedge (a, (0, 0)) (0, (b, 0)), by simp⟩
  | add a b ha hb =>
      simpa only [Prod.mk_add_mk, add_zero] using (LinearMap.range branch).add_mem ha hb

theorem range_electron (phi : Module.Dual ℂ ℂ) :
    (0, (0, (phi, 0))) ∈ LinearMap.range branch := by
  refine ⟨phi 1 • wedge (0, (![1, 0], 0)) (0, (![0, 1], 0)), ?_⟩
  simp only [map_smul, branch_wedge_split, pair_weak_weak]
  have he : phi 1 • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) = phi := by
    apply LinearMap.ext; intro z
    have h := phi.map_smul z (1 : ℂ)
    simpa [mul_comm] using h.symm
  simpa [eps2] using he

theorem range_up (phi : Module.Dual ℂ Color) : (phi, 0) ∈ LinearMap.range branch := by
  let e : Fin 3 → Color := Pi.basisFun ℂ (Fin 3)
  refine ⟨phi (e 0) • wedge (e 1, (0, 0)) (e 2, (0, 0)) +
    phi (e 1) • wedge (e 2, (0, 0)) (e 0, (0, 0)) +
    phi (e 2) • wedge (e 0, (0, 0)) (e 1, (0, 0)), ?_⟩
  simp only [map_add, map_smul, branch_wedge_split, pair_color_color]
  apply Prod.ext
  · apply (Pi.basisFun ℂ (Fin 3)).ext
    intro i
    change phi (e 0) * eps3 (e 1) (e 2) (e i) +
      phi (e 1) * eps3 (e 2) (e 0) (e i) +
      phi (e 2) * eps3 (e 0) (e 1) (e i) = phi (e i)
    fin_cases i <;> simp [e, eps3, Pi.basisFun_apply]
  · simp

theorem branch_surjective : Function.Surjective branch := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rintro ⟨u, q, e, c, w⟩ _
  have h := (LinearMap.range branch).add_mem
    ((LinearMap.range branch).add_mem
      ((LinearMap.range branch).add_mem
        ((LinearMap.range branch).add_mem (range_up u) (range_quark q))
        (range_electron e)) (range_color c)) (range_weak w)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using h

theorem branch_bijective : Function.Bijective branch := by
  refine ⟨?_, branch_surjective⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := branch) ?_).mpr
    branch_surjective
  simp [Blocks, Quark, Color, Weak, Module.finrank_prod, Module.finrank_tensorProduct,
    Subspace.dual_finrank_eq, exteriorPower.finrank_eq, Nat.choose]

def algebraicEquiv : Representation.Equiv exteriorRho blocksRho where
  toLinearEquiv := LinearEquiv.ofBijective branch branch_bijective
  isIntertwining' := branchIntertwiner.isIntertwining'

def analyticEquiv : Representation.Equiv
    (ConcreteSU6Representations.exteriorTwo.rho.comp StandardSMGroup.hom) blocksRho :=
  (SplitRepresentationProjection.restrictEquiv
    ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm StandardSMGroup.hom).trans algebraicEquiv

end

end GUT.StandardSMExterior

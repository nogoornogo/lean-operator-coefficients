import Physics.FieldTheory.Jets.Gauge.AbelianFieldStrength
import Math.Algebra.Jets.LinearJetEquation
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! Antisymmetry, Maxwell and Bianchi as one actual covariant linear system. -/
namespace Physics.AbelianFieldStrength
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections LorentzDirections
open scoped TensorProduct BigOperators

def antisymmetry : Pair →ₗ[ℂ] Jets :=
  (atOrder 0).comp (pairBasis.repr.toLinearMap.comp
    (LinearMap.id + (TensorProduct.comm ℂ V V).toLinearMap))

theorem antisymmetry_tmul (v w : V) : antisymmetry (v ⊗ₜ[ℂ] w) = zeroPair v w + zeroPair w v := by
  simp [antisymmetry, pair, zeroPair]

theorem antisymmetry_covariant (g : Group) (x : Pair) :
    combined field direction g (antisymmetry x) = antisymmetry ((vector.tprod vector) g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    simp only [Representation.tprod_apply, TensorProduct.map_tmul, antisymmetry_tmul,
      map_add, zeroPair_covariant]

def maxwell : V →ₗ[ℂ] Jets :=
  ∑ i : Fin 4, (JetLinear.shift i).comp ((atOrder 0).comp (pair (basis i)))

theorem maxwell_apply (v : V) : maxwell v = ∑ i : Fin 4, JetLinear.shift i (zeroPair (basis i) v) := by
  simp [maxwell, zeroPair]

theorem maxwell_covariant (g : Group) (v : V) :
    combined field direction g (maxwell v) = maxwell (vector g v) := by
  simp only [maxwell_apply, map_sum, combined_covariant, zeroPair_covariant]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let L : V →ₗ[ℂ] Jets := (JetLinear.shift j).comp ((atOrder 0).comp (pair.flip (vector g v)))
  change (∑ i : Fin 4, (direction g (Finsupp.single i 1)) j • L (vector g (basis i))) = L (basis j)
  simp only [← L.map_smul]
  rw [← map_sum, canonical_identity]

def first : Triple →ₗ[ℂ] Jets := TensorProduct.lift
  ((directionalMap.comp metric).compl₂ ((atOrder 0).comp pairBasis.repr.toLinearMap))

def cycle : Triple →ₗ[ℂ] Triple :=
  ((TensorProduct.assoc ℂ V V V).symm.trans (TensorProduct.comm ℂ Pair V)).toLinearMap

theorem cycle_tmul (v w z : V) : cycle (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) = z ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
  simp [cycle]

def bianchi : Triple →ₗ[ℂ] Jets := first + first.comp cycle + first.comp (cycle.comp cycle)

theorem first_tmul (v w z : V) : first (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) =
    directional (metric v) (zeroPair w z) := rfl

theorem bianchi_tmul (v w z : V) : bianchi (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) =
    directional (metric v) (zeroPair w z) + directional (metric z) (zeroPair v w) +
      directional (metric w) (zeroPair z v) := by
  simp only [bianchi, LinearMap.add_apply, LinearMap.comp_apply, cycle_tmul, first_tmul]

theorem bianchi_covariant (g : Group) (x : Triple) :
    combined field direction g (bianchi x) = bianchi ((vector.tprod (vector.tprod vector)) g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul w z =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul, bianchi_tmul,
        map_add, directional_covariant, zeroPair_covariant, metric_covariant]

abbrev Equations := Pair × (V × Triple)
def equationAction : Representation ℂ Group Equations :=
  (vector.tprod vector).prod (vector.prod (vector.tprod (vector.tprod vector)))

def seed : Equations →ₗ[ℂ] Jets := antisymmetry.comp (LinearMap.fst ℂ Pair (V × Triple)) +
  maxwell.comp ((LinearMap.fst ℂ V Triple).comp (LinearMap.snd ℂ Pair (V × Triple))) +
  bianchi.comp ((LinearMap.snd ℂ V Triple).comp (LinearMap.snd ℂ Pair (V × Triple)))

theorem seed_covariant (g : Group) (x : Equations) :
    combined field direction g (seed x) = seed (equationAction g x) := by
  simp only [seed, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_add, antisymmetry_covariant, maxwell_covariant, bianchi_covariant]
  rfl

abbrev relations := LinearJetEquation.relations seed
abbrev Generator := LinearJetEquation.Generator seed
def action := LinearJetEquation.action seed equationAction field direction seed_covariant

theorem antisymmetry_mem (v w : V) : antisymmetry (v ⊗ₜ[ℂ] w) ∈ relations := by
  have h := LinearJetEquation.seed_mem seed (v ⊗ₜ[ℂ] w, (0, 0))
  have he : seed (v ⊗ₜ[ℂ] w, (0, 0)) = antisymmetry (v ⊗ₜ[ℂ] w) := by simp [seed]
  rw [he] at h
  exact h

theorem maxwell_mem (v : V) : maxwell v ∈ relations := by
  have h := LinearJetEquation.seed_mem seed (0, (v, 0))
  have he : seed (0, (v, 0)) = maxwell v := by simp [seed]
  rw [he] at h
  exact h

theorem bianchi_mem (v w z : V) : bianchi (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) ∈ relations := by
  have h := LinearJetEquation.seed_mem seed (0, (0, v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)))
  have he : seed (0, (0, v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z))) = bianchi (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) := by simp [seed]
  rw [he] at h
  exact h

theorem descendant_zero (p : Symbols (Fin 4)) (x : Equations) :
    relations.mkQ (LinearJetEquation.multiple p (seed x)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LinearJetEquation.descendant_mem seed p x)

end
end Physics.AbelianFieldStrength

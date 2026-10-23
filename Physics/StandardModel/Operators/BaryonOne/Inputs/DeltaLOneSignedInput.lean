import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSpeciesSupport
import Math.RepresentationTheory.Exterior.FiniteSpeciesExterior
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open Math

/-! Independent lepton-graded input on all ten signed species. The species
representation is supplied on typed carriers; central-action certificates
are separate from, and never premises in the definition of, this sector. -/
namespace Physics.DeltaLOneSignedInput
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSpeciesSupport
abbrev Species := Fin 10

def hypercharge : Species → ℤ := ![1,4,-2,-3,-6,-1,-4,2,3,6]
def baryon : Species → ℤ := ![1,1,1,0,0,-1,-1,-1,0,0]
def lepton : Species → ℤ := ![0,0,0,1,1,0,0,0,-1,-1]

def multiplicity (labels : Fin 4 → Species) (s : Species) : ℕ :=
  (Finset.univ.filter (fun i => labels i = s)).card
def counts (labels : Fin 4 → Species) : Counts :=
  ⟨multiplicity labels 0, multiplicity labels 1, multiplicity labels 2,
    multiplicity labels 3, multiplicity labels 4, multiplicity labels 5,
    multiplicity labels 6, multiplicity labels 7, multiplicity labels 8,
    multiplicity labels 9⟩

theorem sum_weights (labels : Fin 4 → Species) {A : Type*} [AddCommMonoid A]
    (w : Species → A) : ∑ i, w (labels i) = ∑ s, multiplicity labels s • w s := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun i (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (labels i)) w]
  simp [multiplicity, Finset.sum_const]

theorem slotCount_counts (labels : Fin 4 → Species) : slotCount (counts labels) = 4 := by
  have h := sum_weights labels (fun _ => (1 : ℕ))
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  simpa [slotCount, counts, Fin.sum_univ_succ, add_assoc] using h.symm

theorem hypercharge_counts (labels : Fin 4 → Species) :
    sixHypercharge (counts labels) = ∑ i, hypercharge (labels i) := by
  rw [sum_weights]
  simp [sixHypercharge, counts, hypercharge, Fin.sum_univ_succ]
  ring
theorem baryon_counts (labels : Fin 4 → Species) :
    threeBaryonDegree (counts labels) = ∑ i, baryon (labels i) := by
  rw [sum_weights]
  simp [threeBaryonDegree, counts, baryon, Fin.sum_univ_succ]
  ring
theorem lepton_counts (labels : Fin 4 → Species) :
    leptonDegree (counts labels) = ∑ i, lepton (labels i) := by
  rw [sum_weights]
  simp [leptonDegree, counts, lepton, Fin.sum_univ_succ]
  ring

variable {G : Type*} [Group G] {V : Species → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s))
abbrev Coefficient := FiniteSpeciesExterior.Coefficient r 4

/-- Only the lepton degree is imposed. Baryon number, hypercharge neutrality,
Lorentz parity and a four-family support condition are not assumed. -/
def sector (degree : ℤ) : Submodule ℂ (Coefficient r) where
  carrier := {f | ∀ labels, leptonDegree (counts labels) ≠ degree →
    FiniteSpeciesExterior.restrict r f labels = 0}
  zero_mem' := by intro labels _; ext v; rfl
  add_mem' := by
    intro f g hf hg labels hl
    ext v
    change FiniteSpeciesExterior.restrict r f labels v +
      FiniteSpeciesExterior.restrict r g labels v = 0
    rw [hf labels hl, hg labels hl]; simp
  smul_mem' := by
    intro c f hf labels hl
    ext v
    change c • FiniteSpeciesExterior.restrict r f labels v = 0
    rw [hf labels hl]; simp

theorem hypercharge_of_nonzero (f : Coefficient r) (labels : Fin 4 → Species)
    (v : ∀ i, V (labels i)) (circle : Circle → G)
    (hc : ∀ z s x, r s (circle z) x = (z : ℂ) ^ hypercharge s • x)
    (hf : FiniteSpeciesExterior.restrict r f labels v ≠ 0) :
    sixHypercharge (counts labels) = 0 := by
  rw [hypercharge_counts]
  exact FiniteSpeciesExterior.weight_zero r f labels v hypercharge circle hc hf

theorem lepton_of_nonzero (f : sector r 1) (labels : Fin 4 → Species)
    (v : ∀ i, V (labels i)) (hf : FiniteSpeciesExterior.restrict r f.val labels v ≠ 0) :
    leptonDegree (counts labels) = 1 := by
  by_contra hn
  have h := f.property labels hn
  exact hf (congrArg (fun k => k v) h)

theorem triality_of_nonzero (f : Coefficient r) (labels : Fin 4 → Species)
    (v : ∀ i, V (labels i)) (z : Circle) (hz : IsPrimitiveRoot z 3) (center : G)
    (hc : ∀ s x, r s center x = (z : ℂ) ^ baryon s • x)
    (hf : FiniteSpeciesExterior.restrict r f labels v ≠ 0) :
    threeBaryonDegree (counts labels) % 3 = 0 := by
  have h := ExteriorWeightSupport.scalar_constraint (FiniteSpeciesExterior.representation r)
    f center (fun i => Pi.single (labels i) (v i))
    (fun i => (z : ℂ) ^ baryon (labels i)) (by
      intro i
      rw [FiniteSpeciesExterior.action_single, hc]
      exact Pi.single_smul _ _ _)
  rw [ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero] at h
  have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hf)
  have hcircle : z ^ (∑ i, baryon (labels i)) = 1 := by
    apply Subtype.ext
    exact he
  have hd := (hz.zpow_eq_one_iff_dvd _).mp hcircle
  rw [baryon_counts]
  exact Int.emod_eq_zero_of_dvd hd

/-- The six gauge-compatible supports are consequences of invariance on the
full signed field sum, not an assumption on the input coefficient. The two
odd-Weyl candidates still require Lorentz exclusion. -/
theorem gauge_candidates (f : sector r 1) (labels : Fin 4 → Species)
    (v : ∀ i, V (labels i)) (circle : Circle → G)
    (hy : ∀ z s x, r s (circle z) x = (z : ℂ) ^ hypercharge s • x)
    (z : Circle) (hz : IsPrimitiveRoot z 3) (center : G)
    (hb : ∀ s x, r s center x = (z : ℂ) ^ baryon s • x)
    (hf : FiniteSpeciesExterior.restrict r f.val labels v ≠ 0) :
    counts labels = duql ∨ counts labels = qque ∨ counts labels = qqql ∨
      counts labels = duue ∨ counts labels = antiQddL ∨ counts labels = antiDddE := by
  apply (gauge_admissible_iff _).mp
  exact ⟨slotCount_counts labels, lepton_of_nonzero r f labels v hf,
    hypercharge_of_nonzero r f.val labels v circle hy hf,
    triality_of_nonzero r f.val labels v z hz center hb hf⟩

theorem vanish_outside_gauge_candidates (f : sector r 1) (labels : Fin 4 → Species)
    (circle : Circle → G)
    (hy : ∀ z s x, r s (circle z) x = (z : ℂ) ^ hypercharge s • x)
    (z : Circle) (hz : IsPrimitiveRoot z 3) (center : G)
    (hb : ∀ s x, r s center x = (z : ℂ) ^ baryon s • x)
    (hn : ¬ (counts labels = duql ∨ counts labels = qque ∨ counts labels = qqql ∨
      counts labels = duue ∨ counts labels = antiQddL ∨ counts labels = antiDddE)) :
    FiniteSpeciesExterior.restrict r f.val labels = 0 := by
  ext v
  by_contra hf
  exact hn (gauge_candidates r f labels v circle hy z hz center hb hf)

end
end Physics.DeltaLOneSignedInput

import Math.RepresentationTheory.ExteriorWeightSupport
import Math.RepresentationTheory.FourTensorMultilinear
import Mathlib.LinearAlgebra.Pi

/-! Independently specified exterior coefficients on a finite sum of typed
species. Pure-species restrictions determine the entire coefficient. -/
namespace Math.FiniteSpeciesExterior
set_option autoImplicit false
noncomputable section
open Representation
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s))

def representation : Representation ℂ G (∀ s, V s) where
  toFun g := LinearMap.pi (fun s => (r s g).comp (LinearMap.proj s))
  map_one' := by ext v s; simp
  map_mul' g h := by ext v s; simp [Module.End.mul_apply, map_mul]

@[simp] theorem representation_apply (g : G) (v : ∀ s, V s) (s : S) :
    representation r g v s = r s g (v s) := rfl

theorem action_single (g : G) (s : S) (v : V s) :
    representation r g (Pi.single s v) = Pi.single s (r s g v) := by
  ext t
  by_cases h : s = t
  · subst t; simp
  · simp [Pi.single_eq_of_ne (Ne.symm h)]

abbrev Coefficient (n : ℕ) := ExteriorWeightSupport.Coefficient (representation r) (n := n)

def evaluation {n : ℕ} (f : Coefficient r n) :
    (∀ s, V s) [⋀^Fin n]→ₗ[ℂ] ℂ :=
  f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ n)

def restrict {n : ℕ} (f : Coefficient r n) (labels : Fin n → S) :
    MultilinearMap ℂ (fun i => V (labels i)) ℂ :=
  (evaluation r f).toMultilinearMap.compLinearMap (fun i => LinearMap.single ℂ V (labels i))

@[simp] theorem restrict_apply {n : ℕ} (f : Coefficient r n) (labels : Fin n → S)
    (v : ∀ i, V (labels i)) : restrict r f labels v =
    f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i))) := rfl

theorem restrict_add {n : ℕ} (f h : Coefficient r n) (labels : Fin n → S) :
    restrict r (f + h) labels = restrict r f labels + restrict r h labels := by ext v; rfl

theorem restrict_smul {n : ℕ} (z : ℂ) (f : Coefficient r n) (labels : Fin n → S) :
    restrict r (z • f) labels = z • restrict r f labels := by ext v; rfl

omit [Fintype S] in
/-- Equal finite fiber cardinalities give a slot permutation, without listing
all permutations or imposing a coordinate calculation. -/
theorem permutation_of_counts {n : ℕ} (labels pattern : Fin n → S)
    (h : ∀ s, (Finset.univ.filter (fun i => labels i = s)).card =
      (Finset.univ.filter (fun i => pattern i = s)).card) :
    ∃ p : Equiv.Perm (Fin n), labels ∘ p = pattern := by
  classical
  let e : ∀ s, {i // pattern i = s} ≃ {i // labels i = s} := fun s =>
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using (h s).symm)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

theorem restrict_perm {n : ℕ} (f : Coefficient r n) (labels : Fin n → S)
    (v : ∀ i, V (labels i)) (p : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign p • restrict r f (labels ∘ p) (fun i => v (p i)) =
      restrict r f labels v := by
  exact ((evaluation r f).map_congr_perm (fun i => Pi.single (labels i) (v i)) p).symm

theorem restrict_invariant {n : ℕ} (f : Coefficient r n) (labels : Fin n → S)
    (g : G) (v : ∀ i, V (labels i)) :
    restrict r f labels (fun i => r (labels i) g (v i)) = restrict r f labels v := by
  have h := IntertwiningMap.isIntertwining _ _ f g
    (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)))
  rw [Representation.exteriorPower_apply_ιMulti] at h
  change f (exteriorPower.ιMulti ℂ n
    (fun i => representation r g (Pi.single (labels i) (v i)))) =
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i))) at h
  rw [restrict_apply, restrict_apply]
  simpa only [action_single] using h

theorem pure_ext {n : ℕ} (f h : Coefficient r n)
    (he : ∀ labels, restrict r f labels = restrict r h labels) : f = h := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change evaluation r f v = evaluation r h v
  have expand (k : Coefficient r n) : evaluation r k v =
      ∑ labels : Fin n → S, restrict r k labels (fun i => v i (labels i)) := by
    calc
      _ = evaluation r k (fun i => ∑ s, Pi.single s (v i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = _ := (evaluation r k).toMultilinearMap.map_sum _
  rw [expand f, expand h]
  apply Finset.sum_congr rfl
  intro labels _
  rw [he]

/-- Restriction into the ordered tensor space retains all invariants; it does
not assume that the coefficient already has a contraction formula. -/
def orderedRestriction (f : Coefficient r 4) (labels : Fin 4 → S) :
    IntertwiningMap (FourTensorMultilinear.representation (fun i => r (labels i)))
      (Representation.trivial ℂ G ℂ) :=
  FourTensorMultilinear.invariantLift _ ⟨restrict r f labels, restrict_invariant r f labels⟩

theorem weight_zero {n : ℕ} (f : Coefficient r n) (labels : Fin n → S)
    (v : ∀ i, V (labels i)) (weight : S → ℤ) (circle : Circle → G)
    (hc : ∀ z s x, r s (circle z) x = (z : ℂ) ^ weight s • x)
    (hf : restrict r f labels v ≠ 0) : ∑ i, weight (labels i) = 0 := by
  apply ExteriorWeightSupport.circle_constraint (representation r) f
    (fun i => Pi.single (labels i) (v i)) (fun i => weight (labels i)) circle _ hf
  intro z i
  rw [action_single, hc]
  exact Pi.single_smul _ _ _

end
end Math.FiniteSpeciesExterior

import Math.RepresentationTheory.Exterior.ExteriorContentTree
import Math.RepresentationTheory.Content.PatternSpeciesEquiv
import Math.RepresentationTheory.Content.PatternMultiplicityEquiv

/-! A finite indexed field dictionary is realized by a tree with one leaf per
species. The dictionary transports fields and their actions, not just counts. -/
namespace Math.IndexedExteriorContent
set_option autoImplicit false
noncomputable section
open Representation ExteriorContentTree
universe u v
variable {G : Type v} [Group G]

def tree : (k : ℕ) → (Fin (k+1) → Leaf.{u} G) → Content.{u} G
  | 0, a => .leaf (a 0)
  | k+1, a => .node (.leaf (a 0)) (tree k (fun i => a i.succ))


def headTail (k : ℕ) : Unit ⊕ Fin (k+1) ≃ Fin (k+2) where
  toFun s := match s with | .inl _ => 0 | .inr i => i.succ
  invFun i := Fin.cases (.inl ()) Sum.inr i
  left_inv s := by cases s with | inl x => cases x; rfl | inr i => simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Every indexed species occurs exactly once, also at degree zero. -/
def labels : (k : ℕ) → (a : Fin (k+1) → Leaf.{u} G) → Species (tree k a) ≃ Fin (k+1)
  | 0, _ =>
      { toFun := fun _ => 0
        invFun := fun _ => ()
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => by
          have hx : x = 0 := by omega
          subst x
          rfl }
  | k+1, a => (Equiv.sumCongr (Equiv.refl Unit) (labels k (fun i => a i.succ))).trans (headTail k)

@[simp] theorem labels_zero (a : Fin 1 → Leaf.{u} G) (s : Species (tree 0 a)) :
    labels 0 a s = 0 := rfl
@[simp] theorem labels_head (k : ℕ) (a : Fin (k+2) → Leaf.{u} G) (s : Unit) :
    labels (k+1) a (.inl s) = 0 := rfl
@[simp] theorem labels_tail (k : ℕ) (a : Fin (k+2) → Leaf.{u} G) (s : Species (tree k (fun i => a i.succ))) :
    labels (k+1) a (.inr s) = (labels k (fun i => a i.succ) s).succ := rfl

/-- The canonical tree fields identify with the supplied field dictionary,
including the complete group action. -/
def fieldEquiv : (k : ℕ) → (a : Fin (k+1) → Leaf.{u} G) → (s : Species (tree k a)) →
    Representation.Equiv (fields (tree k a) s) ((a (labels k a s)).rho)
  | 0, _, _ => Representation.Equiv.refl _
  | k+1, a, .inl _ => by
      change Representation.Equiv ((a 0).rho) ((a 0).rho)
      exact Representation.Equiv.refl _
  | k+1, a, .inr s => by
      change Representation.Equiv (fields (tree k (fun i => a i.succ)) s) _
      exact fieldEquiv k (fun i => a i.succ) s

abbrev pattern (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) := labels k a ∘ ExteriorContentTree.pattern (tree k a)

def dictionaryEquiv (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) :
    Representation.Equiv (statistical (tree k a))
      (PatternExteriorSource.representation (fun s => (a s).rho) (pattern k a)) :=
  PatternSpeciesEquiv.equiv (fields (tree k a)) (fun s => (a s).rho)
    (labels k a) (fieldEquiv k a) (ExteriorContentTree.pattern (tree k a))

def decomposition (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) :
    Representation.Equiv (factor (tree k a))
      (PatternExteriorSource.representation (fun s => (a s).rho) (pattern k a)) :=
  (ExteriorContentTree.decomposition (tree k a)).trans (dictionaryEquiv k a)


theorem degree_eq (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) :
    degree (tree k a) = ∑ s, (a s).degree := by
  induction k with
  | zero => simp [tree,degree]
  | succ k ih =>
      change (a 0).degree + degree (tree k (fun i => a i.succ)) = _
      rw [ih]
      exact (Fin.sum_univ_succ (fun s => (a s).degree)).symm

@[simp] theorem pattern_head (k : ℕ) (a : Fin (k+2) → Leaf.{u} G) (i : Fin (a 0).degree) :
    pattern (k+1) a (Fin.castAdd (degree (tree k (fun j => a j.succ))) i) = 0 := by
  change labels (k+1) a (Fin.append (Sum.inl ∘ fun _ : Fin (a 0).degree => ())
    (Sum.inr ∘ ExteriorContentTree.pattern (tree k (fun j => a j.succ))) (Fin.castAdd _ i)) = 0
  rw [Fin.append_left]
  exact labels_head k a ()
@[simp] theorem pattern_tail (k : ℕ) (a : Fin (k+2) → Leaf.{u} G)
    (i : Fin (degree (tree k (fun j => a j.succ)))) :
    pattern (k+1) a (Fin.natAdd (a 0).degree i) = (pattern k (fun j => a j.succ) i).succ := by
  change labels (k+1) a (Fin.append (Sum.inl ∘ fun _ : Fin (a 0).degree => ())
    (Sum.inr ∘ ExteriorContentTree.pattern (tree k (fun j => a j.succ))) (Fin.natAdd _ i)) = _
  rw [Fin.append_right]
  exact labels_tail k a _

theorem pattern_append (k : ℕ) (a : Fin (k+2) → Leaf.{u} G) :
    pattern (k+1) a = Fin.append (fun _ : Fin (a 0).degree => 0)
      (fun i => (pattern k (fun j => a j.succ) i).succ) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact (pattern_head k a j).trans (Fin.append_left (fun _ : Fin (a 0).degree => (0 : Fin (k+2)))
      (fun i => (pattern k (fun t => a t.succ) i).succ) j).symm
  · intro j
    exact (pattern_tail k a j).trans (Fin.append_right (fun _ : Fin (a 0).degree => (0 : Fin (k+2)))
      (fun i => (pattern k (fun t => a t.succ) i).succ) j).symm

theorem pattern_counts (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) (s : Fin (k+1)) :
    (Finset.univ.filter (fun i => pattern k a i = s)).card = (a s).degree := by
  induction k with
  | zero =>
      have hs : s = 0 := by omega
      subst s
      change (Finset.univ.filter (fun _ : Fin (a 0).degree => (0 : Fin 1) = 0)).card = _
      simp
  | succ k ih =>
      rw [pattern_append,Finset.card_filter]
      change (∑ i : Fin ((a 0).degree + degree (tree k (fun j => a j.succ))),
        if Fin.append (fun _ : Fin (a 0).degree => 0)
          (fun j => (pattern k (fun t => a t.succ) j).succ) i = s then 1 else 0) = _
      rw [Fin.sum_univ_add]
      refine Fin.cases ?_ (fun j => ?_) s
      · simp only [Fin.append_left,Fin.append_right]
        simp
      · simp only [Fin.append_left,Fin.append_right]
        simp only [Fin.succ_inj,Ne.symm (Fin.succ_ne_zero j),ite_false,Finset.sum_const_zero,zero_add]
        simpa only [pattern,Function.comp_apply,Finset.card_filter] using ih (fun i => a i.succ) j


theorem degree_of_counts (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ}
    (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree) :
    degree (tree k a) = n := by
  rw [degree_eq]
  calc
    _ = ∑ s, (Finset.univ.filter (fun i => p i = s)).card :=
      Finset.sum_congr rfl (fun s _ => (hc s).symm)
    _ = n := by simpa using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ p

/-- Arbitrary orderings of the same content have the same actual statistical
source; the length equality is proved from the counts. -/
def wordDecomposition (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ}
    (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree) :
    Representation.Equiv (factor (tree k a)) (PatternExteriorSource.representation (fun s => (a s).rho) p) := by
  have hd := degree_of_counts k a p hc
  subst n
  exact (decomposition k a).trans (PatternMultiplicityEquiv.equiv (fun s => (a s).rho) (pattern k a) p
    (fun s => (pattern_counts k a s).trans (hc s).symm))

theorem finiteLeaves (k : ℕ) (a : Fin (k+1) → Leaf.{u} G)
    (h : ∀ s, Module.Finite ℂ (a s).Carrier) : FiniteLeaves (tree k a) := by
  induction k with
  | zero => exact h 0
  | succ k ih => exact ⟨h 0,ih (fun i => a i.succ) (fun i => h i.succ)⟩

theorem dimensionFormula_eq (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) :
    dimensionFormula (tree k a) = ∏ s, (Module.finrank ℂ (a s).Carrier).choose (a s).degree := by
  induction k with
  | zero => simp [tree,dimensionFormula]
  | succ k ih =>
      change (Module.finrank ℂ (a 0).Carrier).choose (a 0).degree * dimensionFormula (tree k (fun i => a i.succ)) = _
      rw [ih]
      exact (Fin.prod_univ_succ (fun s => (Module.finrank ℂ (a s).Carrier).choose (a s).degree)).symm

theorem word_dimension (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ} (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree)
    (h : ∀ s, Module.Finite ℂ (a s).Carrier) :
    Module.finrank ℂ (PatternExteriorSource.Source (fun s => (a s).rho) p) =
      ∏ s, (Module.finrank ℂ (a s).Carrier).choose (a s).degree :=
  (wordDecomposition k a p hc).finrank_eq.symm.trans
    ((ExteriorContentTree.carrier_dimension (tree k a) (finiteLeaves k a h)).trans (dimensionFormula_eq k a))

theorem characterFormula_eq (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) (g : G) :
    characterFormula (tree k a) g = ∏ s, ((a s).rho.exteriorPower (a s).degree).character g := by
  induction k with
  | zero => simp [tree,characterFormula]
  | succ k ih =>
      change ((a 0).rho.exteriorPower (a 0).degree).character g * characterFormula (tree k (fun i => a i.succ)) g = _
      rw [ih]
      exact (Fin.prod_univ_succ (fun s => ((a s).rho.exteriorPower (a s).degree).character g)).symm

theorem word_character (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ} (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree)
    (h : ∀ s, Module.Finite ℂ (a s).Carrier) (g : G) :
    (PatternExteriorSource.representation (fun s => (a s).rho) p).character g =
      ∏ s, ((a s).rho.exteriorPower (a s).degree).character g :=
  (congrFun (Representation.char_iso (wordDecomposition k a p hc)) g).symm.trans
    ((ExteriorContentTree.factor_character (tree k a) (finiteLeaves k a h) g).trans (characterFormula_eq k a g))

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
def wordWithSpectator (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ} (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree) (b : Representation ℂ G Y) :=
  ExternalInvariantTensor.tensorEquiv (wordDecomposition k a p hc) (Representation.Equiv.refl b)

def wordCoefficientEquiv (k : ℕ) (a : Fin (k+1) → Leaf.{u} G) {n : ℕ} (p : Fin n → Fin (k+1))
    (hc : ∀ s, (Finset.univ.filter (fun i => p i = s)).card = (a s).degree) (b : Representation ℂ G Y) :
    PatternCoefficientSupport.space (fun s => (a s).rho) p b ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants ((factor (tree k a)).tprod b) :=
  (PatternCoefficientSupport.equiv (fun s => (a s).rho) p b).trans
    (InvariantCoefficientTransport.alongEquiv (wordWithSpectator k a p hc b)).symm

end
end Math.IndexedExteriorContent

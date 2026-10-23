import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkInvariant

open Math

/-!
# The two-dimensional species-statistics quotient

Four transpositions generate the permutations within the two up and four
down slots. Their separate color/Weyl matrices give the statistics equations
on the 5-by-5 coordinate array. The kernel is reconstructed from entries
`(4,0)` and `(4,2)`. The finite linear algebra is isolated from invariance.
-/
namespace Physics.SixQuarkSpeciesQuotient
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SixQuarkInvariant
open scoped TensorProduct
attribute [local irreducible] reconstruct

def slotSwap (g : Fin 4) : Equiv.Perm (Fin 6) :=
  ![Equiv.swap 0 2, Equiv.swap 1 3, Equiv.swap 3 4, Equiv.swap 4 5] g

def colorMatrix : Fin 4 → Matrix (Fin 5) (Fin 5) ℂ := ![
  !![-1,-1,1,0,0; 0,1,0,0,0; 0,0,1,0,0; 0,-1,0,-1,0; 0,0,-1,0,-1],
  !![0,0,1,-1,0; 0,-1,-1,0,0; 0,0,1,0,0; -1,0,1,0,0; 0,0,-1,0,-1],
  !![-1,0,0,0,0; 0,0,1,0,0; 0,1,0,0,0; 0,0,0,0,1; 0,0,0,1,0],
  !![-1,0,1,0,-1; 0,-1,-1,0,0; 0,0,1,0,0; 0,0,0,-1,-1; 0,0,0,0,1]]

def spinMatrix : Fin 4 → Matrix (Fin 5) (Fin 5) ℂ := ![
  !![0,0,-1,0,1; 0,0,0,-1,1; -1,0,0,0,1; 0,-1,0,0,1; 0,0,0,0,1],
  !![0,1,-1,0,0; 0,1,0,0,0; -1,1,0,0,0; 0,1,0,0,-1; 0,1,0,-1,0],
  !![1,0,0,0,0; 1,-1,0,0,0; 0,0,1,0,0; 0,0,1,-1,1; 0,0,0,0,1],
  !![-1,1,0,0,1; 0,1,0,0,0; 0,0,-1,1,0; 0,0,0,1,0; 0,0,0,0,1]]

theorem color_permuted (g : Fin 4) (a : Fin 5) (v : Fin 6 → Color) :
    SixColorInvariant.pairingValue a (v ∘ slotSwap g) =
      ∑ p, colorMatrix g p a * SixColorInvariant.pairingValue p v := by
  fin_cases g <;> fin_cases a <;>
    simp [slotSwap, colorMatrix, SixColorInvariant.pairingValue,
      Fin.sum_univ_succ, Equiv.swap_apply_def, eps3] <;> ring

theorem spin_permuted (g : Fin 4) (a : Fin 5) (s : Fin 6 → Spin) :
    SixWeylMultilinear.pairingValue a (s ∘ slotSwap g) =
      ∑ p, spinMatrix g p a * SixWeylMultilinear.pairingValue p s := by
  fin_cases g <;> fin_cases a <;>
    simp [slotSwap, spinMatrix, SixWeylMultilinear.pairingValue,
      SixWeylInvariant.pairingValue, Fin.sum_univ_succ, Equiv.swap_apply_def, eps2] <;>
    ring

def residual (c : Fin 5 → Fin 5 → ℂ) (g : Fin 4) (p q : Fin 5) : ℂ :=
  c p q + ∑ a, ∑ b, colorMatrix g p a * spinMatrix g q b * c a b

def SatisfiesStatistics (c : Fin 5 → Fin 5 → ℂ) : Prop :=
  ∀ g p q, residual c g p q = 0

def transform (c : Fin 5 → Fin 5 → ℂ) (g : Fin 4) : Fin 5 → Fin 5 → ℂ :=
  fun p q => ∑ a, ∑ b, colorMatrix g p a * spinMatrix g q b * c a b

private theorem sum_exchange (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ p, ∑ q, ∑ a, ∑ b, F p q a b) = ∑ a, ∑ b, ∑ p, ∑ q, F p q a b := by
  calc
    _ = ∑ p, ∑ a, ∑ q, ∑ b, F p q a b := by
      apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_comm]
    _ = ∑ a, ∑ p, ∑ q, ∑ b, F p q a b := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro a ha
      calc
        _ = ∑ p, ∑ b, ∑ q, F p q a b := by
          apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem reconstruct_transform (c : Fin 5 → Fin 5 → ℂ) (g : Fin 4) :
    reconstruct (transform c g) = (reconstruct c).domDomCongr (slotSwap g) := by
  apply pure_ext
  intro v s
  simp only [reconstruct_apply, MultilinearMap.domDomCongr_apply]
  change (∑ p, ∑ q, transform c g p q * SixColorInvariant.pairingValue p v *
      SixWeylMultilinear.pairingValue q s) =
    ∑ a, ∑ b, c a b * SixColorInvariant.pairingValue a (v ∘ slotSwap g) *
      SixWeylMultilinear.pairingValue b (s ∘ slotSwap g)
  simp_rw [color_permuted, spin_permuted, transform, Finset.mul_sum, Finset.sum_mul]
  rw [sum_exchange]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro q hq
  ring

theorem coordinates_statistics (f : Coefficient) (hf : IsInvariant f)
    (ha : IsSpeciesAlternating f) : SatisfiesStatistics (coordinates f) := by
  have hneg : reconstruct (-coordinates f) = -f := by
    unfold reconstruct
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    simpa only [reconstruct] using congrArg Neg.neg (reconstruct_coordinates f hf)
  intro g p q
  have hs : f.domDomCongr (slotSwap g) = -f := by
    ext v
    have hp : SixSlotAlternation.PreservesPattern (slotSwap g) := by
      fin_cases g <;> decide
    have he := ha (slotSwap g) hp v
    fin_cases g <;> simpa [slotSwap, Function.comp_def] using he
  have he : reconstruct (transform (coordinates f) g) =
      reconstruct (-coordinates f) := by
    rw [reconstruct_transform, reconstruct_coordinates f hf, hs, hneg]
  have hc := congrArg coordinates he
  simp only [coordinates_reconstruct] at hc
  have hc' := congrFun (congrFun hc p) q
  change coordinates f p q + transform (coordinates f) g p q = 0
  rw [hc']
  simp

/-- The two kernel basis arrays; the two indicated entries are identity probes. -/
def embed (z : Fin 2 → ℂ) : Fin 5 → Fin 5 → ℂ :=
  !![-2*z 0, -z 0, -z 0-z 1, -z 0, -z 0+z 1;
    z 0+z 1, z 0+z 1, z 0+z 1, z 0+z 1, 0;
    -z 0-z 1, 0, -z 0-z 1, 0, 0;
    -z 0, -z 0, -z 1, -z 1, 0;
    z 0, 0, z 1, 0, 0]

theorem embed_statistics (z : Fin 2 → ℂ) : SatisfiesStatistics (embed z) := by
  intro g p q
  fin_cases g <;> fin_cases p <;> fin_cases q <;>
    simp [residual, embed, colorMatrix, spinMatrix, Fin.sum_univ_succ] <;> ring

/-- The isolated 25-coordinate linear deduction. Each normalization
checks a sparse rational row certificate; no external rank premise is used. -/
theorem kernel_reconstruct (c : Fin 5 → Fin 5 → ℂ) (h : SatisfiesStatistics c) :
    c = embed ![c 4 0, c 4 2] := by
  ext p q
  fin_cases p <;> fin_cases q
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (2 : ℂ) * (h 1 0 1) + (2 : ℂ) * (h 1 1 1) + (-1 : ℂ) * (h 2 0 1) + (2 : ℂ) * (h 2 3 1) + (-2 : ℂ) * (h 3 3 1)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 1 0 1) + (1 : ℂ) * (h 1 1 1) + (1 : ℂ) * (h 2 3 1) + (-1 : ℂ) * (h 3 3 1)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 0 2 4) + (2 : ℂ) * (h 1 0 3) + (-1 : ℂ) * (h 1 0 4) + (1 : ℂ) * (h 1 1 1) + (-1 : ℂ) * (h 2 0 3) + (1 : ℂ) * (h 2 3 1) + (1 : ℂ) * (h 2 3 3) + (-2 : ℂ) * (h 2 3 4) + (1 : ℂ) * (h 3 1 3) + (-1 : ℂ) * (h 3 3 1) + (-1 : ℂ) * (h 3 3 3) + (-1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 / 2 : ℂ) * (h 0 2 4) + (1 : ℂ) * (h 1 0 3) + (1 : ℂ) * (h 1 1 1) + (1 : ℂ) * (h 2 3 1) + (-1 : ℂ) * (h 2 3 4) + (-1 : ℂ) * (h 3 3 1) + (-1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 1 0 4) + (1 : ℂ) * (h 1 1 1) + (1 : ℂ) * (h 2 3 1) + (-1 : ℂ) * (h 2 3 3) + (-1 : ℂ) * (h 3 1 3) + (-1 : ℂ) * (h 3 3 1) + (1 : ℂ) * (h 3 3 3) + (-1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (-1 : ℂ) * (h 0 2 0) + (-1 : ℂ) * (h 0 4 0) + (1 : ℂ) * (h 2 1 0) + (1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 0 1 1) + (-1 / 2 : ℂ) * (h 0 1 4) + (-1 : ℂ) * (h 0 2 4) + (-1 : ℂ) * (h 0 4 0) + (1 : ℂ) * (h 2 1 3) + (-1 : ℂ) * (h 3 1 3) + (1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (-1 / 2 : ℂ) * (h 0 2 4) + (-1 : ℂ) * (h 0 4 0) + (1 : ℂ) * (h 2 1 2) + (1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (-1 : ℂ) * (h 0 2 4) + (-1 : ℂ) * (h 0 4 0) + (1 : ℂ) * (h 2 1 3) + (-1 : ℂ) * (h 3 1 3) + (1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 / 2 : ℂ) * (h 0 1 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 0 2 0) + (1 : ℂ) * (h 0 4 0) + (-1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (-1 : ℂ) * (h 1 1 1)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 / 2 : ℂ) * (h 0 2 4) + (1 : ℂ) * (h 0 4 0) + (-1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (-1 : ℂ) * (h 3 1 3)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 / 2 : ℂ) * (h 0 2 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (1 : ℂ) * (h 2 3 0)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 2 3 1) + (-1 : ℂ) * (h 3 3 1)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (1 : ℂ) * (h 2 3 2)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ]; ring)) (1 : ℂ) * (h 2 3 3) + (-1 : ℂ) * (h 3 3 3) + (1 : ℂ) * (h 3 3 4)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (1 : ℂ) * (h 2 3 4) + (1 : ℂ) * (h 3 3 4)
  next => rfl
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (-1 : ℂ) * (h 3 3 1)
  next => rfl
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (-1 : ℂ) * (h 3 3 3)
  next =>
    linear_combination (norm := (simp [residual, embed, colorMatrix,
      spinMatrix, Fin.sum_univ_succ])) (-1 : ℂ) * (h 3 3 4)

private def wordPerm : List (Fin 4) → Equiv.Perm (Fin 6)
  | [] => 1
  | g :: w => slotSwap g * wordPerm w

private def generatorWords : Fin 48 → List (Fin 4) := ![
  [],
  [0],
  [1],
  [2],
  [3],
  [1, 0],
  [2, 0],
  [3, 0],
  [2, 1],
  [3, 1],
  [1, 2],
  [3, 2],
  [2, 3],
  [2, 1, 0],
  [3, 1, 0],
  [1, 2, 0],
  [3, 2, 0],
  [2, 3, 0],
  [1, 2, 1],
  [3, 2, 1],
  [2, 3, 1],
  [3, 1, 2],
  [2, 3, 2],
  [1, 2, 3],
  [1, 2, 1, 0],
  [3, 2, 1, 0],
  [2, 3, 1, 0],
  [3, 1, 2, 0],
  [2, 3, 2, 0],
  [1, 2, 3, 0],
  [3, 1, 2, 1],
  [2, 3, 2, 1],
  [1, 2, 3, 1],
  [2, 3, 1, 2],
  [1, 2, 3, 2],
  [3, 1, 2, 1, 0],
  [2, 3, 2, 1, 0],
  [1, 2, 3, 1, 0],
  [2, 3, 1, 2, 0],
  [1, 2, 3, 2, 0],
  [2, 3, 1, 2, 1],
  [1, 2, 3, 2, 1],
  [1, 2, 3, 1, 2],
  [2, 3, 1, 2, 1, 0],
  [1, 2, 3, 2, 1, 0],
  [1, 2, 3, 1, 2, 0],
  [1, 2, 3, 1, 2, 1],
  [1, 2, 3, 1, 2, 1, 0]]

private theorem generators_cover : ∀ p : Equiv.Perm (Fin 6),
    SixSlotAlternation.PreservesPattern p →
      ∃ r : Fin 48, wordPerm (generatorWords r) = p := by
  decide +kernel

private theorem word_sign {X : Type*} (f : (Fin 6 → X) → ℂ)
    (h : ∀ g v, f (v ∘ slotSwap g) = -f v) (w : List (Fin 4))
    (v : Fin 6 → X) : f (v ∘ wordPerm w) = Equiv.Perm.sign (wordPerm w) • f v := by
  induction w generalizing v with
  | nil => simp [wordPerm]
  | cons g w ih =>
    have hg : Equiv.Perm.sign (slotSwap g) = -1 := by fin_cases g <;> decide
    calc
      _ = f ((v ∘ slotSwap g) ∘ wordPerm w) := rfl
      _ = Equiv.Perm.sign (wordPerm w) • f (v ∘ slotSwap g) := ih _
      _ = Equiv.Perm.sign (wordPerm (g :: w)) • f v := by
        rw [h, wordPerm, map_mul, hg, mul_comm, mul_smul]
        simp

/-- The four generators suffice for any six-input scalar function, including
tensor slots carrying multiplicities. Reuses the certified 48-word cover. -/
theorem generators_species_sign {X : Type*} (f : (Fin 6 → X) → ℂ)
    (hs : ∀ g v, f (v ∘ slotSwap g) = -f v)
    (p : Equiv.Perm (Fin 6)) (hp : SixSlotAlternation.PreservesPattern p)
    (v : Fin 6 → X) : f (v ∘ p) = Equiv.Perm.sign p • f v := by
  obtain ⟨r, hr⟩ := generators_cover p hp
  rw [← hr]
  exact word_sign f hs _ _

theorem reconstruct_speciesAlternating (c : Fin 5 → Fin 5 → ℂ)
    (hc : SatisfiesStatistics c) : IsSpeciesAlternating (reconstruct c) := by
  have hn : reconstruct (-c) = -reconstruct c := by
    simp only [reconstruct, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  have hs : ∀ g v, reconstruct c (v ∘ slotSwap g) = -reconstruct c v := by
    intro g v
    have ht : transform c g = -c := by
      ext p q
      have h := hc g p q
      change c p q + transform c g p q = 0 at h
      exact eq_neg_of_add_eq_zero_right h
    have he := reconstruct_transform c g
    rw [ht, hn] at he
    have hv := congrArg (fun f : Coefficient => f v) he
    simp only [_root_.neg_apply, MultilinearMap.domDomCongr_apply] at hv
    simpa only [Function.comp_def] using hv.symm
  intro p hp v
  obtain ⟨r, hr⟩ := generators_cover p hp
  rw [← hr]
  exact word_sign _ hs _ _

/-- The solution space of the four species-exchange constraints. -/
def statisticsKernel : Submodule ℂ (Fin 5 → Fin 5 → ℂ) where
  carrier := {c | SatisfiesStatistics c}
  zero_mem' := by intro g p q; simp [residual]
  add_mem' := by
    intro c d hc hd g p q
    have h : residual (c + d) g p q = residual c g p q + residual d g p q := by
      simp [residual, mul_add, Finset.sum_add_distrib]; ring
    rw [h, hc, hd, add_zero]
  smul_mem' := by
    intro z c hc g p q
    have h : residual (z • c) g p q = z * residual c g p q := by
      simp only [residual, Pi.smul_apply, smul_eq_mul]
      rw [mul_add]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      ring
    rw [h, hc, mul_zero]

/-- The two free entries, with an explicitly verified inverse. -/
def kernelEquiv : statisticsKernel ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun c := ![c.1 4 0, c.1 4 2]
  invFun z := ⟨embed z, embed_statistics z⟩
  left_inv c := Subtype.ext (kernel_reconstruct c.1 c.2).symm
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' c d := by ext i; fin_cases i <;> rfl
  map_smul' z c := by ext i; fin_cases i <;> rfl

theorem finrank_statisticsKernel : Module.finrank ℂ statisticsKernel = 2 := by
  rw [kernelEquiv.finrank_eq]
  simp

/-- Two evaluations on decomposable quarks, not formal coordinate entries. -/
def twoProbes (f : Coefficient) : Fin 2 → ℂ :=
  ![f (fun i => colorBasis (![0, 0, 1, 1, 2, 2] i) ⊗ₜ[ℂ]
      weakBasis (![0, 1, 0, 1, 0, 1] i)),
    f (fun i => colorBasis (![0, 0, 1, 1, 2, 2] i) ⊗ₜ[ℂ]
      weakBasis (![0, 0, 1, 1, 0, 1] i))]

theorem twoProbes_reconstruct_embed (z : Fin 2 → ℂ) :
    twoProbes (reconstruct (embed z)) = ![z 0 - z 1, z 1] := by
  ext i
  fin_cases i
  · change reconstruct (embed z) (fun i =>
      colorBasis (![0, 0, 1, 1, 2, 2] i) ⊗ₜ[ℂ] weakBasis (![0, 1, 0, 1, 0, 1] i)) =
        z 0 - z 1
    rw [reconstruct_apply]
    simp [embed, SixColorInvariant.pairingValue,
      SixWeylMultilinear.pairingValue, SixWeylInvariant.pairingValue, eps3, eps2,
      colorBasis, weakBasis, Fin.sum_univ_succ, Fin.ext_iff]
    ring
  · change reconstruct (embed z) (fun i =>
      colorBasis (![0, 0, 1, 1, 2, 2] i) ⊗ₜ[ℂ] weakBasis (![0, 0, 1, 1, 0, 1] i)) = z 1
    rw [reconstruct_apply]
    simp [embed, SixColorInvariant.pairingValue,
      SixWeylMultilinear.pairingValue, SixWeylInvariant.pairingValue, eps3, eps2,
      colorBasis, weakBasis, Fin.sum_univ_succ, Fin.ext_iff]

/-- The inverse of the raw two-probe evaluation map. -/
def fromProbes (t : Fin 2 → ℂ) : statisticsKernel :=
  ⟨embed ![t 0 + t 1, t 1], embed_statistics _⟩

theorem probes_fromProbes (t : Fin 2 → ℂ) :
    twoProbes (reconstruct (fromProbes t).1) = t := by
  rw [fromProbes, twoProbes_reconstruct_embed]
  ext i; fin_cases i <;> simp

theorem fromProbes_probes (c : statisticsKernel) :
    fromProbes (twoProbes (reconstruct c.1)) = c := by
  apply Subtype.ext
  rw [kernel_reconstruct c.1 c.2, twoProbes_reconstruct_embed]
  simp [fromProbes]

/-- The constraint solution space is linearly classified by two actual probes. -/
def probeEquiv : statisticsKernel ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun c := ![c.1 4 0 - c.1 4 2, c.1 4 2]
  invFun := fromProbes
  left_inv c := by
    apply Subtype.ext
    simpa [fromProbes] using (kernel_reconstruct c.1 c.2).symm
  right_inv t := by ext i; fin_cases i <;> simp [fromProbes, embed]
  map_add' c d := by
    ext i; fin_cases i
    · simp; ring
    · simp
  map_smul' z c := by
    ext i; fin_cases i
    · simp [smul_eq_mul]; ring
    · simp [smul_eq_mul]

theorem probeEquiv_apply (c : statisticsKernel) :
    probeEquiv c = twoProbes (reconstruct c.1) := by
  rw [kernel_reconstruct c.1 c.2, twoProbes_reconstruct_embed]
  rfl

theorem reconstruct_fromProbes (f : Coefficient) (hf : IsInvariant f)
    (ha : IsSpeciesAlternating f) :
    reconstruct (fromProbes (twoProbes f)).1 = f := by
  let c : statisticsKernel := ⟨coordinates f, coordinates_statistics f hf ha⟩
  have he := fromProbes_probes c
  rw [reconstruct_coordinates f hf] at he
  have hc := congrArg (fun c : statisticsKernel => reconstruct c.1) he
  exact hc.trans (reconstruct_coordinates f hf)

/-- The actual invariant multilinear maps with the full species sign rule. -/
def admissible : Submodule ℂ Coefficient where
  carrier := {f | IsInvariant f ∧ IsSpeciesAlternating f}
  zero_mem' := by
    constructor
    · constructor <;> intro g v <;> simp
    · intro p hp v; simp
  add_mem' := by
    intro f h hf hh
    constructor
    · constructor
      · intro g v; simp only [_root_.add_apply, hf.1.1, hh.1.1]
      · intro g v; simp only [_root_.add_apply, hf.1.2, hh.1.2]
    · intro p hp v; simp only [_root_.add_apply, hf.2 p hp, hh.2 p hp,
        smul_add]
  smul_mem' := by
    intro z f hf
    constructor
    · constructor
      · intro g v; simp only [_root_.smul_apply, hf.1.1]
      · intro g v; simp only [_root_.smul_apply, hf.1.2]
    · intro p hp v; simp only [_root_.smul_apply, hf.2 p hp]
      exact smul_comm _ _ _

/-- Reconstruction into the actual quark domain. -/
def fromProbesCoefficient (t : Fin 2 → ℂ) : admissible :=
  ⟨reconstruct (fromProbes t).1, reconstruct_invariant _,
    reconstruct_speciesAlternating _ (fromProbes t).2⟩

def coefficientProbeEquiv : admissible ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := twoProbes f.1
  invFun := fromProbesCoefficient
  left_inv f := Subtype.ext (reconstruct_fromProbes f.1 f.2.1 f.2.2)
  right_inv := probes_fromProbes
  map_add' f h := by ext i; fin_cases i <;> rfl
  map_smul' z f := by ext i; fin_cases i <;> rfl

theorem finrank_admissible : Module.finrank ℂ admissible = 2 := by
  rw [coefficientProbeEquiv.finrank_eq]
  simp

theorem eq_of_twoProbes {f h : Coefficient} (hf : IsInvariant f)
    (hh : IsInvariant h) (hfa : IsSpeciesAlternating f) (hha : IsSpeciesAlternating h)
    (he : twoProbes f = twoProbes h) : f = h := by
  rw [← reconstruct_fromProbes f hf hfa, ← reconstruct_fromProbes h hh hha, he]

end
end Physics.SixQuarkSpeciesQuotient

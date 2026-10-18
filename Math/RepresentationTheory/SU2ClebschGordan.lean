import Math.RepresentationTheory.SU2SymmetricEmbeddings
import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.RepresentationTheory.SU2DoubletDuality

/-! Actual SU2 symmetric-power tensor decomposition at all degrees. -/
namespace Math.SU2ClebschGordan
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct

abbrev Index (h d : ℕ) := Fin (min h d + 1)
def degree (h d : ℕ) (r : Index h d) : ℕ := h-r.val + (d-r.val)
abbrev Carrier (h d : ℕ) (r : Index h d) := Sym[ℂ]^(degree h d r) Doublet
def summand (h d : ℕ) (r : Index h d) := doublet.symmetricPower (degree h d r)
abbrev Tensor (h d : ℕ) := (doublet.symmetricPower h).tprod (doublet.symmetricPower d)

theorem degree_eq (h d : ℕ) (r : Index h d) : degree h d r = h+d-2*r.val := by
  have hr := r.isLt
  dsimp [degree]
  omega

def powerCast {p q : ℕ} (he : p=q) : Representation.Equiv
    (doublet.symmetricPower p) (doublet.symmetricPower q) := by
  subst q
  exact .refl _

def targetTransport (h d : ℕ) (r : Index h d) : Representation.Equiv
    (Tensor (h-r.val+r.val) (d-r.val+r.val)) (Tensor h d) :=
  ExternalInvariantTensor.tensorEquiv
    (powerCast (Nat.sub_add_cancel (by have hr:=r.isLt; omega)))
    (powerCast (Nat.sub_add_cancel (by have hr:=r.isLt; omega)))

def embed (h d : ℕ) (r : Index h d) : IntertwiningMap (summand h d r) (Tensor h d) :=
  (targetTransport h d r).toIntertwiningMap.comp
    (SU2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val)

theorem embed_injective (h d : ℕ) (r : Index h d) : Function.Injective (embed h d r) :=
  (targetTransport h d r).injective.comp
    (SU2SymmetricEmbeddings.embedding_injective (h-r.val) (d-r.val) r.val)

theorem embed_nonzero (h d : ℕ) (r : Index h d) : embed h d r ≠ 0 := by
  intro he
  have hb : SU2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val = 0 := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply (targetTransport h d r).injective
    have hx := DFunLike.congr_fun he x
    change targetTransport h d r
      (SU2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val x) = 0 at hx
    change targetTransport h d r
      (SU2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val x) = targetTransport h d r 0
    rw [map_zero]
    exact hx
  exact SU2SymmetricEmbeddings.embedding_nonzero _ _ _ hb

instance summand_irreducible (h d : ℕ) (r : Index h d) : IsIrreducible (summand h d r) :=
  WeakDoubletScalars.symmetricPower_irreducible _

def assemble (h d : ℕ) : IntertwiningMap (FiniteBlockHom.action (summand h d)) (Tensor h d) :=
  DistinctIrreducibleAssembly.assemble (A := Carrier h d) (B := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet) (summand h d) (Tensor h d) (embed h d)

theorem distinct_dimensions (h d : ℕ) (i j : Index h d) (hij : i≠j) :
    Module.finrank ℂ (Carrier h d i) ≠ Module.finrank ℂ (Carrier h d j) := by
  rw [TauCeti.SU2.finrank_symPower,TauCeti.SU2.finrank_symPower]
  intro he
  have hi:=i.isLt
  have hj:=j.isLt
  apply hij
  apply Fin.ext
  dsimp [degree] at he
  omega

theorem assemble_injective (h d : ℕ) : Function.Injective (assemble h d) := by
  unfold assemble
  generalize he : embed h d = f
  apply DistinctIrreducibleAssembly.injective
  · intro r
    rw [← he]
    exact embed_nonzero h d r
  · exact distinct_dimensions h d

private theorem ascending_sum (D J : ℕ) :
    ∑ j ∈ Finset.range (J+1), (D+2*j+1) = (J+1)*(D+J+1) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ,ih]; ring

theorem dimension_sum (h d : ℕ) :
    ∑ r : Index h d, (degree h d r + 1) = (h+1)*(d+1) := by
  simp_rw [degree_eq]
  rw [Fin.sum_univ_eq_sum_range (fun r => h+d-2*r+1) (min h d+1),
    ← Finset.sum_range_reflect]
  have he : ∀ j ∈ Finset.range (min h d+1),
      h+d-2*(min h d+1-1-j)+1 = (h+d-2*min h d)+2*j+1 := by
    intro j hj
    have hj' : j ≤ min h d := by simpa [Nat.lt_succ_iff] using hj
    omega
  rw [Finset.sum_congr rfl he,ascending_sum]
  rcases Nat.le_total h d with hh | hh
  · rw [Nat.min_eq_left hh,show h+d-2*h+h+1=d+1 by omega]
  · rw [Nat.min_eq_right hh,show h+d-2*d+d+1=h+1 by omega,mul_comm]

theorem ranks_equal (h d : ℕ) :
    Module.finrank ℂ (∀ r : Index h d, Carrier h d r) =
      Module.finrank ℂ (Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet) := by
  rw [Module.finrank_pi_fintype,Module.finrank_tensorProduct]
  simp_rw [TauCeti.SU2.finrank_symPower]
  exact dimension_sum h d

def equivalence (h d : ℕ) : Representation.Equiv
    (FiniteBlockHom.action (summand h d)) (Tensor h d) :=
  (assemble h d).ofBijective ⟨assemble_injective h d,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := ∀ r : Index h d, Carrier h d r)
      (V₂ := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet)
      (f := (assemble h d).toLinearMap) (ranks_equal h d)).mp
      (assemble_injective h d)⟩

/-- The requested actual doublet/dual tensor decomposition; finite products
represent the finite direct sum without any missing group-action premise. -/
def dualEquivalence (h d : ℕ) : Representation.Equiv
    ((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d))
    (FiniteBlockHom.action (summand h d)) :=
  (ExternalInvariantTensor.tensorEquiv (.refl (doublet.symmetricPower h))
    (SU2DoubletDuality.equivalence.symm.symmetricPower d)).trans (equivalence h d).symm

end
end Math.SU2ClebschGordan

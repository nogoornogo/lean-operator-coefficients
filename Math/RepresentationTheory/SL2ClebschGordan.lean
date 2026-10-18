import Math.RepresentationTheory.SL2SymmetricEmbeddings
import Math.RepresentationTheory.SU2ClebschGordan
import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.RepresentationTheory.SU2DoubletDuality

/-! SL2 Clebsch–Gordan from the same linear assembly as the SU2 theorem. -/
namespace Math.SL2ClebschGordan
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings
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

theorem powerCast_linearEquiv {p q : ℕ} (he : p=q) :
    (powerCast he).toLinearEquiv = (SU2ClebschGordan.powerCast he).toLinearEquiv := by
  subst q
  rfl

def targetTransport (h d : ℕ) (r : Index h d) : Representation.Equiv
    (Tensor (h-r.val+r.val) (d-r.val+r.val)) (Tensor h d) :=
  ExternalInvariantTensor.tensorEquiv
    (powerCast (Nat.sub_add_cancel (by have hr:=r.isLt; omega)))
    (powerCast (Nat.sub_add_cancel (by have hr:=r.isLt; omega)))

def embed (h d : ℕ) (r : Index h d) : IntertwiningMap (summand h d r) (Tensor h d) :=
  (targetTransport h d r).toIntertwiningMap.comp
    (SL2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val)

theorem embed_injective (h d : ℕ) (r : Index h d) : Function.Injective (embed h d r) :=
  (targetTransport h d r).injective.comp
    (SL2SymmetricEmbeddings.embedding_injective (h-r.val) (d-r.val) r.val)

theorem embed_linearMap (h d : ℕ) (r : Index h d) :
    (embed h d r).toLinearMap = (SU2ClebschGordan.embed h d r).toLinearMap := by
  change (targetTransport h d r).toLinearEquiv.toLinearMap.comp
      (SL2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val).toLinearMap =
    (SU2ClebschGordan.targetTransport h d r).toLinearEquiv.toLinearMap.comp
      (SU2SymmetricEmbeddings.embedding (h-r.val) (d-r.val) r.val).toLinearMap
  rw [SL2SymmetricEmbeddings.embedding_linearMap]
  simp only [targetTransport, SU2ClebschGordan.targetTransport,
    ExternalInvariantTensor.tensorEquiv, powerCast_linearEquiv]

def assemble (h d : ℕ) : IntertwiningMap (FiniteBlockHom.action (summand h d)) (Tensor h d) :=
  DistinctIrreducibleAssembly.assemble (A := Carrier h d) (B := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet) (summand h d) (Tensor h d) (embed h d)

theorem assemble_linearMap (h d : ℕ) :
    (assemble h d).toLinearMap = (SU2ClebschGordan.assemble h d).toLinearMap := by
  unfold assemble SU2ClebschGordan.assemble DistinctIrreducibleAssembly.assemble
  simp only [embed_linearMap]
  rfl

theorem assemble_injective (h d : ℕ) : Function.Injective (assemble h d) := by
  change Function.Injective (assemble h d).toLinearMap
  rw [assemble_linearMap]
  exact SU2ClebschGordan.assemble_injective h d

theorem ranks_equal (h d : ℕ) :
    Module.finrank ℂ (∀ r : Index h d, Carrier h d r) =
      Module.finrank ℂ (Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet) :=
  SU2ClebschGordan.ranks_equal h d

def equivalence (h d : ℕ) : Representation.Equiv
    (FiniteBlockHom.action (summand h d)) (Tensor h d) :=
  (assemble h d).ofBijective ⟨assemble_injective h d,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := ∀ r : Index h d, Carrier h d r)
      (V₂ := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet)
      (f := (assemble h d).toLinearMap) (ranks_equal h d)).mp
      (assemble_injective h d)⟩

/-- Compact invariance of any coefficient on two symmetric powers already
implies invariance under the full complex group. -/
theorem coefficient_fixed_of_compact (h d : ℕ)
    (f : (Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d Doublet) →ₗ[ℂ] ℂ)
    (hc : ∀ u x, f (Tensor h d (compactInclusion u) x) = f x) :
    ∀ g x, f (Tensor h d g x) = f x := by
  have hr (r : Index h d) : ∀ g y,
      f (embed h d r ((summand h d r) g y)) = f (embed h d r y) := by
    apply SL2SymmetricEmbeddings.coefficient_fixed_of_compact (degree h d r)
      (f.comp (embed h d r).toLinearMap)
    intro u y
    change f (embed h d r ((summand h d r) (compactInclusion u) y)) = _
    rw [(embed h d r).isIntertwining _ _ (compactInclusion u)]
    exact hc u _
  intro g x
  obtain ⟨v, rfl⟩ := (equivalence h d).surjective x
  change f (Tensor h d g (assemble h d v)) = f (assemble h d v)
  rw [← (assemble h d).isIntertwining _ _ g]
  simp only [assemble, DistinctIrreducibleAssembly.assemble_apply,
    FiniteBlockHom.action_apply, map_sum]
  exact Finset.sum_congr rfl (fun r _ => hr r g (v r))

end
end Math.SL2ClebschGordan

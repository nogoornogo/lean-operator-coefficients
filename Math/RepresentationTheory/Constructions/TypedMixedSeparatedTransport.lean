import Math.RepresentationTheory.Constructions.TypedMixedCarrierNaturality
import Math.RepresentationTheory.Constructions.TypedMixedLocalTransport

/-! Presentation changes of the separated residual carrier. Maps are induced on
the actual coinvariant/exchange quotients; completeness is used only in proofs. -/
namespace Math.TypedMixedSeparatedTransport
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M L' M' : P → Type*} {K N K' N' : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  [∀ u, AddCommGroup (L' u)] [∀ u, Module ℂ (L' u)]
  [∀ u, AddCommGroup (M' u)] [∀ u, Module ℂ (M' u)]
  [∀ u, AddCommGroup (K' u)] [∀ u, Module ℂ (K' u)]
  [∀ u, AddCommGroup (N' u)] [∀ u, Module ℂ (N' u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (a' : ∀ u, Representation ℂ G (L' u)) (b' : ∀ u, Representation ℂ G (K' u))
  (c' : ∀ u, Representation ℂ H (M' u)) (d' : ∀ u, Representation ℂ H (N' u))
  (e : ∀ u, Representation.Equiv (TypedMixedSeparatedHom.residualF (L := L) c u)
    (TypedMixedSeparatedHom.residualF (L := L') c' u))
  (f : ∀ u, Representation.Equiv (TypedMixedSeparatedHom.residualB (K := K) d u)
    (TypedMixedSeparatedHom.residualB (K := K') d' u))
  (he : ∀ u g v, e u (TypedMixedSeparatedHom.localF (M := M) a u g v) =
    TypedMixedSeparatedHom.localF (M := M') a' u g (e u v))
  (hf : ∀ u g w, f u (TypedMixedSeparatedHom.localB (N := N) b u g w) =
    TypedMixedSeparatedHom.localB (N := N') b' u g (f u w))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

@[reducible] local instance (u : P) : AddCommGroup (L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K u ⊗[ℂ] N u) := inferInstance
@[reducible] local instance (u : P) : AddCommGroup (L' u ⊗[ℂ] M' u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K' u ⊗[ℂ] N' u) := inferInstance
@[reducible] local instance : AddCommGroup (TypedMixedSeparatedHom.Carrier a b c d p s) := inferInstance
@[reducible] local instance : AddCommGroup (TypedMixedSeparatedHom.Carrier a' b' c' d' p s) := inferInstance

abbrev rawEquiv := TypedMixedLocalTransport.carrierEquiv
  (TypedMixedSeparatedHom.localF (M := M) a) (TypedMixedSeparatedHom.localB (N := N) b)
  (TypedMixedSeparatedHom.residualF (L := L) c) (TypedMixedSeparatedHom.residualB (K := K) d)
  (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d)
  (TypedMixedSeparatedHom.localF (M := M') a') (TypedMixedSeparatedHom.localB (N := N') b')
  (TypedMixedSeparatedHom.residualF (L := L') c') (TypedMixedSeparatedHom.residualB (K := K') d')
  (TypedMixedSeparatedHom.commutesF a' c') (TypedMixedSeparatedHom.commutesB b' d')
  e f he hf p s

def carrierEquiv : Representation.Equiv (TypedMixedSeparatedHom.residual a b c d p s)
    (TypedMixedSeparatedHom.residual a' b' c' d' p s) :=
  (TypedMixedCarrierNaturality.carrierEquiv a b c d p s).symm.trans
    ((rawEquiv a b c d a' b' c' d' e f he hf p s).trans
      (TypedMixedCarrierNaturality.carrierEquiv a' b' c' d' p s))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem carrierEquiv_separate (u) :
    carrierEquiv a b c d a' b' c' d' e f he hf p s
      (TypedMixedCarrierNaturality.carrierEquiv a b c d p s u) =
    TypedMixedCarrierNaturality.carrierEquiv a' b' c' d' p s
      (rawEquiv a b c d a' b' c' d' e f he hf p s u) := by
  change TypedMixedCarrierNaturality.carrierEquiv a' b' c' d' p s
    (rawEquiv a b c d a' b' c' d' e f he hf p s
    ((TypedMixedCarrierNaturality.carrierEquiv a b c d p s).symm
      (TypedMixedCarrierNaturality.carrierEquiv a b c d p s u))) = _
  rw [Representation.Equiv.symm_apply_apply]

abbrev inputPull := TypedMixedLocalTransport.pull
  (TypedMixedSeparatedHom.localF (M := M) a) (TypedMixedSeparatedHom.localB (N := N) b)
  (TypedMixedSeparatedHom.residualF (L := L) c) (TypedMixedSeparatedHom.residualB (K := K) d)
  (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d)
  (TypedMixedSeparatedHom.localF (M := M') a') (TypedMixedSeparatedHom.localB (N := N') b')
  (TypedMixedSeparatedHom.residualF (L := L') c') (TypedMixedSeparatedHom.residualB (K := K') d')
  (TypedMixedSeparatedHom.commutesF a' c') (TypedMixedSeparatedHom.commutesB b' d')
  e f he hf p s

def homEquiv : IntertwiningMap (TypedMixedSeparatedHom.residual a' b' c' d' p s)
    (trivial ℂ H ℂ) ≃ₗ[ℂ]
    IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s) (trivial ℂ H ℂ) where
  toFun q := q.comp (carrierEquiv a b c d a' b' c' d' e f he hf p s).toIntertwiningMap
  invFun q := q.comp (carrierEquiv a b c d a' b' c' d' e f he hf p s).symm.toIntertwiningMap
  left_inv q := by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro u
    exact congrArg q ((carrierEquiv a b c d a' b' c' d' e f he hf p s).apply_symm_apply u)
  right_inv q := by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro u
    exact congrArg q ((carrierEquiv a b c d a' b' c' d' e f he hf p s).symm_apply_apply u)
  map_add' _ _ := by ext u; rfl
  map_smul' _ _ := by ext u; rfl

omit [Fintype P] [Fintype Q] in
theorem inputPull_apply (q : MixedPatternAssembly.orderedSpace
    (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d') p s)
    (v : ∀ i, L (p i) ⊗[ℂ] M (p i)) (w : ∀ j, K (s j) ⊗[ℂ] N (s j)) :
    (inputPull a b c d a' b' c' d' e f he hf p s q).val v w =
      q.val (fun i => e (p i) (v i)) (fun j => f (s j) (w j)) :=
  TypedMixedLocalTransport.pull_apply _ _ _ _ _ _ _ _ _ _ _ _ e f he hf p s q v w

omit [Fintype P] [Fintype Q] in
theorem extraction (q : MixedPatternAssembly.orderedSpace
    (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d') p s) :
    TypedMixedSeparatedHom.equiv a b c d p s
      (inputPull a b c d a' b' c' d' e f he hf p s q) =
    homEquiv a b c d a' b' c' d' e f he hf p s
      (TypedMixedSeparatedHom.equiv a' b' c' d' p s q) := by
  have h1 := TypedMixedCarrierNaturality.extraction a b c d p s
    (inputPull a b c d a' b' c' d' e f he hf p s q)
  have h2 := TypedMixedLocalTransport.extraction
    (TypedMixedSeparatedHom.localF (M := M) a) (TypedMixedSeparatedHom.localB (N := N) b)
    (TypedMixedSeparatedHom.residualF (L := L) c) (TypedMixedSeparatedHom.residualB (K := K) d)
    (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d)
    (TypedMixedSeparatedHom.localF (M := M') a') (TypedMixedSeparatedHom.localB (N := N') b')
    (TypedMixedSeparatedHom.residualF (L := L') c') (TypedMixedSeparatedHom.residualB (K := K') d')
    (TypedMixedSeparatedHom.commutesF a' c') (TypedMixedSeparatedHom.commutesB b' d')
    e f he hf p s q
  have h3 := TypedMixedCarrierNaturality.extraction a' b' c' d' p s q
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have h1u := congrArg (fun z : IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s)
    (trivial ℂ H ℂ) => z u) h1
  have h2u := congrArg (fun z : IntertwiningMap (TypedMixedCarrierNaturality.raw a b c d p s)
    (trivial ℂ H ℂ) => z ((TypedMixedCarrierNaturality.carrierEquiv a b c d p s).symm u)) h2
  have h3u := congrArg (fun z : IntertwiningMap (TypedMixedSeparatedHom.residual a' b' c' d' p s)
    (trivial ℂ H ℂ) => z (carrierEquiv a b c d a' b' c' d' e f he hf p s u)) h3
  exact (h1u.trans h2u).trans (by
    change _ = TypedMixedSeparatedHom.equiv a' b' c' d' p s q
      (carrierEquiv a b c d a' b' c' d' e f he hf p s u)
    rw [h3u]
    change _ = TypedMixedLocalHom.equiv _ _ _ _ _ _ p s q
      ((TypedMixedCarrierNaturality.carrierEquiv a' b' c' d' p s).symm
        (TypedMixedCarrierNaturality.carrierEquiv a' b' c' d' p s _))
    rw [Representation.Equiv.symm_apply_apply]
    rfl)

omit [Fintype P] [Fintype Q] in
theorem homEquiv_id (q : IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s)
    (trivial ℂ H ℂ)) :
    homEquiv a b c d a b c d (fun u => Representation.Equiv.refl
      (TypedMixedSeparatedHom.residualF (L := L) c u))
      (fun u => Representation.Equiv.refl (TypedMixedSeparatedHom.residualB (K := K) d u))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) p s q = q := by
  obtain ⟨q,rfl⟩ := (TypedMixedSeparatedHom.equiv a b c d p s).surjective q
  have h := extraction a b c d a b c d
    (fun u => Representation.Equiv.refl (TypedMixedSeparatedHom.residualF (L := L) c u))
    (fun u => Representation.Equiv.refl (TypedMixedSeparatedHom.residualB (K := K) d u))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) p s q
  have hi : inputPull a b c d a b c d
      (fun u => Representation.Equiv.refl (TypedMixedSeparatedHom.residualF (L := L) c u))
      (fun u => Representation.Equiv.refl (TypedMixedSeparatedHom.residualB (K := K) d u))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) p s q = q :=
    TypedMixedLocalTransport.pull_id _ _ _ _ _ _ p s q
  exact h.symm.trans (congrArg (TypedMixedSeparatedHom.equiv a b c d p s) hi)
end
end Math.TypedMixedSeparatedTransport

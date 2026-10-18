import Math.RepresentationTheory.TypedMixedLocalHomNaturality
import Math.RepresentationTheory.TypedMixedExchangeNaturality
import Math.RepresentationTheory.LocalRelationNaturality

/-! Direct carrier transport for ordered mixed fields with commuting actions.
The input constraint conversion does not use coefficient completeness. -/
namespace Math.TypedMixedLocalTransport
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {V V' : P → Type*} {W W' : Q → Type*}
  [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  [∀ u, AddCommGroup (V' u)] [∀ u, Module ℂ (V' u)]
  [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  [∀ u, AddCommGroup (W' u)] [∀ u, Module ℂ (W' u)]
  (a : ∀ u, Representation ℂ G (V u)) (b : ∀ u, Representation ℂ G (W u))
  (c : ∀ u, Representation ℂ H (V u)) (d : ∀ u, Representation ℂ H (W u))
  (ha : ∀ u g h v, a u g (c u h v) = c u h (a u g v))
  (hb : ∀ u g h w, b u g (d u h w) = d u h (b u g w))
  (a' : ∀ u, Representation ℂ G (V' u)) (b' : ∀ u, Representation ℂ G (W' u))
  (c' : ∀ u, Representation ℂ H (V' u)) (d' : ∀ u, Representation ℂ H (W' u))
  (ha' : ∀ u g h v, a' u g (c' u h v) = c' u h (a' u g v))
  (hb' : ∀ u g h w, b' u g (d' u h w) = d' u h (b' u g w))
  (e : ∀ u, Representation.Equiv (c u) (c' u))
  (f : ∀ u, Representation.Equiv (d u) (d' u))
  (he : ∀ u g v, e u (a u g v) = a' u g (e u v))
  (hf : ∀ u g w, f u (b u g w) = b' u g (f u w))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
include he hf in
theorem local_compatible (g : G) (u : TypedMixedExchangeQuotient.Domain (V := V) (W := W) p s) :
    TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f
      (TypedMixedExchangeQuotient.action a b p s g u) =
    TypedMixedExchangeQuotient.action a' b' p s g
      (TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f u) := by
  have hlin : (TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f).toLinearMap.comp
      (TypedMixedExchangeQuotient.action a b p s g) =
      (TypedMixedExchangeQuotient.action a' b' p s g).comp
        (TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f).toLinearMap := by
    apply TypedMixedTensorHom.pure_ext
    intro v w
    change TensorProduct.map (PiTensorProduct.map (fun i => (e (p i)).toLinearMap))
        (PiTensorProduct.map (fun j => (f (s j)).toLinearMap))
        (TypedMixedExchangeQuotient.action a b p s g
          ((PiTensorProduct.tprod ℂ) v ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) w)) =
      TypedMixedExchangeQuotient.action a' b' p s g
        (TensorProduct.map (PiTensorProduct.map (fun i => (e (p i)).toLinearMap))
          (PiTensorProduct.map (fun j => (f (s j)).toLinearMap))
          ((PiTensorProduct.tprod ℂ) v ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) w))
    simp only [TypedMixedExchangeQuotient.action, Representation.tprod_apply,
      PiTensorProduct.map_tprod,
      TensorProduct.map_tmul, MultilinearInvariantHom.tensorRepresentation_tprod]
    congr 1
    · congr 1; funext i; exact he (p i) g (v i)
    · congr 1; funext i; exact hf (s i) g (w i)
  exact LinearMap.congr_fun hlin u

def carrierEquiv : Representation.Equiv (TypedMixedLocalHom.residual a b c d ha hb p s)
    (TypedMixedLocalHom.residual a' b' c' d' ha' hb' p s) :=
  LocalRelationNaturality.quotientEquiv
    (TypedMixedExchangeQuotient.action a b p s) (TypedMixedExchangeQuotient.action c d p s)
    (TypedMixedLocalHom.commutes a b c d ha hb p s)
    (TypedMixedExchangeQuotient.relations p s) (TypedMixedExchangeQuotient.stable c d p s)
    (TypedMixedExchangeQuotient.action a' b' p s) (TypedMixedExchangeQuotient.action c' d' p s)
    (TypedMixedLocalHom.commutes a' b' c' d' ha' hb' p s)
    (TypedMixedExchangeQuotient.relations p s) (TypedMixedExchangeQuotient.stable c' d' p s)
    (TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f)
    (local_compatible a b c d a' b' c' d' e f he hf p s)
    (TypedMixedExchangeNaturality.relations_map_equiv p s c d c' d' e f)

def rawPull : LocalRelationHom.Input (TypedMixedExchangeQuotient.action a' b' p s)
    (TypedMixedExchangeQuotient.action c' d' p s) (trivial ℂ H ℂ)
    (TypedMixedExchangeQuotient.relations p s) →ₗ[ℂ]
    LocalRelationHom.Input (TypedMixedExchangeQuotient.action a b p s)
      (TypedMixedExchangeQuotient.action c d p s) (trivial ℂ H ℂ)
      (TypedMixedExchangeQuotient.relations p s) :=
  LocalRelationNaturality.pull _ _ _ _ _ _
    (TypedMixedExchangeNaturality.intertwiner p s c d c' d'
      (fun u => (e u).toIntertwiningMap) (fun u => (f u).toIntertwiningMap))
    (local_compatible a b c d a' b' c' d' e f he hf p s)
    (TypedMixedExchangeNaturality.map_relations (fun u => (e u).toLinearMap)
      (fun u => (f u).toLinearMap) p s)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem carrierEquiv_mk (u : TypedMixedExchangeQuotient.Domain (V := V) (W := W) p s) :
    carrierEquiv a b c d ha hb a' b' c' d' ha' hb' e f he hf p s
      ((LocalRelationHom.image (TypedMixedExchangeQuotient.action a b p s)
        (TypedMixedExchangeQuotient.relations p s)).mkQ
        ((LocalCoinvariantHom.relations (TypedMixedExchangeQuotient.action a b p s)).mkQ u)) =
    (LocalRelationHom.image (TypedMixedExchangeQuotient.action a' b' p s)
      (TypedMixedExchangeQuotient.relations p s)).mkQ
      ((LocalCoinvariantHom.relations (TypedMixedExchangeQuotient.action a' b' p s)).mkQ
        (TypedMixedExchangeNaturality.tensorEquiv p s c d c' d' e f u)) := rfl

def pull : MixedPatternAssembly.orderedSpace (TypedMixedLocalHom.fermion a' c' ha')
    (TypedMixedLocalHom.boson b' d' hb') p s →ₗ[ℂ]
    MixedPatternAssembly.orderedSpace (TypedMixedLocalHom.fermion a c ha)
      (TypedMixedLocalHom.boson b d hb) p s :=
  (TypedMixedLocalHom.inputEquiv a b c d ha hb p s).symm.toLinearMap.comp
    ((rawPull a b c d a' b' c' d' e f he hf p s).comp
      (TypedMixedLocalHom.inputEquiv a' b' c' d' ha' hb' p s).toLinearMap)

omit [Fintype P] [Fintype Q] in
theorem pull_apply (q : MixedPatternAssembly.orderedSpace
    (TypedMixedLocalHom.fermion a' c' ha') (TypedMixedLocalHom.boson b' d' hb') p s)
    (v : ∀ i, V (p i)) (w : ∀ j, W (s j)) :
    (pull a b c d ha hb a' b' c' d' ha' hb' e f he hf p s q).val v w =
    q.val (fun i => e (p i) (v i)) (fun j => f (s j) (w j)) := by
  have h := congrArg
    (fun z : LocalRelationHom.Input (TypedMixedExchangeQuotient.action a b p s)
      (TypedMixedExchangeQuotient.action c d p s) (trivial ℂ H ℂ)
      (TypedMixedExchangeQuotient.relations p s) =>
      z.val.val ((PiTensorProduct.tprod ℂ) v ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) w))
    ((TypedMixedLocalHom.inputEquiv a b c d ha hb p s).apply_symm_apply
      (rawPull a b c d a' b' c' d' e f he hf p s
        (TypedMixedLocalHom.inputEquiv a' b' c' d' ha' hb' p s q)))
  change (TypedMixedLocalHom.inputEquiv a b c d ha hb p s
    (pull a b c d ha hb a' b' c' d' ha' hb' e f he hf p s q)).val.val _ = _ at h
  rw [TypedMixedLocalHom.inputEquiv_apply] at h
  change TypedMixedTensorHom.orderedEquiv.symm
    (pull a b c d ha hb a' b' c' d' ha' hb' e f he hf p s q).val
      ((PiTensorProduct.tprod ℂ) v ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) w) =
    (TypedMixedLocalHom.inputEquiv a' b' c' d' ha' hb' p s q).val.val
      (TypedMixedExchangeNaturality.tensorMap (fun u => (e u).toLinearMap)
        (fun u => (f u).toLinearMap) p s
        ((PiTensorProduct.tprod ℂ) v ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) w)) at h
  rw [TypedMixedLocalHom.inputEquiv_apply] at h
  simp only [TypedMixedExchangeNaturality.tensorMap, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod, TypedMixedTensorHom.lift_apply] at h
  exact h

omit [Fintype P] [Fintype Q] in
theorem extraction (q : MixedPatternAssembly.orderedSpace
    (TypedMixedLocalHom.fermion a' c' ha') (TypedMixedLocalHom.boson b' d' hb') p s) :
    TypedMixedLocalHom.equiv a b c d ha hb p s
      (pull a b c d ha hb a' b' c' d' ha' hb' e f he hf p s q) =
    (TypedMixedLocalHom.equiv a' b' c' d' ha' hb' p s q).comp
      (carrierEquiv a b c d ha hb a' b' c' d' ha' hb' e f he hf p s).toIntertwiningMap := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalRelationHom.image (TypedMixedExchangeQuotient.action a b p s)
    (TypedMixedExchangeQuotient.relations p s)).mkQ_surjective u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations
    (TypedMixedExchangeQuotient.action a b p s)).mkQ_surjective u
  change LocalRelationHom.equiv _ _ _ _ _ _
    ((TypedMixedLocalHom.inputEquiv a b c d ha hb p s)
      ((TypedMixedLocalHom.inputEquiv a b c d ha hb p s).symm _)) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Fintype P] [Fintype Q] in
theorem pull_id (q : MixedPatternAssembly.orderedSpace
    (TypedMixedLocalHom.fermion a c ha) (TypedMixedLocalHom.boson b d hb) p s) :
    pull a b c d ha hb a b c d ha hb (fun u => Representation.Equiv.refl (c u))
      (fun u => Representation.Equiv.refl (d u)) (fun _ _ _ => rfl) (fun _ _ _ => rfl) p s q = q := by
  apply Subtype.ext
  ext v w
  exact pull_apply a b c d ha hb a b c d ha hb
    (fun u => Representation.Equiv.refl (c u)) (fun u => Representation.Equiv.refl (d u))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) p s q v w

section Composition
variable {V'' : P → Type*} {W'' : Q → Type*}
  [∀ u, AddCommGroup (V'' u)] [∀ u, Module ℂ (V'' u)]
  [∀ u, AddCommGroup (W'' u)] [∀ u, Module ℂ (W'' u)]
  (a'' : ∀ u, Representation ℂ G (V'' u)) (b'' : ∀ u, Representation ℂ G (W'' u))
  (c'' : ∀ u, Representation ℂ H (V'' u)) (d'' : ∀ u, Representation ℂ H (W'' u))
  (ha'' : ∀ u g h v, a'' u g (c'' u h v) = c'' u h (a'' u g v))
  (hb'' : ∀ u g h w, b'' u g (d'' u h w) = d'' u h (b'' u g w))
  (e' : ∀ u, Representation.Equiv (c' u) (c'' u))
  (f' : ∀ u, Representation.Equiv (d' u) (d'' u))
  (he' : ∀ u g v, e' u (a' u g v) = a'' u g (e' u v))
  (hf' : ∀ u g w, f' u (b' u g w) = b'' u g (f' u w))

omit [Fintype P] [Fintype Q] in
theorem pull_comp (q : MixedPatternAssembly.orderedSpace
    (TypedMixedLocalHom.fermion a'' c'' ha'') (TypedMixedLocalHom.boson b'' d'' hb'') p s) :
    pull a b c d ha hb a' b' c' d' ha' hb' e f he hf p s
      (pull a' b' c' d' ha' hb' a'' b'' c'' d'' ha'' hb'' e' f' he' hf' p s q) =
    pull a b c d ha hb a'' b'' c'' d'' ha'' hb''
      (fun u => (e u).trans (e' u)) (fun u => (f u).trans (f' u))
      (fun u g v => (congrArg (e' u) (he u g v)).trans (he' u g (e u v)))
      (fun u g w => (congrArg (f' u) (hf u g w)).trans (hf' u g (f u w))) p s q := by
  apply Subtype.ext
  ext v w
  rw [pull_apply, pull_apply]
  exact (pull_apply a b c d ha hb a'' b'' c'' d'' ha'' hb''
    (fun u => (e u).trans (e' u)) (fun u => (f u).trans (f' u))
    (fun u g v => (congrArg (e' u) (he u g v)).trans (he' u g (e u v)))
    (fun u g w => (congrArg (f' u) (hf u g w)).trans (hf' u g (f u w))) p s q v w).symm

omit [Fintype P] [Fintype Q] in
theorem hom_comp (q : IntertwiningMap
    (TypedMixedLocalHom.residual a'' b'' c'' d'' ha'' hb'' p s) (trivial ℂ H ℂ)) :
    (q.comp (carrierEquiv a' b' c' d' ha' hb' a'' b'' c'' d'' ha'' hb''
      e' f' he' hf' p s).toIntertwiningMap).comp
      (carrierEquiv a b c d ha hb a' b' c' d' ha' hb' e f he hf p s).toIntertwiningMap =
    q.comp (carrierEquiv a b c d ha hb a'' b'' c'' d'' ha'' hb''
      (fun u => (e u).trans (e' u)) (fun u => (f u).trans (f' u))
      (fun u g v => (congrArg (e' u) (he u g v)).trans (he' u g (e u v)))
      (fun u g w => (congrArg (f' u) (hf u g w)).trans (hf' u g (f u w))) p s).toIntertwiningMap := by
  obtain ⟨q,rfl⟩ := (TypedMixedLocalHom.equiv a'' b'' c'' d'' ha'' hb'' p s).surjective q
  have hA := extraction a b c d ha hb a' b' c' d' ha' hb' e f he hf p s
    (pull a' b' c' d' ha' hb' a'' b'' c'' d'' ha'' hb'' e' f' he' hf' p s q)
  have hB := extraction a' b' c' d' ha' hb' a'' b'' c'' d'' ha'' hb''
    e' f' he' hf' p s q
  have hC := extraction a b c d ha hb a'' b'' c'' d'' ha'' hb''
    (fun u => (e u).trans (e' u)) (fun u => (f u).trans (f' u))
    (fun u g v => (congrArg (e' u) (he u g v)).trans (he' u g (e u v)))
    (fun u g w => (congrArg (f' u) (hf u g w)).trans (hf' u g (f u w))) p s q
  have h := congrArg (fun z : IntertwiningMap
    (TypedMixedLocalHom.residual a' b' c' d' ha' hb' p s) (trivial ℂ H ℂ) =>
    z.comp (carrierEquiv a b c d ha hb a' b' c' d' ha' hb' e f he hf p s).toIntertwiningMap) hB
  exact (h.symm.trans hA.symm).trans
    ((congrArg (TypedMixedLocalHom.equiv a b c d ha hb p s)
      (pull_comp a b c d ha hb a' b' c' d' ha' hb' e f he hf p s
        a'' b'' c'' d'' ha'' hb'' e' f' he' hf' q)).trans hC)
end Composition
end
end Math.TypedMixedLocalTransport

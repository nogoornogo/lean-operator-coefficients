import Math.RepresentationTheory.SymmetricDualTensorSwap
import Math.RepresentationTheory.TensorVolumeSplit

/-! Source certificates for the two local color exclusion rules. All claims
refer to the actual raw embedding of an equivariant retraction. -/
namespace Math.SymmetricVertexCertificate
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

variable {G V A B : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] (rho : Representation ℂ G V)

abbrev raw (p q : ℕ) := (rho.tensorPower p).tprod (rho.dual.tensorPower q)

def cast {p q a b : ℕ} (hp : p = a) (hq : q = b) : Representation.Equiv
    (raw rho p q) (raw rho a b) :=
  tensorEquiv (TensorVolumeSplit.powerCast rho hp) (TensorVolumeSplit.powerCast rho.dual hq)

theorem cast_refl (p q : ℕ) (x : SymmetricTensorTrace.Raw (V := V) p q) :
    cast rho (rfl : p=p) (rfl : q=q) x = x := by
  change TensorProduct.map (_root_.TensorPower.cast ℂ V rfl).toLinearMap
    (_root_.TensorPower.cast ℂ (Module.Dual ℂ V) rfl).toLinearMap x = x
  simp only [_root_.TensorPower.cast_refl,LinearEquiv.refl_toLinearMap,
    TensorProduct.map_id,LinearMap.id_apply]

theorem cast_inverse {p q a b : ℕ} (hp : p=a) (hq : q=b)
    (x : SymmetricTensorTrace.Raw (V := V) p q) :
    cast rho hp.symm hq.symm (cast rho hp hq x) = x := by
  subst a
  subst b
  rw [cast_refl,cast_refl]

theorem cast_trans {p q a b c d : ℕ} (hp : p=a) (hq : q=b) (ha : a=c) (hb : b=d)
    (x : SymmetricTensorTrace.Raw (V := V) p q) :
    cast rho ha hb (cast rho hp hq x) = cast rho (hp.trans ha) (hq.trans hb) x := by
  subst a
  subst b
  subst c
  subst d
  simp only [cast_refl]

theorem cast_symmetric {p q a b : ℕ} (hp : p=a) (hq : q=b)
    (y : SymmetricTensorTrace.Symmetric (V := V) p q) :
    ∃ z, SymmetricTensorTrace.inclusion rho a b z =
      cast rho hp hq (SymmetricTensorTrace.inclusion rho p q y) := by
  subst a
  subst b
  exact ⟨y,(cast_refl rho p q _).symm⟩

def Symmetric {p q : ℕ} {a : Representation ℂ G A} (S : Split (raw rho p q) a) : Prop :=
  ∀ x, ∃ y, SymmetricTensorTrace.inclusion rho p q y = S.embed x

def Traceless {p q : ℕ} {a : Representation ℂ G A} (S : Split (raw rho p q) a) : Prop :=
  ∀ (c d : ℕ) (hp : p=1+c) (hq : q=1+d) x,
    SymmetricTensorTrace.rawTrace c d (cast rho hp hq (S.embed x)) = 0

theorem annihilate {p q c d : ℕ} {a : Representation ℂ G A}
    (S : Split (raw rho p q) a) (hs : Symmetric rho S) (ht : Traceless rho S)
    (hp : p=1+c) (hq : q=1+d)
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (F : SymmetricTensorTrace.Raw (V := V) (1+c) (1+d) →ₗ[ℂ] N)
    (H : SymmetricTensorTrace.Raw (V := V) c d →ₗ[ℂ] N)
    (hf : F.comp (SymmetricTensorTrace.inclusion rho (1+c) (1+d)) =
      (H.comp (SymmetricTensorTrace.rawTrace c d)).comp
        (SymmetricTensorTrace.inclusion rho (1+c) (1+d))) (x : A) :
    F (cast rho hp hq (S.embed x)) = 0 := by
  obtain ⟨y,hy⟩ := hs x
  obtain ⟨z,hz⟩ := cast_symmetric rho hp hq y
  rw [hy] at hz
  have he := LinearMap.congr_fun hf z
  change F (SymmetricTensorTrace.inclusion rho (1+c) (1+d) z) =
    H (SymmetricTensorTrace.rawTrace c d (SymmetricTensorTrace.inclusion rho (1+c) (1+d) z)) at he
  rw [hz,ht c d hp hq x,map_zero] at he
  exact he

theorem symmetric_transport {p q : ℕ} {a : Representation ℂ G A} {b : Representation ℂ G B}
    (S : Split (raw rho p q) a) (e : Representation.Equiv a b) (h : Symmetric rho S) :
    Symmetric rho (S.trans (Split.ofEquiv e)) := fun x => h (e.symm x)

theorem traceless_transport {p q : ℕ} {a : Representation ℂ G A} {b : Representation ℂ G B}
    (S : Split (raw rho p q) a) (e : Representation.Equiv a b) (h : Traceless rho S) :
    Traceless rho (S.trans (Split.ofEquiv e)) := fun c d hp hq x => h c d hp hq (e.symm x)

variable [FiniteDimensional ℂ V]

def swapped {p q : ℕ} {a : Representation ℂ G A}
    (S : Split ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q)) a) :
    Split (raw rho q p) a :=
  (Split.ofEquiv (DualMixedTensorSwap.equivalence rho p q).symm).trans S

theorem symmetric_swapped {p q : ℕ} {a : Representation ℂ G A}
    (S : Split ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q)) a)
    (h : Symmetric rho.dual S) : Symmetric rho (swapped rho S) := by
  intro x
  obtain ⟨y,hy⟩ := h x
  refine ⟨SymmetricDualTensorSwap.equivalence rho p q y,?_⟩
  have he := LinearMap.congr_fun (SymmetricDualTensorSwap.inclusion rho p q) y
  change SymmetricTensorTrace.inclusion rho q p (SymmetricDualTensorSwap.equivalence rho p q y) =
    DualMixedTensorSwap.equivalence rho p q (SymmetricTensorTrace.inclusion rho.dual p q y) at he
  exact he.trans (congrArg (DualMixedTensorSwap.equivalence rho p q) hy)

theorem traceless_swapped {p q : ℕ} {a : Representation ℂ G A}
    (S : Split ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q)) a)
    (hs : Symmetric rho.dual S) (ht : Traceless rho.dual S) :
    Traceless rho (swapped rho S) := by
  intro c d hp hq x
  subst p
  subst q
  have hz := ht d c rfl rfl x
  rw [cast_refl] at hz ⊢
  obtain ⟨y,hy⟩ := hs x
  have he := LinearMap.congr_fun (SymmetricDualTensorSwap.trace rho d c) y
  change SymmetricTensorTrace.rawTrace c d
      (DualMixedTensorSwap.equivalence rho (1+d) (1+c)
        (SymmetricTensorTrace.inclusion rho.dual (1+d) (1+c) y)) =
    DualMixedTensorSwap.equivalence rho d c
      (SymmetricTensorTrace.rawTrace d c (SymmetricTensorTrace.inclusion rho.dual (1+d) (1+c) y)) at he
  rw [hy,hz,map_zero] at he
  exact he

end
end Math.SymmetricVertexCertificate

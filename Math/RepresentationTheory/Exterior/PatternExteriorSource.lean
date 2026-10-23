import Math.RepresentationTheory.Invariants.MultilinearInvariantHom
import Math.RepresentationTheory.Exterior.TypedPatternAlternation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! A fixed species content as an actual subrepresentation of the exterior
source. The ordered tensor maps onto this statistical image. -/
namespace Math.PatternExteriorSource
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) {n : ℕ} (p : Fin n → S)

abbrev Raw := MultilinearInvariantHom.tensorRepresentation (fun i => r (p i))
abbrev Full := (FiniteSpeciesExterior.representation r).exteriorPower n

omit [Fintype S] in
theorem orbit_iff_counts (labels : Fin n → S) :
    (∃ e : Equiv.Perm (Fin n), labels ∘ e = p) ↔
      ∀ s, (Finset.univ.filter (fun i => labels i = s)).card =
        (Finset.univ.filter (fun i => p i = s)).card := by
  constructor
  · rintro ⟨e,he⟩ s
    let es : {i // p i = s} ≃ {i // labels i = s} := e.subtypeEquiv
      (by intro i; have hi : labels (e i) = p i := congrFun he i; rw [hi])
    simpa only [Fintype.card_subtype] using (Fintype.card_congr es).symm
  · exact FiniteSpeciesExterior.permutation_of_counts _ p

def wedge : MultilinearMap ℂ (fun i => V (p i)) (⋀[ℂ]^n (∀ s, V s)) :=
  (exteriorPower.ιMulti ℂ n).toMultilinearMap.compLinearMap
    (fun i => LinearMap.single ℂ V (p i))

def map : IntertwiningMap (Raw r p) (Full r (n := n)) where
  toLinearMap := PiTensorProduct.lift (wedge p)
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      MultilinearInvariantHom.tensorRepresentation_tprod, PiTensorProduct.lift.tprod]
    change exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (r (p i) g (v i))) =
      (Full r) g (exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)))
    rw [Representation.exteriorPower_apply_ιMulti]
    apply congrArg (exteriorPower.ιMulti ℂ n)
    funext i
    exact (FiniteSpeciesExterior.action_single r g (p i) (v i)).symm

abbrev Source := (map r p).range.toSubmodule
@[reducible] instance : AddCommGroup (Source r p) := (Source r p).addCommGroup
abbrev representation := (map r p).range.toRepresentation

def onto : IntertwiningMap (Raw r p) (representation r p) where
  toLinearMap := (map r p).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (map r p).isIntertwining _ _ g x

theorem onto_surjective : Function.Surjective (onto r p) := by
  rintro ⟨x,y,hy⟩
  exact ⟨y, Subtype.ext hy⟩

theorem source_scalar (g : G) (c : ℂ) (he : Raw r p g = c • LinearMap.id)
    (x : Source r p) : representation r p g x = c • x := by
  obtain ⟨y,rfl⟩ := onto_surjective r p x
  calc
    _ = onto r p (Raw r p g y) := ((onto r p).isIntertwining _ _ g y).symm
    _ = onto r p (c • y) := by rw [he]; rfl
    _ = _ := (onto r p).map_smul c y

def inclusion : IntertwiningMap (representation r p) (Full r (n := n)) where
  toLinearMap := (Source r p).subtype
  isIntertwining' _ := rfl

@[simp] theorem onto_tprod (v : ∀ i, V (p i)) :
    (onto r p (PiTensorProduct.tprod ℂ v)).val =
      exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)) :=
  PiTensorProduct.lift.tprod _

def pure : MultilinearMap ℂ (fun i => V (p i)) (Source r p) :=
  (onto r p).toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ)

@[simp] theorem pure_val (v : ∀ i, V (p i)) :
    (pure r p v).val = exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)) :=
  onto_tprod r p v

theorem pure_compatible : TypedPatternAlternation.Compatible (V := V) p (pure r p) := by
  intro e he v
  apply Subtype.ext
  simp only [TypedPatternAlternation.ordered, MultilinearMap.compLinearMap_apply,
    LinearMap.proj_apply, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
    Submodule.coe_smul, pure_val, Function.comp_apply]
  have hp (i : Fin n) : p (e i) = p i := congrFun he i
  have hv : (fun i => Pi.single (p i) (v i (p i))) ∘ e =
      fun i => Pi.single (p i) (v (e i) (p i)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [hp i]
  have hh := ((exteriorPower.ιMulti ℂ n).map_congr_perm
    (fun i => Pi.single (p i) (v i (p i))) e).symm
  rw [hv] at hh
  simpa only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ] using hh

def projectionLinear : (⋀[ℂ]^n (∀ s, V s)) →ₗ[ℂ] Source r p :=
  exteriorPower.alternatingMapLinearEquiv
    (TypedPatternAlternation.alternating (V := V) p (pure r p))

@[simp] theorem projection_pure (v : ∀ i, V (p i)) :
    projectionLinear r p (exteriorPower.ιMulti ℂ n
      (fun i => Pi.single (p i) (v i))) = pure r p v := by
  rw [projectionLinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact TypedPatternAlternation.alternating_pure p _ (pure_compatible r p) v

theorem projection_vanish (labels : Fin n → S) (v : ∀ i, V (labels i))
    (h : ¬ ∃ e : Equiv.Perm (Fin n), labels ∘ e = p) :
    projectionLinear r p (exteriorPower.ιMulti ℂ n
      (fun i => Pi.single (labels i) (v i))) = 0 := by
  rw [projectionLinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact TypedPatternAlternation.alternating_vanish p _ labels v h

theorem projection_inclusion (x : Source r p) : projectionLinear r p x.val = x := by
  obtain ⟨y,rfl⟩ := onto_surjective r p x
  have he : (projectionLinear r p).comp (map r p).toLinearMap = (onto r p).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      map, PiTensorProduct.lift.tprod]
    exact projection_pure r p v
  exact DFunLike.congr_fun he y

theorem pure_action (g : G) (v : ∀ i, V (p i)) :
    pure r p (fun i => r (p i) g (v i)) = (representation r p) g (pure r p v) := by
  have he := (onto r p).isIntertwining _ _ g (PiTensorProduct.tprod ℂ v)
  rw [MultilinearInvariantHom.tensorRepresentation_tprod] at he
  exact he

def projection : IntertwiningMap (Full r (n := n)) (representation r p) where
  toLinearMap := projectionLinear r p
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti, projectionLinear,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    simp only [TypedPatternAlternation.alternating, AlternatingMap.smul_apply,
      MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      TypedPatternAlternation.ordered, MultilinearMap.compLinearMap_apply,
      LinearMap.proj_apply, Function.comp_apply]
    rw [map_smul, map_sum]
    apply congrArg (_ • ·)
    apply Finset.sum_congr rfl
    intro e _
    simp only [Units.smul_def, map_zsmul]
    apply congrArg ((Equiv.Perm.sign e : ℤ) • ·)
    change pure r p (fun i => r (p i) g (v (e i) (p i))) =
      (representation r p) g (pure r p (fun i => v (e i) (p i)))
    exact pure_action r p g _

end
end Math.PatternExteriorSource

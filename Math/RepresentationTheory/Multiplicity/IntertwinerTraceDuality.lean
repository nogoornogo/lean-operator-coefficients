import Math.RepresentationTheory.Decomposition.SemisimpleSplitting
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Trace

/-! The trace pairing on intertwiner spaces is perfect for an irreducible
constituent of a finite-dimensional semisimple representation. -/

namespace Math.IntertwinerTraceDuality
noncomputable section
open Representation

variable {G V U : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (rho : Representation ℂ G V) (r : Representation ℂ G U)

def pairing : IntertwiningMap rho r →ₗ[ℂ]
    Module.Dual ℂ (IntertwiningMap r rho) where
  toFun f := {
    toFun := fun g => LinearMap.trace ℂ U (f.toLinearMap.comp g.toLinearMap)
    map_add' := by intro g k; simp [LinearMap.comp_add]
    map_smul' := by intro c g; simp [LinearMap.comp_smul] }
  map_add' := by intro f k; ext g; simp [LinearMap.add_comp]
  map_smul' := by intro c f; ext g; simp [LinearMap.smul_comp]

def transpose (f : IntertwiningMap r.dual rho.dual) : IntertwiningMap rho r :=
  (SplitRepresentationProjection.bidualEquiv r).symm.toIntertwiningMap.comp
    ((SplitRepresentationProjection.dualMap f).comp
      (SplitRepresentationProjection.bidualEquiv rho).toIntertwiningMap)

theorem transpose_apply (f : IntertwiningMap r.dual rho.dual)
    (x : V) (phi : Module.Dual ℂ U) : phi (transpose rho r f x) = f phi x := by
  have he := (Module.evalEquiv ℂ U).apply_symm_apply
    ((SplitRepresentationProjection.dualMap f)
      ((SplitRepresentationProjection.bidualEquiv rho) x))
  exact LinearMap.congr_fun he phi

def transposeEquiv : IntertwiningMap r.dual rho.dual ≃ₗ[ℂ] IntertwiningMap rho r where
  toFun := transpose rho r
  invFun := SplitRepresentationProjection.dualMap
  left_inv f := by ext phi x; exact transpose_apply rho r f x phi
  right_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext; intro x
    apply (Module.evalEquiv ℂ U).injective
    apply LinearMap.ext; intro phi
    exact transpose_apply rho r (SplitRepresentationProjection.dualMap f) x phi
  map_add' f g := by
    apply IntertwiningMap.ext
    apply LinearMap.ext; intro x
    apply (Module.evalEquiv ℂ U).injective
    apply LinearMap.ext; intro phi
    change phi (transpose rho r (f + g) x) = phi (transpose rho r f x + transpose rho r g x)
    rw [map_add, transpose_apply, transpose_apply, transpose_apply]
    rfl
  map_smul' c f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext; intro x
    apply (Module.evalEquiv ℂ U).injective
    apply LinearMap.ext; intro phi
    change phi (transpose rho r (c • f) x) = phi (c • transpose rho r f x)
    rw [map_smul, transpose_apply, transpose_apply]
    rfl

omit [FiniteDimensional ℂ V] in
theorem pairing_split (S : SplitRepresentationProjection.Split rho r) :
    pairing rho r S.project S.embed = (Module.finrank ℂ U : ℂ) := by
  have he : S.project.toLinearMap.comp S.embed.toLinearMap = LinearMap.id := by
    ext x
    exact S.left_inv x
  change LinearMap.trace ℂ U (S.project.toLinearMap.comp S.embed.toLinearMap) = _
  rw [he, LinearMap.trace_id]

variable [IsIrreducible r]

omit [FiniteDimensional ℂ V] in
theorem pairing_injective (hs : IsSemisimpleRepresentation rho) :
    Function.Injective (pairing rho r) := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) r.asModule
  let : Nontrivial U := r.asModuleEquiv.toEquiv.symm.nontrivial
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  by_contra hn
  have hsurj := (IsIrreducible.surjective_or_eq_zero f).resolve_right hn
  obtain ⟨S, hS⟩ := SemisimpleSplitting.exists_split rho r hs f hsurj
  have he := pairing_split rho r S
  rw [hS, hf] at he
  change (0 : ℂ) = (Module.finrank ℂ U : ℂ) at he
  have hp : Module.finrank ℂ U ≠ 0 := ne_of_gt Module.finrank_pos
  exact hp (by exact_mod_cast he.symm)

omit [FiniteDimensional ℂ V] in
theorem pairing_flip_injective (hs : IsSemisimpleRepresentation rho) :
    Function.Injective (pairing rho r).flip := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) r.asModule
  let : Nontrivial U := r.asModuleEquiv.toEquiv.symm.nontrivial
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  by_contra hn
  have hinj := (IsIrreducible.injective_or_eq_zero f).resolve_right hn
  obtain ⟨S, hS⟩ := SemisimpleSplitting.exists_retraction rho r hs f hinj
  have he := pairing_split rho r S
  rw [hS] at he
  have hz := LinearMap.congr_fun hf S.project
  change pairing rho r S.project f = 0 at hz
  rw [hz] at he
  have hp : Module.finrank ℂ U ≠ 0 := ne_of_gt Module.finrank_pos
  exact hp (by exact_mod_cast he.symm)

theorem pairing_bijective (hs : IsSemisimpleRepresentation rho) :
    Function.Bijective (pairing rho r) := by
  let := LinearMap.IsPerfPair.of_injective
    (pairing_injective rho r hs) (pairing_flip_injective rho r hs)
  exact LinearMap.IsPerfPair.bijective_left (pairing rho r)

def equiv (hs : IsSemisimpleRepresentation rho) :
    IntertwiningMap rho r ≃ₗ[ℂ] Module.Dual ℂ (IntertwiningMap r rho) :=
  LinearEquiv.ofBijective (pairing rho r) (pairing_bijective rho r hs)

end
end Math.IntertwinerTraceDuality

import Math.LieGroups.SpecialUnitary.SphereLocalProduct
import Math.LieGroups.SpecialUnitary.SpecialUnitaryBase
import Math.Topology.PuncturedSphere
import TauCeti.AlgebraicTopology.Sphere.Puncture

/-! The two explicit section domains are punctured spheres and are contractible.
This identifies the local inputs to induction, not the global gluing step. -/

set_option autoImplicit false
open scoped ContinuousMap

namespace Math.SUN.SphereSection

noncomputable section

theorem denominator_eq_zero_iff {n : ℕ} (v : Sphere (n + 1)) :
    denominator v = 0 ↔ v = antipode (north n) := by
  constructor
  · intro h
    have hv := vector_dot v
    rw [h, star_zero, zero_add] at hv
    have hq : inner ℂ (WithLp.toLp 2 (vector v) : Space (n + 1))
        (WithLp.toLp 2 (vector v)) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      exact hv
    have hz : vector v = 0 := congrArg WithLp.ofLp (inner_self_eq_zero.mp hq)
    apply Subtype.ext
    ext i
    have hi := congrFun hz i
    change pole n i + v.val i = 0 at hi
    have he := eq_neg_of_add_eq_zero_right hi
    simpa [antipode, north, pole, VectorStabilizer.lastVector, Pi.single_apply] using he
  · rintro rfl
    simp [denominator, antipode, north]

theorem patch_eq_compl (n : ℕ) : patch n = {antipode (north n)}ᶜ := by
  ext v
  exact not_congr (denominator_eq_zero_iff v)

theorem southPatch_eq_compl (n : ℕ) : southPatch n = {north n}ᶜ := by
  ext v
  change denominator (antipode v) ≠ 0 ↔ v ≠ north n
  simp only [ne_eq, denominator_eq_zero_iff]
  constructor
  · intro h hv
    exact h (congrArg antipode hv)
  · intro h hv
    apply h
    simpa only [antipode_antipode] using congrArg antipode hv

theorem patch_contractible (n : ℕ) : ContractibleSpace (patch n) := by
  rw [patch_eq_compl]
  exact TauCeti.contractibleSpace_sphere_compl_singleton _

theorem southPatch_contractible (n : ℕ) : ContractibleSpace (southPatch n) := by
  rw [southPatch_eq_compl]
  exact TauCeti.contractibleSpace_sphere_compl_singleton _

def patchProductHomotopyEquiv (n : ℕ) :
    (projection ⁻¹' patch (n + 1)) ≃ₕ Block.Group (n + 1) := by
  let := patch_contractible (n + 1)
  exact (northLocalProduct n).toHomotopyEquiv.trans
    (((ContractibleSpace.hequiv_unit (patch (n + 1))).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl (Block.Group (n + 1)))).trans
        (Homeomorph.uniqueProd Unit (Block.Group (n + 1))).toHomotopyEquiv)

def southProductHomotopyEquiv (n : ℕ) :
    (projection ⁻¹' southPatch (n + 1)) ≃ₕ Block.Group (n + 1) := by
  let := southPatch_contractible (n + 1)
  exact (southLocalProduct n).toHomotopyEquiv.trans
    (((ContractibleSpace.hequiv_unit (southPatch (n + 1))).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl (Block.Group (n + 1)))).trans
        (Homeomorph.uniqueProd Unit (Block.Group (n + 1))).toHomotopyEquiv)

theorem northPreimage_simplyConnected (n : ℕ) [SimplyConnectedSpace (Block.Group (n + 1))] :
    SimplyConnectedSpace (projection ⁻¹' patch (n + 1)) :=
  (patchProductHomotopyEquiv n).simplyConnectedSpace

theorem southPreimage_simplyConnected (n : ℕ) [SimplyConnectedSpace (Block.Group (n + 1))] :
    SimplyConnectedSpace (projection ⁻¹' southPatch (n + 1)) :=
  (southProductHomotopyEquiv n).simplyConnectedSpace

theorem real_finrank_space (n : ℕ) : Module.finrank ℝ (Space n) = 2 * n := by
  simpa [Space] using (Module.finrank_mul_finrank ℝ ℂ (Space n)).symm

theorem overlap_pathConnected (n : ℕ) :
    IsPathConnected (patch (n + 1) ∩ southPatch (n + 1)) := by
  rw [patch_eq_compl, southPatch_eq_compl]
  have hd : 2 < Module.finrank ℝ (Space (n + 2)) := by rw [real_finrank_space]; omega
  have h := Math.PuncturedSphere.isPathConnected_compl_antipodes hd
    (antipode (north (n + 1)))
  have hn : -(antipode (north (n + 1))) = north (n + 1) := by
    apply Subtype.ext
    exact neg_neg _
  rwa [hn] at h

def overlapSection {n : ℕ} (v : ↥(patch (n + 1) ∩ southPatch (n + 1))) : Block.Group (n + 2) :=
  specialSection ⟨v.val, v.property.1⟩

theorem projection_overlapSection {n : ℕ} (v : ↥(patch (n + 1) ∩ southPatch (n + 1))) :
    projection (overlapSection v) = v.val := projection_specialSection _

theorem overlapSection_continuous (n : ℕ) : Continuous (@overlapSection n) :=
  (specialSection_continuous n).comp (continuous_subtype_val.subtype_mk _)

def overlapLocalProduct (n : ℕ) :
    (projection ⁻¹' (patch (n + 1) ∩ southPatch (n + 1))) ≃ₜ
      (↥(patch (n + 1) ∩ southPatch (n + 1)) × Block.Group (n + 1)) :=
  localProduct _ overlapSection projection_overlapSection (overlapSection_continuous n)

theorem overlapPreimage_pathConnected (n : ℕ) [PathConnectedSpace (Block.Group (n + 1))] :
    IsPathConnected (projection ⁻¹' (patch (n + 1) ∩ southPatch (n + 1))) := by
  let := isPathConnected_iff_pathConnectedSpace.mp (overlap_pathConnected n)
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (overlapLocalProduct n).symm.pathConnectedSpace

theorem preimages_union_univ (n : ℕ) :
    (projection ⁻¹' patch (n + 1)) ∪ (projection ⁻¹' southPatch (n + 1)) = Set.univ := by
  ext g
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
  exact patches_cover (projection g)

theorem pathConnected_succ (n : ℕ) [PathConnectedSpace (Block.Group (n + 1))] :
    PathConnectedSpace (Block.Group (n + 2)) := by
  let := patch_contractible (n + 1)
  let := southPatch_contractible (n + 1)
  have hn : IsPathConnected (projection ⁻¹' patch (n + 1)) :=
    isPathConnected_iff_pathConnectedSpace.mpr (northLocalProduct n).symm.pathConnectedSpace
  have hs : IsPathConnected (projection ⁻¹' southPatch (n + 1)) :=
    isPathConnected_iff_pathConnectedSpace.mpr (southLocalProduct n).symm.pathConnectedSpace
  have hi : ((projection ⁻¹' patch (n + 1)) ∩
      (projection ⁻¹' southPatch (n + 1))).Nonempty :=
    (overlapPreimage_pathConnected n).nonempty
  have hu := hn.union hs hi
  rw [preimages_union_univ] at hu
  exact pathConnectedSpace_iff_univ.mpr hu

theorem specialUnitary_pathConnected (n : ℕ) : PathConnectedSpace (Block.Group n) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    induction n with
    | zero =>
      let := Block.rank_one_simplyConnected
      infer_instance
    | succ n ih =>
      let := ih
      exact pathConnected_succ n

end

end Math.SUN.SphereSection

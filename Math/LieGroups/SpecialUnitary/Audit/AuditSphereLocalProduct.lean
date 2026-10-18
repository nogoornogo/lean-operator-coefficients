import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.SphereLocalProduct

/-! Boundary ranks and both charts, including points outside the north patch.
Local products are not a substitute for a simple-connectedness proof. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "Sphere local products import a concrete GUT family: {mod}"

namespace Math.SUN.SphereSection.Audit

noncomputable section

theorem south_not_in_north_patch (n : ℕ) : antipode (north n) ∉ patch n := by
  simp [patch, denominator, antipode, north]

theorem south_in_south_patch (n : ℕ) : antipode (north n) ∈ southPatch n := by
  change antipode (antipode (north n)) ∈ patch n
  rw [antipode_antipode]
  exact north_mem_patch n

theorem south_section_reaches_south (n : ℕ) :
    projection (southSection ⟨antipode (north (n + 1)), south_in_south_patch (n + 1)⟩) =
      antipode (north (n + 1)) := projection_southSection _

def firstVector : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩

theorem firstVector_mem_patch : firstVector ∈ patch 1 := by
  norm_num [patch, denominator, firstVector, Fin.last]

theorem firstVector_section_last_entry :
    (specialSection ⟨firstVector, firstVector_mem_patch⟩).val 0 1 = 1 := by
  simpa [firstVector] using
    specialSection_last_column (⟨firstVector, firstVector_mem_patch⟩ : patch 1) 0

/-- SU(1) cannot act transitively on S^1: the rank restriction is essential. -/
theorem rank_one_projection_not_surjective : ¬ Function.Surjective (@projection 0) := by
  intro h
  obtain ⟨g, hg⟩ := h (antipode (north 0))
  have hd : g.val 0 0 = 1 := by
    have hd := g.property.2
    change Matrix.det g.val = 1 at hd
    simpa [Matrix.det_fin_one] using hd
  have hc := congrArg (fun v : Sphere 1 => v.val 0) hg
  change g.val 0 0 = -1 at hc
  rw [hd] at hc
  norm_num at hc

example : Function.Surjective (@projection 1) := projection_surjective 0
example : Function.Surjective (@projection 4) := projection_surjective 3
example (n : ℕ) (g : projection ⁻¹' patch (n + 1)) :
    (northLocalProduct n).symm (northLocalProduct n g) = g :=
  (northLocalProduct n).symm_apply_apply g
example (n : ℕ) (x : southPatch (n + 1) × Block.Group (n + 1)) :
    southLocalProduct n ((southLocalProduct n).symm x) = x :=
  (southLocalProduct n).apply_symm_apply x

#print axioms rankOne_unitary
#print axioms unitarySection_last_column
#print axioms unitarySection_continuous
#print axioms correctRight_last_column
#print axioms specialSection_continuous
#print axioms projection_continuous
#print axioms projection_specialSection
#print axioms patches_cover
#print axioms southSection_continuous
#print axioms projection_southSection
#print axioms projection_surjective
#print axioms difference_mem_stabilizer
#print axioms localProduct
#print axioms localProduct_fst
#print axioms northLocalProduct
#print axioms southLocalProduct
#print axioms exists_localProduct
#print axioms south_not_in_north_patch
#print axioms south_section_reaches_south
#print axioms firstVector_section_last_entry
#print axioms rank_one_projection_not_surjective

end

end Math.SUN.SphereSection.Audit

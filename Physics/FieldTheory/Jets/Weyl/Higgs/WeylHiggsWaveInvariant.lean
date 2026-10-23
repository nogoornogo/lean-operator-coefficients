import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternal

/-! The full-relation annihilating wave sum defines an admitted coefficient
on the entire actual mixed grade, with no invariant-extension hypothesis. -/
namespace Physics.WeylHiggsWaveInvariant
set_option autoImplicit false
noncomputable section
open Math PairedWeylKinetic WeylHiggsInput

theorem factorize (g : Group) (p : A) :
    action g p = action (g.1,1) (action (1,g.2) p) := by
  have hg : g = (g.1,1)*(1,g.2) := by ext <;> simp
  conv_lhs => rw [hg, map_mul]
  rfl

theorem invariant (g : Group) (p : A) (hp : p ∈ V) :
    WeylHiggsWaveSum.functional (action g p) = WeylHiggsWaveSum.functional p := by
  rw [factorize]
  exact (WeylHiggsWaveInternal.invariant g.1 _ (grade_stable (1,g.2) hp)).trans
    (WeylHiggsWaveLorentz.invariant g.2 p hp)

def coefficient : selected.Coefficient := ⟨{
  toLinearMap := WeylHiggsWaveSum.functional.comp V.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro p
    exact invariant g p.val p.property }, fun _ hp => WeylHiggsWaveSum.annihilates hp⟩

theorem coefficient_apply (p : V) : coefficient.val p = WeylHiggsWaveSum.functional p.val := rfl
theorem candidate_value : WeylHiggsSelection.evaluate coefficient = 384*Complex.I :=
  WeylHiggsWaveSum.candidate_value

end
end Physics.WeylHiggsWaveInvariant

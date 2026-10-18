import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Open charts from local inverse equations

Shrinking two open neighborhoods makes local inverse equations into an
open partial homeomorphism, without any inverse-function theorem hypothesis.
-/

set_option autoImplicit false

namespace Math.LocalInverseChart

open Set Filter
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def ofOpen (f : X → Y) (g : Y → X) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hleft : LeftInvOn g f U) (hright : RightInvOn g f V) :
    OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := U ∩ f ⁻¹' V
  target := V ∩ g ⁻¹' U
  map_source' := fun x hx => ⟨hx.2, by simpa only [mem_preimage, hleft hx.1] using hx.1⟩
  map_target' := fun y hy => ⟨hy.2, by simpa only [mem_preimage, hright hy.1] using hy.1⟩
  left_inv' := fun x hx => hleft hx.1
  right_inv' := fun y hy => hright hy.1
  open_source := hf.isOpen_inter_preimage hU hV
  open_target := hg.isOpen_inter_preimage hV hU
  continuousOn_toFun := hf.mono inter_subset_left
  continuousOn_invFun := hg.mono inter_subset_left

theorem exists_chart_within (f : X → Y) (g : Y → X) (x : X) (y : Y)
    (s : Set X) (t : Set Y) (hs : s ∈ 𝓝 x) (ht : t ∈ 𝓝 y)
    (hxy : f x = y)
    (hf : ∀ᶠ z in 𝓝 x, ContinuousAt f z)
    (hg : ∀ᶠ z in 𝓝 y, ContinuousAt g z)
    (hleft : ∀ᶠ z in 𝓝 x, g (f z) = z)
    (hright : ∀ᶠ z in 𝓝 y, f (g z) = z) :
    ∃ e : OpenPartialHomeomorph X Y,
      (∀ z, e z = f z) ∧ (∀ z, e.symm z = g z) ∧ x ∈ e.source ∧ y ∈ e.target ∧
        e.source ⊆ s ∧ e.target ⊆ t := by
  obtain ⟨U, hUp, hU, hx⟩ := eventually_nhds_iff.mp (hf.and (hleft.and hs))
  obtain ⟨V, hVp, hV, hy⟩ := eventually_nhds_iff.mp (hg.and (hright.and ht))
  let e := ofOpen f g U V hU hV
    (fun z hz => (hUp z hz).1.continuousWithinAt)
    (fun z hz => (hVp z hz).1.continuousWithinAt)
    (fun z hz => (hUp z hz).2.1) (fun z hz => (hVp z hz).2.1)
  have hxs : x ∈ e.source := ⟨hx, by simpa only [mem_preimage, hxy] using hy⟩
  exact ⟨e, fun _ => rfl, fun _ => rfl, hxs, hxy ▸ e.map_source hxs,
    fun z hz => (hUp z hz.1).2.2, fun z hz => (hVp z hz.1).2.2⟩

end Math.LocalInverseChart

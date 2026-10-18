import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Lean.Util.CollectAxioms

/-!
# General covering and proper-map lemmas

These checked lemmas are retained from the E6 local-prover investigation.
They do not construct the positive-dimensional torus quotient bundle.

The lemmas are project-independent and can be used in any context requiring
fiber bundles, covering maps, or proper maps of topological groups.

## Contents

1. `fiberBundle_with_discrete_fiber_isCoveringMap` — a fiber bundle with discrete fiber
   is a covering map (wrapping `FiberBundle.isCoveringMap` from mathlib)

2. `properMap_of_compactGroup_quotient` — the quotient map of a topological group by a
   compact normal subgroup is proper. The normality hypothesis is not available
   for the E6 maximal torus, so this is not that candidate's quotient bridge.

Both lemmas are fully proved (no `sorry`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Bundle

namespace Math.CoveringBundle

/-!
## 1. Fiber bundle with discrete fiber → covering map
-/

/-- A fiber bundle with discrete fiber is a covering map. -/
theorem fiberBundle_with_discrete_fiber_isCoveringMap
    {X : Type*} [TopologicalSpace X]
    {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    {E : X → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  FiberBundle.isCoveringMap

/-!
## 2. Properness of the quotient map by a compact normal subgroup

For a topological group `G` and a compact normal subgroup `H`, the quotient map
`π : G → G/H` is proper.

This version is stated for a normal subgroup. No normality of the E6 maximal
torus is asserted, and its positive-dimensional fibers are not discrete.
-/

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The quotient map of a topological group by a compact normal subgroup is proper. -/
theorem properMap_of_compactGroup_quotient (H : Subgroup G) [H.Normal] [CompactSpace H] :
    IsProperMap (QuotientGroup.mk : G → G ⧸ H) := by
  have h_cont : Continuous (QuotientGroup.mk : G → G ⧸ H) :=
    QuotientGroup.continuous_mk
  have h_compact_set : IsCompact (H : Set G) :=
    isCompact_iff_compactSpace.2 ‹_›
  have h_closed : IsClosedMap (QuotientGroup.mk : G → G ⧸ H) :=
    QuotientGroup.isClosedMap_coe h_compact_set
  have h_compact_fibers : ∀ y : G ⧸ H, IsCompact (QuotientGroup.mk ⁻¹' {y}) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    -- The fiber over `gH` is the coset `gH = g • H`.
    let ψ : G → G := fun x ↦ g * x
    have hψ_cont : Continuous ψ :=
      continuous_mul.comp (Continuous.prodMk continuous_const continuous_id)
    have h_coset_compact : IsCompact (ψ '' (H : Set G)) :=
      h_compact_set.image hψ_cont
    have h_fiber_eq : ((QuotientGroup.mk : G → G ⧸ H) ⁻¹' {(QuotientGroup.mk : G → G ⧸ H) g}) = ψ '' (H : Set G) := by
      ext h
      constructor
      · intro hh
        have h_eq_val : (QuotientGroup.mk h : G ⧸ H) = (QuotientGroup.mk g) := by simpa using hh
        have h_rel : h⁻¹ * g ∈ H := by
          have := Quotient.exact h_eq_val
          have h_rel' : QuotientGroup.leftRel H h g := this
          rw [QuotientGroup.leftRel_apply] at h_rel'
          exact h_rel'
        have h_inv_rel : g⁻¹ * h ∈ H := by
          have := H.inv_mem h_rel
          simpa [mul_inv_rev, inv_inv] using this
        refine ⟨g⁻¹ * h, h_inv_rel, ?_⟩
        dsimp [ψ]
        simp
      · rintro ⟨n, hn, rfl⟩
        have h_rel : QuotientGroup.leftRel H (g * n) g := by
          rw [QuotientGroup.leftRel_apply]
          have h_eq : (g * n)⁻¹ * g = n⁻¹ := by
            calc
              (g * n)⁻¹ * g = (n⁻¹ * g⁻¹) * g := by rw [mul_inv_rev]
              _ = n⁻¹ * (g⁻¹ * g) := by rw [mul_assoc]
              _ = n⁻¹ * 1 := by rw [inv_mul_cancel]
              _ = n⁻¹ := by rw [mul_one]
          rw [h_eq]
          exact H.inv_mem hn
        have h_eq_val : (QuotientGroup.mk (g * n) : G ⧸ H) = (QuotientGroup.mk g) :=
          Quotient.sound h_rel
        simpa [ψ] using h_eq_val
    rw [h_fiber_eq]
    exact h_coset_compact
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  exact ⟨h_cont, h_closed, h_compact_fibers⟩

end Math.CoveringBundle

/-! ## Audit -/

run_cmd do
  let declarations := [
    ``Math.CoveringBundle.fiberBundle_with_discrete_fiber_isCoveringMap,
    ``Math.CoveringBundle.properMap_of_compactGroup_quotient]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "CoveringBundle: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"CoveringBundle: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"CoveringBundle: checked {declarations.length} declarations"

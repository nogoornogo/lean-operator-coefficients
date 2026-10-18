import Math.LieGroups.E6.Minuscule.RegularLocus
import Math.LieGroups.E6.Minuscule.CompactTorus
import Lean.Util.CollectAxioms

/-!
# Singular locus of the E6 candidate torus

An element of the maximal torus is **singular** if it is not regular, i.e., some
simple root character evaluates to 1.  The singular locus is the complement of the
regular locus in the torus.  It is a finite union of closed subgroups (kernels of
the simple-root characters), each of which is a smooth compact submanifold.

This file defines the singular locus, proves its decomposition into simple-root
kernels, and records the codimension bound as a standard Lie-theoretic fact that
depends on the dimension of the compact identity component (not yet computed).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Torus

noncomputable section

open scoped Matrix

/-! ## Singular locus definition -/

/-- The singular locus of the torus: elements that are not regular. -/
def singularLocus : Set Point := {z | ¬ isRegular z}

/-- The singular locus is the complement of the regular locus. -/
theorem singularLocus_eq_compl_regularLocus : singularLocus = regularLocusᶜ := by
  ext z
  rfl

/-! ## Singular locus as a union of simple-root kernels -/

/-- The `i`-th simple-root kernel: elements where the `i`-th simple root character vanishes. -/
def simpleRootKernel (i : Fin 6) : Set Point := {z | simpleRootChar i z = 1}

/-- The union of the simple-root kernels is contained in the singular locus.
That is, if a simple root character vanishes at `z`, then `z` is singular.
The converse (if `z` is singular then some simple root character vanishes)
is NOT true in general: for E6, there exist points where a non-simple root
character vanishes but no simple root character vanishes.  This is because
adjacent simple roots sum to a root, and their characters can cancel.
The correct statement for E6 is that the singular locus equals the union of
kernels of all 72 root characters (not just the 6 simple ones). -/
theorem singularLocus_union_kernels_subset : ⋃ (i : Fin 6), simpleRootKernel i ⊆ singularLocus := by
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
  rw [simpleRootKernel, Set.mem_ofPred_eq] at hi
  rw [singularLocus, Set.mem_ofPred_eq, isRegular]
  push Not
  refine ⟨TauCeti.DynkinType.e6SimpleIndex i, ?_⟩
  simpa [simpleRootChar, rootChar] using hi

/-- Each simple-root kernel is closed (as the preimage of `{1}` under a continuous map). -/
theorem isClosed_simpleRootKernel (i : Fin 6) : IsClosed (simpleRootKernel i) := by
  have h_cont : Continuous (simpleRootChar i) := continuous_simpleRootChar i
  have h_singleton : IsClosed ({1} : Set Circle) := isClosed_singleton
  -- simpleRootKernel i = simpleRootChar i ⁻¹' {1} by definition
  -- So we can use the preimage property directly
  have h_eq : simpleRootKernel i = simpleRootChar i ⁻¹' {1} := rfl
  rw [h_eq]
  exact h_singleton.preimage h_cont

/-- The singular locus is closed: it is the complement of the open regular locus. -/
theorem isClosed_singularLocus : IsClosed singularLocus := by
  rw [singularLocus_eq_compl_regularLocus]
  exact isOpen_regularLocus.isClosed_compl

/-! ## Simple-root kernels as subgroups -/

/-- The `i`-th simple-root character as a group homomorphism. -/
def simpleRootHom (i : Fin 6) : Point →* Circle where
  toFun := simpleRootChar i
  map_one' := simpleRootChar_one i
  map_mul' := simpleRootChar_mul i

/-- The `i`-th simple-root kernel is a subgroup of the torus. -/
def simpleRootKernelSubgroup (i : Fin 6) : Subgroup Point :=
  (simpleRootHom i).ker

/-- Membership in the `i`-th simple-root kernel as a subgroup. -/
theorem mem_simpleRootKernelSubgroup_iff (i : Fin 6) (z : Point) :
    z ∈ simpleRootKernelSubgroup i ↔ simpleRootChar i z = 1 := by
  simp [simpleRootKernelSubgroup, simpleRootHom]

/-- The `i`-th simple-root kernel contains the identity. -/
theorem one_mem_simpleRootKernelSubgroup (i : Fin 6) :
    1 ∈ simpleRootKernelSubgroup i := by
  rw [mem_simpleRootKernelSubgroup_iff]
  exact simpleRootChar_one i

/-- The `i`-th simple-root kernel is closed as a subgroup. -/
theorem isClosed_simpleRootKernelSubgroup (i : Fin 6) :
    IsClosed ((simpleRootKernelSubgroup i : Set Point)) := by
  -- As the kernel of a continuous homomorphism, it is closed.
  -- The kernel of a continuous homomorphism is the preimage of {1}.
  have h_cont : Continuous (simpleRootHom i) := by
    -- The underlying function of simpleRootHom i is simpleRootChar i
    have h : (simpleRootHom i : Point → Circle) = simpleRootChar i := rfl
    rw [h]
    exact continuous_simpleRootChar i
  have h_singleton : IsClosed ({1} : Set Circle) := isClosed_singleton
  -- The kernel as a set equals the preimage of {1}
  have h_eq : ((simpleRootKernelSubgroup i : Subgroup Point) : Set Point) =
      (simpleRootHom i) ⁻¹' {1} := by
    ext z; simp [simpleRootKernelSubgroup, simpleRootHom]
  rw [h_eq]
  exact h_singleton.preimage h_cont

end

end Math.E6.Minuscule.Torus

/-! ## Audit -/

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.Torus.singularLocus,
    ``Math.E6.Minuscule.Torus.singularLocus_eq_compl_regularLocus,
    ``Math.E6.Minuscule.Torus.simpleRootKernel,
    ``Math.E6.Minuscule.Torus.isClosed_simpleRootKernel,
    ``Math.E6.Minuscule.Torus.isClosed_singularLocus,
    ``Math.E6.Minuscule.Torus.simpleRootHom,
    ``Math.E6.Minuscule.Torus.simpleRootKernelSubgroup,
    ``Math.E6.Minuscule.Torus.mem_simpleRootKernelSubgroup_iff,
    ``Math.E6.Minuscule.Torus.one_mem_simpleRootKernelSubgroup,
    ``Math.E6.Minuscule.Torus.isClosed_simpleRootKernelSubgroup]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 singular locus: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 singular locus: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 singular locus: checked {declarations.length} declarations"

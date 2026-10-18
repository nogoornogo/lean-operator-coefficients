import Mathlib.Algebra.Lie.Weights.RootSystem
import Lean.Util.CollectAxioms

/-!
# Fixed-centralizer predicates retained from the local-prover draft

These are definitions and their projections, not a root-character comparison
or a theorem about the global regular locus. In particular `regularLocus T`
fixes one subgroup T and must not be claimed open or dense in a Lie group.
The unproved Lie-algebra target is archived, not assumed.
-/

set_option autoImplicit false

namespace Math.RootSpace

/-- A fixed-centralizer predicate; no equivalence with root regularity is asserted. -/
def IsRegularInTorus {G : Type*} [Group G] (T : Subgroup G) (g : G) : Prop :=
  g ∈ T ∧ Subgroup.centralizer ({g} : Set G) = T

theorem centralizer_eq_torus_of_regular {G : Type*} [Group G] (T : Subgroup G) {g : G}
    (hreg : IsRegularInTorus T g) : Subgroup.centralizer ({g} : Set G) = T :=
  hreg.2

/-- The fixed-T locus, NOT the conjugacy-invariant regular locus of G. -/
def regularLocus {G : Type*} [Group G] (T : Subgroup G) : Set G :=
  {g | Subgroup.centralizer ({g} : Set G) = T}

theorem regular_torus_subset_regularLocus {G : Type*} [Group G] (T : Subgroup G) {g : G}
    (hg : IsRegularInTorus T g) : g ∈ regularLocus T :=
  hg.2

def lieCentralizer (L : Type*) [LieRing L] (g : L) : Set L :=
  {x | ⁅g, x⁆ = 0}

end Math.RootSpace

run_cmd do
  let declarations := [
    ``Math.RootSpace.IsRegularInTorus,
    ``Math.RootSpace.centralizer_eq_torus_of_regular,
    ``Math.RootSpace.regularLocus,
    ``Math.RootSpace.regular_torus_subset_regularLocus,
    ``Math.RootSpace.lieCentralizer]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "RootSpace: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"RootSpace: {decl} depends on axioms: {axioms}"

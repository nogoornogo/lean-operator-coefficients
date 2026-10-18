import TauCeti.Algebra.Lie.E6.Minuscule.RootDatum
import TauCeti.Algebra.Lie.E6.Minuscule.ClosedRootSubgroup
import TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Killing
import Mathlib.Basic.Complex.Basic
import Lean.Util.CollectAxioms

/-!
# E6-0: pinned algebraic ingredients, not a compact E6 implementation

Check the actual types and transitive axioms of the finite weight model, Serre
representation, and algebraic carrier. Neither a named root datum nor a closed
immersion of group schemes identifies the carrier with the desired compact
real group. In particular, no compactness, Spin inclusion, continuous unitary
27 action, or SM branching theorem is claimed here.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open TauCeti.DynkinType TauCeti.E6Minuscule
open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

example : Function.Injective e6MinusculeWeight := e6MinusculeWeight_injective

example : e6MinusculeWeight 0 = Pi.single 0 1 := e6MinusculeWeight_zero

example : Submodule.span ℤ (Set.range e6MinusculeWeight) = ⊤ :=
  span_range_e6MinusculeWeight_eq_top

example : (MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
    (Pi.single 0 1 : Fin 6 → ℤ)).ncard = 27 := ncard_orbit_e6MinusculeWeight

example : TauCeti.IsSerreSystem ℤ (CartanMatrix.E 6)ᵀ
    cartanGeneratorMatrix raisingMatrix loweringMatrix := isSerreSystem

example : TauCeti.IsSerreSystem ℚ (CartanMatrix.E 6)ᵀ
    weightTable.cartanGeneratorMatrixQ weightTable.raisingMatrixQ
      weightTable.loweringMatrixQ := weightTable.isSerreSystemQ

-- These are algebraic matrix points; no compact topology is asserted.
example : Group (points ℂ) := inferInstance

example : (points ℂ) →* Matrix.GeneralLinearGroup (Fin 27) ℂ :=
  (points ℂ).subtype

example : Function.Injective (points ℂ).subtype := Subtype.val_injective

example : (Fin 6 → ℂˣ) →* points ℂ := weightTorusPoints ℂ

example (k : Fin 6 ⊕ Fin 6) : Multiplicative ℂ →* points ℂ :=
  rootSubgroupPoints k ℂ

example : AlgebraicGeometry.IsClosedImmersion carrierι.hom.hom.left := inferInstance

example : AlgebraicGeometry.IsClosedImmersion weightTorus.hom.hom.left := inferInstance

example (k : Fin 6 ⊕ Fin 6) :
    AlgebraicGeometry.IsClosedImmersion (rootSubgroup k).hom.hom.left := inferInstance

#check serreRepresentation
#check weightTable.rationalSerreRepresentation
#check groupScheme
#check pointsPresentation
#check rootGeneratorWeight_inl_eq_root_simpleIndex
#check weightTorus_conj_rootSubgroup_root_simpleIndex

-- The comparison has a proved surjectivity theorem, not an injectivity theorem.
example : Function.Surjective (TauCeti.DynkinType.serreLift E6 valid_E6) :=
  TauCeti.DynkinType.serreLift_surjective E6 valid_E6

#check TauCeti.DynkinType.serreLift E6 valid_E6

example : LieAlgebra.IsKilling ℚ (E6.lieAlgebra valid_E6) := inferInstance

example : LieAlgebra.IsKilling ℂ (E6.lieAlgebraBaseChange valid_E6 ℂ) := inferInstance

end

end Math.E6.Audit

-- Reject a changed trust boundary, rather than only printing it for inspection.
run_cmd do
  let declarations := [
    ``TauCeti.DynkinType.e6SimplyConnectedRootDatum,
    ``TauCeti.DynkinType.hasCartanType_e6SimplyConnectedRootDatum,
    ``TauCeti.DynkinType.e6MinusculeWeight_injective,
    ``TauCeti.DynkinType.e6MinusculeWeight_zero,
    ``TauCeti.DynkinType.e6MinusculeWeight_reflection,
    ``TauCeti.DynkinType.range_e6MinusculeWeight,
    ``TauCeti.DynkinType.ncard_orbit_e6MinusculeWeight,
    ``TauCeti.DynkinType.span_range_e6MinusculeWeight_eq_top,
    ``TauCeti.E6Minuscule.isSl2Triple,
    ``TauCeti.E6Minuscule.isSerreSystem,
    ``TauCeti.E6Minuscule.serreRepresentation,
    ``TauCeti.E6Minuscule.serreRepresentation_serreH,
    ``TauCeti.E6Minuscule.serreRepresentation_serreE,
    ``TauCeti.E6Minuscule.serreRepresentation_serreF,
    ``TauCeti.MinusculeWeightTable.isSerreSystemQ,
    ``TauCeti.MinusculeWeightTable.rationalSerreRepresentation,
    ``TauCeti.MinusculeWeightTable.rep_serreKostantForm_mem_lattice,
    ``TauCeti.E6Minuscule.groupScheme,
    ``TauCeti.E6Minuscule.isClosedImmersion_carrierι,
    ``TauCeti.E6Minuscule.isClosedImmersion_weightTorus,
    ``TauCeti.E6Minuscule.rootSubgroupCoordinateMap_surjective,
    ``TauCeti.E6Minuscule.isClosedImmersion_rootSubgroup,
    ``TauCeti.E6Minuscule.points,
    ``TauCeti.E6Minuscule.mem_points_iff,
    ``TauCeti.E6Minuscule.coe_rootSubgroupPoints,
    ``TauCeti.E6Minuscule.coe_weightTorusPoints,
    ``TauCeti.E6Minuscule.pointsPresentation,
    ``TauCeti.E6Minuscule.map_rootSubgroupPoints,
    ``TauCeti.E6Minuscule.map_weightTorusPoints,
    ``TauCeti.E6Minuscule.rootGeneratorWeight_inl_eq_root_simpleIndex,
    ``TauCeti.E6Minuscule.rootGeneratorWeight_inr_eq_neg_root_simpleIndex,
    ``TauCeti.E6Minuscule.weightTorus_conj_rootSubgroup_root_simpleIndex,
    ``TauCeti.E6Minuscule.weightTorus_conj_rootSubgroup_neg_root_simpleIndex,
    ``TauCeti.DynkinType.serreLift,
    ``TauCeti.DynkinType.serreLift_surjective,
    ``TauCeti.DynkinType.geckLieEquiv,
    ``TauCeti.DynkinType.instIsKillingLieAlgebra,
    ``TauCeti.DynkinType.instIsKillingLieAlgebraBaseChange]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0: checked {declarations.length} declarations against the standard axiom allowlist"

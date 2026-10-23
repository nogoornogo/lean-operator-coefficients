import Physics.FieldTheory.Jets.Lagrangian.LagrangianModelLiterature
import Physics.FieldTheory.Jets.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.RegisteredLagrangianModels
import Physics.FieldTheory.Jets.DerivativeLiteratureRecheck
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.LagrangianModelLiterature instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LagrangianModelLiterature.CPV.first_order => Physics.LagrangianModelLiterature.CPV.first_order,
  GUT.LagrangianModelLiterature.CPV.higher_order_survives => Physics.LagrangianModelLiterature.CPV.higher_order_survives,
  GUT.LagrangianModelLiterature.DHM.chi => Physics.LagrangianModelLiterature.DHM.chi,
  GUT.LagrangianModelLiterature.DHM.chi.eq_1 => Physics.LagrangianModelLiterature.DHM.chi.eq_1,
  GUT.LagrangianModelLiterature.DHM.coefficient_equations => Physics.LagrangianModelLiterature.DHM.coefficient_equations,
  GUT.LagrangianModelLiterature.DHM.density_dictionary => Physics.LagrangianModelLiterature.DHM.density_dictionary,
  GUT.LagrangianModelLiterature.DHM.direct_paper_equations => Physics.LagrangianModelLiterature.DHM.direct_paper_equations,
  GUT.LagrangianModelLiterature.DHM.dotted => Physics.LagrangianModelLiterature.DHM.dotted,
  GUT.LagrangianModelLiterature.DHM.dotted.eq_1 => Physics.LagrangianModelLiterature.DHM.dotted.eq_1,
  GUT.LagrangianModelLiterature.DHM.dotted_dictionary => Physics.LagrangianModelLiterature.DHM.dotted_dictionary,
  GUT.LagrangianModelLiterature.DHM.dotted_euler => Physics.LagrangianModelLiterature.DHM.dotted_euler,
  GUT.LagrangianModelLiterature.DHM.dotted_interaction_euler => Physics.LagrangianModelLiterature.DHM.dotted_interaction_euler,
  GUT.LagrangianModelLiterature.DHM.euler_dictionary => Physics.LagrangianModelLiterature.DHM.euler_dictionary,
  GUT.LagrangianModelLiterature.DHM.full_lorentz => Physics.LagrangianModelLiterature.DHM.full_lorentz,
  GUT.LagrangianModelLiterature.DHM.full_relation_dictionary => Physics.LagrangianModelLiterature.DHM.full_relation_dictionary,
  GUT.LagrangianModelLiterature.DHM.kinetic => Physics.LagrangianModelLiterature.DHM.kinetic,
  GUT.LagrangianModelLiterature.DHM.kinetic.eq_1 => Physics.LagrangianModelLiterature.DHM.kinetic.eq_1,
  GUT.LagrangianModelLiterature.DHM.kinetic_dictionary => Physics.LagrangianModelLiterature.DHM.kinetic_dictionary,
  GUT.LagrangianModelLiterature.DHM.kinetic_euler_dictionary => Physics.LagrangianModelLiterature.DHM.kinetic_euler_dictionary,
  GUT.LagrangianModelLiterature.DHM.model => Physics.LagrangianModelLiterature.DHM.model,
  GUT.LagrangianModelLiterature.DHM.paperCoefficientEquiv => Physics.LagrangianModelLiterature.DHM.paperCoefficientEquiv,
  GUT.LagrangianModelLiterature.DHM.paperDensity => Physics.LagrangianModelLiterature.DHM.paperDensity,
  GUT.LagrangianModelLiterature.DHM.paperDensity.eq_1 => Physics.LagrangianModelLiterature.DHM.paperDensity.eq_1,
  GUT.LagrangianModelLiterature.DHM.paperModel => Physics.LagrangianModelLiterature.DHM.paperModel,
  GUT.LagrangianModelLiterature.DHM.paper_evaluation => Physics.LagrangianModelLiterature.DHM.paper_evaluation,
  GUT.LagrangianModelLiterature.DHM.parameters => Physics.LagrangianModelLiterature.DHM.parameters,
  GUT.LagrangianModelLiterature.DHM.parameters.eq_1 => Physics.LagrangianModelLiterature.DHM.parameters.eq_1,
  GUT.LagrangianModelLiterature.DHM.raised => Physics.LagrangianModelLiterature.DHM.raised,
  GUT.LagrangianModelLiterature.DHM.raised.eq_1 => Physics.LagrangianModelLiterature.DHM.raised.eq_1,
  GUT.LagrangianModelLiterature.DHM.undotted => Physics.LagrangianModelLiterature.DHM.undotted,
  GUT.LagrangianModelLiterature.DHM.undotted.eq_1 => Physics.LagrangianModelLiterature.DHM.undotted.eq_1,
  GUT.LagrangianModelLiterature.DHM.undotted_dictionary => Physics.LagrangianModelLiterature.DHM.undotted_dictionary,
  GUT.LagrangianModelLiterature.DHM.undotted_euler => Physics.LagrangianModelLiterature.DHM.undotted_euler,
  GUT.LagrangianModelLiterature.DHM.undotted_interaction_euler => Physics.LagrangianModelLiterature.DHM.undotted_interaction_euler,
  GUT.LagrangianModelLiterature.Warsaw.gaugeless_higgs => Physics.LagrangianModelLiterature.Warsaw.gaugeless_higgs,
  GUT.LagrangianModelLiterature.instAddCommGroupA_physics => Physics.LagrangianModelLiterature.instAddCommGroupA_physics,
  GUT.LagrangianModelLiterature.instModuleComplexA_physics => Physics.LagrangianModelLiterature.instModuleComplexA_physics,
  GUT.LagrangianModelLiterature.instRingA_physics => Physics.LagrangianModelLiterature.instRingA_physics
]

assert_compatible GUT.LagrangianModelLiterature.CPV.first_order => Physics.LagrangianModelLiterature.CPV.first_order
assert_compatible GUT.LagrangianModelLiterature.CPV.higher_order_survives => Physics.LagrangianModelLiterature.CPV.higher_order_survives
assert_compatible GUT.LagrangianModelLiterature.DHM.chi => Physics.LagrangianModelLiterature.DHM.chi
assert_compatible GUT.LagrangianModelLiterature.DHM.chi.eq_1 => Physics.LagrangianModelLiterature.DHM.chi.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.coefficient_equations => Physics.LagrangianModelLiterature.DHM.coefficient_equations
assert_compatible GUT.LagrangianModelLiterature.DHM.density_dictionary => Physics.LagrangianModelLiterature.DHM.density_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.direct_paper_equations => Physics.LagrangianModelLiterature.DHM.direct_paper_equations
assert_compatible GUT.LagrangianModelLiterature.DHM.dotted => Physics.LagrangianModelLiterature.DHM.dotted
assert_compatible GUT.LagrangianModelLiterature.DHM.dotted.eq_1 => Physics.LagrangianModelLiterature.DHM.dotted.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.dotted_dictionary => Physics.LagrangianModelLiterature.DHM.dotted_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.dotted_euler => Physics.LagrangianModelLiterature.DHM.dotted_euler
assert_compatible GUT.LagrangianModelLiterature.DHM.dotted_interaction_euler => Physics.LagrangianModelLiterature.DHM.dotted_interaction_euler
assert_compatible GUT.LagrangianModelLiterature.DHM.euler_dictionary => Physics.LagrangianModelLiterature.DHM.euler_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.full_lorentz => Physics.LagrangianModelLiterature.DHM.full_lorentz
assert_compatible GUT.LagrangianModelLiterature.DHM.full_relation_dictionary => Physics.LagrangianModelLiterature.DHM.full_relation_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.kinetic => Physics.LagrangianModelLiterature.DHM.kinetic
assert_compatible GUT.LagrangianModelLiterature.DHM.kinetic.eq_1 => Physics.LagrangianModelLiterature.DHM.kinetic.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.kinetic_dictionary => Physics.LagrangianModelLiterature.DHM.kinetic_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.kinetic_euler_dictionary => Physics.LagrangianModelLiterature.DHM.kinetic_euler_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.model => Physics.LagrangianModelLiterature.DHM.model
assert_compatible GUT.LagrangianModelLiterature.DHM.paperCoefficientEquiv => Physics.LagrangianModelLiterature.DHM.paperCoefficientEquiv
assert_compatible GUT.LagrangianModelLiterature.DHM.paperDensity => Physics.LagrangianModelLiterature.DHM.paperDensity
assert_compatible GUT.LagrangianModelLiterature.DHM.paperDensity.eq_1 => Physics.LagrangianModelLiterature.DHM.paperDensity.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.paperModel => Physics.LagrangianModelLiterature.DHM.paperModel
assert_compatible GUT.LagrangianModelLiterature.DHM.paper_evaluation => Physics.LagrangianModelLiterature.DHM.paper_evaluation
assert_compatible GUT.LagrangianModelLiterature.DHM.parameters => Physics.LagrangianModelLiterature.DHM.parameters
assert_compatible GUT.LagrangianModelLiterature.DHM.parameters.eq_1 => Physics.LagrangianModelLiterature.DHM.parameters.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.raised => Physics.LagrangianModelLiterature.DHM.raised
assert_compatible GUT.LagrangianModelLiterature.DHM.raised.eq_1 => Physics.LagrangianModelLiterature.DHM.raised.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.undotted => Physics.LagrangianModelLiterature.DHM.undotted
assert_compatible GUT.LagrangianModelLiterature.DHM.undotted.eq_1 => Physics.LagrangianModelLiterature.DHM.undotted.eq_1
assert_compatible GUT.LagrangianModelLiterature.DHM.undotted_dictionary => Physics.LagrangianModelLiterature.DHM.undotted_dictionary
assert_compatible GUT.LagrangianModelLiterature.DHM.undotted_euler => Physics.LagrangianModelLiterature.DHM.undotted_euler
assert_compatible GUT.LagrangianModelLiterature.DHM.undotted_interaction_euler => Physics.LagrangianModelLiterature.DHM.undotted_interaction_euler
assert_compatible GUT.LagrangianModelLiterature.Warsaw.gaugeless_higgs => Physics.LagrangianModelLiterature.Warsaw.gaugeless_higgs
assert_compatible GUT.LagrangianModelLiterature.instAddCommGroupA_physics => Physics.LagrangianModelLiterature.instAddCommGroupA_physics
assert_compatible GUT.LagrangianModelLiterature.instModuleComplexA_physics => Physics.LagrangianModelLiterature.instModuleComplexA_physics
assert_compatible GUT.LagrangianModelLiterature.instRingA_physics => Physics.LagrangianModelLiterature.instRingA_physics

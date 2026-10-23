import Physics.StandardModel.Operators.Dipole.DipoleCouplingModel
import Physics.StandardModel.Operators.DipoleMediatorPaths
import Math.LinearAlgebra.BilinearSelectedPaths
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleCouplingModel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleCouplingModel.Couplings => Physics.DipoleCouplingModel.Couplings,
  GUT.DipoleCouplingModel.Couplings.casesOn => Physics.DipoleCouplingModel.Couplings.casesOn,
  GUT.DipoleCouplingModel.Couplings.ctorIdx => Physics.DipoleCouplingModel.Couplings.ctorIdx,
  GUT.DipoleCouplingModel.Couplings.incoming => Physics.DipoleCouplingModel.Couplings.incoming,
  GUT.DipoleCouplingModel.Couplings.mk => Physics.DipoleCouplingModel.Couplings.mk,
  GUT.DipoleCouplingModel.Couplings.mk.inj => Physics.DipoleCouplingModel.Couplings.mk.inj,
  GUT.DipoleCouplingModel.Couplings.mk.injEq => Physics.DipoleCouplingModel.Couplings.mk.injEq,
  GUT.DipoleCouplingModel.Couplings.mk.noConfusion => Physics.DipoleCouplingModel.Couplings.mk.noConfusion,
  GUT.DipoleCouplingModel.Couplings.mk.sizeOf_spec => Physics.DipoleCouplingModel.Couplings.mk.sizeOf_spec,
  GUT.DipoleCouplingModel.Couplings.noConfusion => Physics.DipoleCouplingModel.Couplings.noConfusion,
  GUT.DipoleCouplingModel.Couplings.noConfusionType => Physics.DipoleCouplingModel.Couplings.noConfusionType,
  GUT.DipoleCouplingModel.Couplings.outgoingB => Physics.DipoleCouplingModel.Couplings.outgoingB,
  GUT.DipoleCouplingModel.Couplings.outgoingW => Physics.DipoleCouplingModel.Couplings.outgoingW,
  GUT.DipoleCouplingModel.Couplings.propagator => Physics.DipoleCouplingModel.Couplings.propagator,
  GUT.DipoleCouplingModel.Couplings.rec => Physics.DipoleCouplingModel.Couplings.rec,
  GUT.DipoleCouplingModel.Couplings.recOn => Physics.DipoleCouplingModel.Couplings.recOn,
  GUT.DipoleCouplingModel.basis_paths => Physics.DipoleCouplingModel.basis_paths,
  GUT.DipoleCouplingModel.bilinear => Physics.DipoleCouplingModel.bilinear,
  GUT.DipoleCouplingModel.bilinear_apply => Physics.DipoleCouplingModel.bilinear_apply,
  GUT.DipoleCouplingModel.channel => Physics.DipoleCouplingModel.channel,
  GUT.DipoleCouplingModel.exists_nonzero_iff_basis_path => Physics.DipoleCouplingModel.exists_nonzero_iff_basis_path,
  GUT.DipoleCouplingModel.generation => Physics.DipoleCouplingModel.generation,
  GUT.DipoleCouplingModel.generation.congr_simp => Physics.DipoleCouplingModel.generation.congr_simp,
  GUT.DipoleCouplingModel.generation_eq_paths => Physics.DipoleCouplingModel.generation_eq_paths,
  GUT.DipoleCouplingModel.generation_factorization => Physics.DipoleCouplingModel.generation_factorization,
  GUT.DipoleCouplingModel.generation_residual => Physics.DipoleCouplingModel.generation_residual,
  GUT.DipoleCouplingModel.generation_zero_of_propagator_zero => Physics.DipoleCouplingModel.generation_zero_of_propagator_zero,
  GUT.DipoleCouplingModel.nonzero_at_basis_witness => Physics.DipoleCouplingModel.nonzero_at_basis_witness,
  GUT.DipoleCouplingModel.parameterized_factorization => Physics.DipoleCouplingModel.parameterized_factorization,
  GUT.DipoleCouplingModel.residual => Physics.DipoleCouplingModel.residual,
  GUT.DipoleCouplingModel.residual.eq_1 => Physics.DipoleCouplingModel.residual.eq_1,
  GUT.DipoleCouplingModel.residual_expansion => Physics.DipoleCouplingModel.residual_expansion,
  GUT.DipoleCouplingModel.selected => Physics.DipoleCouplingModel.selected,
  GUT.DipoleFlavorSelection.evaluation.eq_1 => Physics.DipoleFlavorSelection.evaluation.eq_1,
  GUT.DipoleFlavorSelection.residualSelector.eq_1 => Physics.DipoleFlavorSelection.residualSelector.eq_1
]

assert_compatible GUT.DipoleCouplingModel.Couplings => Physics.DipoleCouplingModel.Couplings
assert_compatible GUT.DipoleCouplingModel.Couplings.casesOn => Physics.DipoleCouplingModel.Couplings.casesOn
assert_compatible GUT.DipoleCouplingModel.Couplings.ctorIdx => Physics.DipoleCouplingModel.Couplings.ctorIdx
assert_compatible GUT.DipoleCouplingModel.Couplings.incoming => Physics.DipoleCouplingModel.Couplings.incoming
assert_compatible GUT.DipoleCouplingModel.Couplings.mk => Physics.DipoleCouplingModel.Couplings.mk
assert_compatible GUT.DipoleCouplingModel.Couplings.mk.inj => Physics.DipoleCouplingModel.Couplings.mk.inj
assert_compatible GUT.DipoleCouplingModel.Couplings.mk.injEq => Physics.DipoleCouplingModel.Couplings.mk.injEq
assert_compatible GUT.DipoleCouplingModel.Couplings.mk.noConfusion => Physics.DipoleCouplingModel.Couplings.mk.noConfusion
assert_compatible GUT.DipoleCouplingModel.Couplings.mk.sizeOf_spec => Physics.DipoleCouplingModel.Couplings.mk.sizeOf_spec
assert_compatible GUT.DipoleCouplingModel.Couplings.noConfusion => Physics.DipoleCouplingModel.Couplings.noConfusion
assert_compatible GUT.DipoleCouplingModel.Couplings.noConfusionType => Physics.DipoleCouplingModel.Couplings.noConfusionType
assert_compatible GUT.DipoleCouplingModel.Couplings.outgoingB => Physics.DipoleCouplingModel.Couplings.outgoingB
assert_compatible GUT.DipoleCouplingModel.Couplings.outgoingW => Physics.DipoleCouplingModel.Couplings.outgoingW
assert_compatible GUT.DipoleCouplingModel.Couplings.propagator => Physics.DipoleCouplingModel.Couplings.propagator
assert_compatible GUT.DipoleCouplingModel.Couplings.rec => Physics.DipoleCouplingModel.Couplings.rec
assert_compatible GUT.DipoleCouplingModel.Couplings.recOn => Physics.DipoleCouplingModel.Couplings.recOn
assert_compatible GUT.DipoleCouplingModel.basis_paths => Physics.DipoleCouplingModel.basis_paths
assert_compatible GUT.DipoleCouplingModel.bilinear => Physics.DipoleCouplingModel.bilinear
assert_compatible GUT.DipoleCouplingModel.bilinear_apply => Physics.DipoleCouplingModel.bilinear_apply
assert_compatible GUT.DipoleCouplingModel.channel => Physics.DipoleCouplingModel.channel
assert_compatible GUT.DipoleCouplingModel.exists_nonzero_iff_basis_path => Physics.DipoleCouplingModel.exists_nonzero_iff_basis_path
assert_compatible GUT.DipoleCouplingModel.generation => Physics.DipoleCouplingModel.generation
assert_compatible GUT.DipoleCouplingModel.generation.congr_simp => Physics.DipoleCouplingModel.generation.congr_simp
assert_compatible GUT.DipoleCouplingModel.generation_eq_paths => Physics.DipoleCouplingModel.generation_eq_paths
assert_compatible GUT.DipoleCouplingModel.generation_factorization => Physics.DipoleCouplingModel.generation_factorization
assert_compatible GUT.DipoleCouplingModel.generation_residual => Physics.DipoleCouplingModel.generation_residual
assert_compatible GUT.DipoleCouplingModel.generation_zero_of_propagator_zero => Physics.DipoleCouplingModel.generation_zero_of_propagator_zero
assert_compatible GUT.DipoleCouplingModel.nonzero_at_basis_witness => Physics.DipoleCouplingModel.nonzero_at_basis_witness
assert_compatible GUT.DipoleCouplingModel.parameterized_factorization => Physics.DipoleCouplingModel.parameterized_factorization
assert_compatible GUT.DipoleCouplingModel.residual => Physics.DipoleCouplingModel.residual
assert_compatible GUT.DipoleCouplingModel.residual.eq_1 => Physics.DipoleCouplingModel.residual.eq_1
assert_compatible GUT.DipoleCouplingModel.residual_expansion => Physics.DipoleCouplingModel.residual_expansion
assert_compatible GUT.DipoleCouplingModel.selected => Physics.DipoleCouplingModel.selected
assert_compatible GUT.DipoleFlavorSelection.evaluation.eq_1 => Physics.DipoleFlavorSelection.evaluation.eq_1
assert_compatible GUT.DipoleFlavorSelection.residualSelector.eq_1 => Physics.DipoleFlavorSelection.residualSelector.eq_1

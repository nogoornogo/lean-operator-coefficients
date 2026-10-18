import Math.LieGroups.Spin.FockCommutant

/-! Comparison of the actual compact SU(5) lift with its exterior action.
The scalar is constructed from the actual action, not supplied as a certificate.
Its triviality is proved separately in `SU5ExteriorAction`. -/

set_option autoImplicit false

namespace Math.CompactSpin.ExteriorComparison

noncomputable section

theorem actual_generator_intertwining (g : SU5) (v : Polarized.RealSpace 5)
    (s : Fock.Space 5) :
    Fock.representation 5 (SU5Inclusion g) (Fock.generator 5 v s) =
      Fock.generator 5 (SpecialUnitaryRealification.realAction g v)
        (Fock.representation 5 (SU5Inclusion g) s) := by
  have h := LinearMap.congr_fun (Fock.SU5_conjugation g v)
    (Fock.representation 5 (SU5Inclusion g) s)
  simpa only [Module.End.mul_apply, Representation.inv_self_apply] using h

def comparisonOperator (g : SU5) : Module.End ℂ (Fock.Space 5) :=
  (exteriorAction g).symm.toLinearMap.comp (Fock.representation 5 (SU5Inclusion g))

theorem comparisonOperator_commutes (g : SU5) (v : Polarized.RealSpace 5) :
    Commute (comparisonOperator g) (Fock.generator 5 v) := by
  apply LinearMap.ext
  intro s
  change (exteriorAction g).symm
    (Fock.representation 5 (SU5Inclusion g) (Fock.generator 5 v s)) =
      Fock.generator 5 v ((exteriorAction g).symm (Fock.representation 5 (SU5Inclusion g) s))
  apply (exteriorAction g).injective
  rw [LinearEquiv.apply_symm_apply, generator_naturality, LinearEquiv.apply_symm_apply,
    actual_generator_intertwining]

def scalar (g : SU5) : ℂ := Fock.vacuumScalar 5 (comparisonOperator g)

theorem comparisonOperator_eq_scalar (g : SU5) : comparisonOperator g = scalar g • 1 :=
  Fock.commutant_scalar 5 _ (comparisonOperator_commutes g)

theorem actual_eq_scalar_exterior (g : SU5) (s : Fock.Space 5) :
    Fock.representation 5 (SU5Inclusion g) s = scalar g • exteriorAction g s := by
  have h := congrArg (exteriorAction g)
    (LinearMap.congr_fun (comparisonOperator_eq_scalar g) s)
  simpa only [comparisonOperator, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_smul] using h

theorem scalar_ne_zero (g : SU5) : scalar g ≠ 0 := by
  intro h
  have hs := actual_eq_scalar_exterior g 1
  rw [h, zero_smul] at hs
  have hzero : (1 : Fock.Space 5) = 0 :=
    ((Fock.representation 5).apply_bijective (SU5Inclusion g)).injective (by simpa using hs)
  exact one_ne_zero hzero

theorem actual_vacuum (g : SU5) :
    Fock.representation 5 (SU5Inclusion g) 1 = scalar g • (1 : Fock.Space 5) := by
  have h := actual_eq_scalar_exterior g 1
  change Fock.representation 5 (SU5Inclusion g) 1 =
    scalar g • ExteriorNaturality.mapEquiv (WAction g) 1 at h
  simpa only [map_one] using h

theorem scalar_eq_vacuumCoefficient (g : SU5) :
    scalar g = ExteriorAlgebra.algebraMapInv (Fock.representation 5 (SU5Inclusion g) 1) := by
  rw [actual_vacuum, map_smul, map_one, smul_eq_mul, mul_one]

theorem scalar_one : scalar 1 = 1 := by
  simp only [scalar_eq_vacuumCoefficient, map_one, Module.End.one_apply]

theorem scalar_mul (g h : SU5) : scalar (g * h) = scalar g * scalar h := by
  rw [scalar_eq_vacuumCoefficient, map_mul, map_mul, Module.End.mul_apply,
    actual_vacuum, map_smul, actual_vacuum, map_smul, map_smul, map_one]
  simp only [smul_eq_mul, mul_comm, one_mul]

def scalarHom : SU5 →* ℂ where
  toFun := scalar
  map_one' := scalar_one
  map_mul' := scalar_mul

theorem scalar_continuous : Continuous scalarHom := by
  change Continuous scalar
  have h := (Fock.coefficient_continuous 5 ExteriorAlgebra.algebraMapInv.toLinearMap 1).comp
    SU5Inclusion_continuous
  simpa only [AlgHom.toLinearMap_apply, Function.comp_def, ← scalar_eq_vacuumCoefficient] using h

theorem halfSpin_eq_scalar_exterior (g : SU5) (s : HalfSpin.Space 5) :
    (HalfSpin.representation 5 (SU5Inclusion g) s : Fock.Space 5) =
      scalar g • exteriorAction g s := by
  rw [Fock.halfSpin_restriction, actual_eq_scalar_exterior]

end

end Math.CompactSpin.ExteriorComparison

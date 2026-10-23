import GUT.SU6.SelectionRules.Models.StandardSMUVYukawa
import GUT.SU6.SelectionRules.Models.StandardSMUVCoordinates
import GUT.SU6.Characters.SignedWeylTransposition

open Physics

open Math

/-!
# An extra stabilizer of the constructed scalar vacuum

The witness mixes a color coordinate with a weak coordinate while fixing
the sixth coordinate. All equalities refer to the existing UV mass and VEV;
neither is replaced by a new mass or an assumed invariance certificate.
-/

set_option autoImplicit false

namespace GUT.StandardSMUVStabilizer

noncomputable section

open StandardSMUVFields SplitRepresentationProjection StandardSMUVCoordinates

abbrev Six := Fin 6 → ℂ
abbrev Wedge := ⋀[ℂ]^2 Six

def rotation : ActualRestriction.SU6 :=
  SignedWeylTransposition.signedTranspositionSU 0 3 (by decide)

theorem rotation_apply (v : Six) :
    FundamentalRepresentation.rho rotation v = ![-v 3, v 1, v 2, v 0, v 4, v 5] := by
  funext i
  fin_cases i <;>
    simp [FundamentalRepresentation.rho, rotation,
      SignedWeylTransposition.signedTranspositionSU,
      SignedWeylTransposition.signedMatrix, SignedWeylTransposition.signMatrix,
      SignedWeylTransposition.signAt, SignedWeylTransposition.permutationMatrix,
      SignedWeylTransposition.transposition, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Equiv.swap_apply_def]

def sixth : Six := ![0, 0, 0, 0, 0, 1]

theorem rotation_sixth : FundamentalRepresentation.rho rotation sixth = sixth := by
  rw [rotation_apply]
  simp [sixth]

theorem rotation_inv_sixth : FundamentalRepresentation.rho rotation⁻¹ sixth = sixth := by
  calc
    FundamentalRepresentation.rho rotation⁻¹ sixth =
        FundamentalRepresentation.rho rotation⁻¹ (FundamentalRepresentation.rho rotation sixth) :=
      congrArg (FundamentalRepresentation.rho rotation⁻¹) rotation_sixth.symm
    _ = sixth := Representation.inv_self_apply _ _ _

theorem rotation_last (v : Six) : FundamentalRepresentation.rho rotation v 5 = v 5 := by
  rw [rotation_apply]
  rfl

def extract : StandardSMExterior.Blocks →ₗ[ℂ] Six where
  toFun x := ![x.2.2.2.1 0, x.2.2.2.1 1, x.2.2.2.1 2,
    x.2.2.2.2 0, x.2.2.2.2 1, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

def contract : Wedge →ₗ[ℂ] Six := extract.comp StandardSMExterior.branch

theorem contract_wedge (v : Fin 2 → Six) :
    contract (exteriorPower.ιMulti ℂ 2 v) = v 1 5 • v 0 - v 0 5 • v 1 := by
  change extract (StandardSMExterior.branch (exteriorPower.ιMulti ℂ 2 v)) = _
  rw [StandardSMExterior.branch_wedge]
  funext i
  fin_cases i <;> simp [extract, StandardSMExterior.pair, StandardSMGroup.splitEquiv,
    mul_comm]

theorem contract_covariant (g : ActualRestriction.SU6)
    (hg : ∀ v : Six, FundamentalRepresentation.rho g v 5 = v 5) (w : Wedge) :
    contract (exteriorPower.map 2 (FundamentalRepresentation.rho g) w) =
      FundamentalRepresentation.rho g (contract w) := by
  have he : contract.comp (exteriorPower.map 2 (FundamentalRepresentation.rho g)) =
      (FundamentalRepresentation.rho g).comp contract := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext; intro v
    change contract (exteriorPower.map 2 (FundamentalRepresentation.rho g)
      (exteriorPower.ιMulti ℂ 2 v)) = _
    rw [exteriorPower.map_apply_ιMulti, contract_wedge]
    change _ = FundamentalRepresentation.rho g (contract (exteriorPower.ιMulti ℂ 2 v))
    rw [contract_wedge, map_sub, map_smul, map_smul]
    simp only [Function.comp_apply, hg]
  exact LinearMap.congr_fun he w

def exteriorRho : Representation ℂ ActualRestriction.SU6 Wedge :=
  (CertifiedConstructions.exteriorActual FundamentalRepresentation.actual 2).rho

def exteriorCoordinates : Representation.Equiv ConcreteSU6Representations.exteriorTwo.rho
    exteriorRho := ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm
def dualCoordinates : Representation.Equiv ConcreteSU6Representations.antifundamental.rho
    FundamentalRepresentation.rho.dual := ConcreteSU6Representations.antifundamentalEquiv.symm

def heavyVector (x : UV) : Six :=
  contract (exteriorCoordinates x.1.1) + dualCoordinates x.1.2 sixth • sixth

attribute [local irreducible] uvRho StandardSMGroup.hom FundamentalRepresentation.rho

def gaugeLinear : UV ≃ₗ[ℂ] StandardSMFullGaugeMass.Fields :=
  ((StandardSMExterior.analyticEquiv.toLinearEquiv.prodCongr
    ((ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
      StandardSMGroup.splitEquiv.symm.dualMap).trans
      StandardSMContragredient.heavyDualEquiv.toLinearEquiv)).trans reorder).prodCongr
    (ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
      StandardSMGroup.splitEquiv.symm.dualMap)

theorem gaugeEquiv_linear : gaugeEquiv.toLinearEquiv = gaugeLinear := by
  have hc : StandardSMContragredient.antifundamentalEquiv.toLinearEquiv =
      (ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
        StandardSMGroup.splitEquiv.symm.dualMap).trans
        StandardSMContragredient.heavyDualEquiv.toLinearEquiv := by
    unfold StandardSMContragredient.antifundamentalEquiv
    erw [trans_linear, analyticAntifundamentalEquiv_linear]
  unfold gaugeEquiv
  erw [prod_linear, trans_linear, prod_linear, hc, analyticAntifundamentalEquiv_linear]
  rfl

theorem heavyDual_singlet (phi : Module.Dual ℂ StandardSMFullGaugeMass.Heavy) :
    singletEquiv (StandardSMContragredient.heavyDualEquiv.toLinearEquiv phi).2.2 =
      phi (0, 0, 1) := rfl

theorem exterior_branch (w : ConcreteSU6Representations.exteriorTwo.V) :
    StandardSMExterior.analyticEquiv.toLinearEquiv w =
      StandardSMExterior.branch (exteriorCoordinates w) := rfl

theorem mass_formula (H : Type*) [CommGroup H] (x y : UV) :
    (StandardSMUVMass.mass H).form x y =
      dualCoordinates y.2 (heavyVector x) + dualCoordinates x.2 (heavyVector y) := by
  rw [mass_form_gauge, gaugeEquiv_linear]
  change (StandardSMFullGaugeMass.mass (neutralCharges H)).form (gaugeLinear x) (gaugeLinear y) = _
  rw [StandardSMFullGaugeMass.mass, SplitWeylMass.mass_apply]
  have ha (z : UV) (v : StandardSMFullGaugeMass.Heavy) :
      (gaugeLinear z).2 v = dualCoordinates z.2 (StandardSMGroup.splitEquiv.symm v) := by
    change (ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
      StandardSMGroup.splitEquiv.symm.dualMap) z.2 v = _
    erw [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  rw [ha, ha]
  change dualCoordinates y.2 (StandardSMGroup.splitEquiv.symm
    ((gaugeLinear x).1.2)) + dualCoordinates x.2 (StandardSMGroup.splitEquiv.symm
    ((gaugeLinear y).1.2)) = _
  have he (z : UV) : StandardSMGroup.splitEquiv.symm ((gaugeLinear z).1.2) = heavyVector z := by
    change StandardSMGroup.splitEquiv.symm
      ((StandardSMExterior.analyticEquiv.toLinearEquiv z.1.1).2.2.2.1,
        (StandardSMExterior.analyticEquiv.toLinearEquiv z.1.1).2.2.2.2,
        singletEquiv (StandardSMContragredient.heavyDualEquiv.toLinearEquiv
          ((ConcreteSU6Representations.antifundamentalEquiv.symm.toLinearEquiv.trans
            StandardSMGroup.splitEquiv.symm.dualMap) z.1.2)).2.2) = _
    rw [heavyDual_singlet, exterior_branch]
    erw [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
    funext i
    fin_cases i <;> simp [heavyVector, contract, extract, StandardSMGroup.splitEquiv,
      dualCoordinates, sixth]
    rfl
  rw [he, he]

attribute [local semireducible] uvRho

theorem exteriorCoordinates_action (g : ActualRestriction.SU6)
    (w : ConcreteSU6Representations.exteriorTwo.V) :
    exteriorCoordinates (ConcreteSU6Representations.exteriorTwo.rho g w) =
      exteriorPower.map 2 (FundamentalRepresentation.rho g) (exteriorCoordinates w) :=
  Representation.IntertwiningMap.isIntertwining _ _ exteriorCoordinates.toIntertwiningMap g w

theorem dualCoordinates_action (g : ActualRestriction.SU6)
    (phi : ConcreteSU6Representations.antifundamental.V) (v : Six) :
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho g phi) v =
      dualCoordinates phi (FundamentalRepresentation.rho g⁻¹ v) := by
  exact LinearMap.congr_fun
    (Representation.IntertwiningMap.isIntertwining _ _ dualCoordinates.toIntertwiningMap g phi) v

theorem heavyVector_rotation (x : UV) :
    heavyVector (uvRho rotation x) = FundamentalRepresentation.rho rotation (heavyVector x) := by
  change contract (exteriorCoordinates (ConcreteSU6Representations.exteriorTwo.rho rotation x.1.1)) +
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho rotation x.1.2) sixth • sixth = _
  rw [exteriorCoordinates_action, contract_covariant rotation rotation_last,
    dualCoordinates_action, rotation_inv_sixth]
  simp only [heavyVector, map_add, map_smul, rotation_sixth]

theorem mass_rotation (H : Type*) [CommGroup H] (x y : UV) :
    (StandardSMUVMass.mass H).form (uvRho rotation x) (uvRho rotation y) =
      (StandardSMUVMass.mass H).form x y := by
  rw [mass_formula, mass_formula, heavyVector_rotation, heavyVector_rotation]
  change dualCoordinates (ConcreteSU6Representations.antifundamental.rho rotation y.2)
      (FundamentalRepresentation.rho rotation (heavyVector x)) +
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho rotation x.2)
      (FundamentalRepresentation.rho rotation (heavyVector y)) = _
  rw [dualCoordinates_action, dualCoordinates_action,
    Representation.inv_self_apply, Representation.inv_self_apply]

attribute [local irreducible] StandardSMUVMass.mass

-- Abstract the mass first so kernel conversion does not expand its branching maps.
private theorem fixed_iff_for_mass (H : Type*) [CommGroup H]
    (B : InvariantWeylMass.SymmetricMass (StandardSMUVMass.rho H)) (g : ActualRestriction.SU6) :
    (UnitarySymmetricScalar.model uvRho uv_jointlyContinuous).rho g
        (UnitarySymmetricScalar.vacuum uvRho uv_jointlyContinuous (StandardSMGroup.withResidual H) B) =
      UnitarySymmetricScalar.vacuum uvRho uv_jointlyContinuous (StandardSMGroup.withResidual H) B ↔
      ∀ x y, B.form (uvRho g x) (uvRho g y) = B.form x y :=
  UnitarySymmetricScalar.vacuum_fixed_iff uvRho uv_jointlyContinuous
    (StandardSMGroup.withResidual H) B g

theorem vacuum_fixed_iff (H : Type*) [CommGroup H] (g : ActualRestriction.SU6) :
    StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H ↔
      ∀ x y, (StandardSMUVMass.mass H).form (uvRho g x) (uvRho g y) =
        (StandardSMUVMass.mass H).form x y :=
  fixed_iff_for_mass H (StandardSMUVMass.mass H) g

theorem vacuum_rotation (H : Type*) [CommGroup H] :
    StandardSMUVYukawa.scalar.rho rotation (StandardSMUVYukawa.vacuum H) =
      StandardSMUVYukawa.vacuum H :=
  (vacuum_fixed_iff H rotation).mpr (mass_rotation H)

theorem rotation_entry : (rotation : Matrix (Fin 6) (Fin 6) ℂ) 0 3 = -1 := by
  norm_num [rotation, SignedWeylTransposition.signedTranspositionSU,
    SignedWeylTransposition.signedMatrix, SignedWeylTransposition.signMatrix,
    SignedWeylTransposition.signAt, SignedWeylTransposition.permutationMatrix,
    SignedWeylTransposition.transposition, Matrix.diagonal_mul]

theorem standard_entry (g : StandardSMGaugeTensor.GaugeGroup) :
    (StandardSMGroup.hom g : Matrix (Fin 6) (Fin 6) ℂ) 0 3 = 0 := by
  unfold StandardSMGroup.hom
  change StandardSMGroup.matrixHom g 0 3 = 0
  simp [StandardSMGroup.matrixHom, StandardSMGroup.rawHom, StandardSMGroup.rawMatrix,
    Matrix.reindex_apply, StandardSMGroup.blockIndexEquiv_symm]

theorem rotation_not_standard : rotation ∉ StandardSMGroup.hom.range := by
  rintro ⟨g, hg⟩
  have he := congrArg (fun a : ActualRestriction.SU6 => (a : Matrix (Fin 6) (Fin 6) ℂ) 0 3) hg
  rw [standard_entry, rotation_entry] at he
  norm_num at he

theorem exists_extra_stabilizer (H : Type*) [CommGroup H] :
    ∃ g : ActualRestriction.SU6, g ∉ StandardSMGroup.hom.range ∧
      StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum H) =
        StandardSMUVYukawa.vacuum H :=
  ⟨rotation, rotation_not_standard, vacuum_rotation H⟩

theorem standard_lt_stabilizer (H : Type*) [CommGroup H] :
    StandardSMGroup.hom.range <
      WeylYukawaMass.vacuumStabilizer StandardSMUVYukawa.scalar.rho (StandardSMUVYukawa.vacuum H) := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact StandardSMUVYukawa.vacuum_fixed H (g, 1)
  · intro h
    exact rotation_not_standard (h (vacuum_rotation H))

end

end GUT.StandardSMUVStabilizer

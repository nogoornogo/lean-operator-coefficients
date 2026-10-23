import Physics.StandardModel.Operators.Selection.LeptonTriality
import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.UnitaryGroup

open Math

/-!
# Actual SM matter with lepton triality

Three copies of the five left-handed SM species carry the finite residual
action. Continuity of algebraic matrix coefficients supplies an equivalent
unitary model by compact-group averaging. Zero symmetric mass has the entire
45-dimensional representation as its radical. No UV unification group is used.
-/

set_option autoImplicit false

namespace Physics.LeptonTrialitySource

noncomputable section

open StandardSMGaugeTensor StandardSMResidualTensor SMEpsilonTensor
open LeptonTriality FiniteBasisHilbertization InvariantWeylMass

abbrev Group := GaugeGroup × Residual
abbrev Generation := Quark × (Module.Dual ℂ Color ×
  (Module.Dual ℂ Color × (Weak × Module.Dual ℂ ℂ)))
abbrev Matter := Generation × (Generation × Generation)
abbrev SpeciesIndex := (Fin 3 × Fin 2) ⊕ (Fin 3 ⊕ (Fin 3 ⊕ (Fin 2 ⊕ Unit)))
abbrev MatterIndex := SpeciesIndex ⊕ (SpeciesIndex ⊕ SpeciesIndex)

def generation : Representation ℂ Group Generation :=
  (charged quark assignment.quark.toMul).prod
    ((charged upRight.dual assignment.up.toMul).prod
      ((charged downRight.dual assignment.down.toMul).prod
        ((charged lepton assignment.lepton.toMul).prod
          (charged electronRight.dual assignment.electron.toMul))))

def matter : Representation ℂ Group Matter := generation.prod (generation.prod generation)

def colorBasis : Module.Basis (Fin 3) ℂ Color := Pi.basisFun ℂ (Fin 3)
def weakBasis : Module.Basis (Fin 2) ℂ Weak := Pi.basisFun ℂ (Fin 2)
def scalarBasis : Module.Basis Unit ℂ ℂ := Module.Basis.singleton Unit ℂ
def quarkBasis := colorBasis.tensorProduct weakBasis
def generationBasis : Module.Basis SpeciesIndex ℂ Generation :=
  quarkBasis.prod (colorBasis.dualBasis.prod
    (colorBasis.dualBasis.prod (weakBasis.prod scalarBasis.dualBasis)))
def matterBasis : Module.Basis MatterIndex ℂ Matter :=
  generationBasis.prod (generationBasis.prod generationBasis)

private def ContinuousCoefficients {K V I : Type*} [_root_.Group K]
    [TopologicalSpace K] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis I ℂ V) (r : Representation ℂ K V) : Prop :=
  ∀ i j, Continuous fun g => b.coord i (r g (b j))

private theorem coefficients_prod {K V W I J : Type*} [_root_.Group K]
    [TopologicalSpace K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (b : Module.Basis I ℂ V) (c : Module.Basis J ℂ W)
    (r : Representation ℂ K V) (s : Representation ℂ K W)
    (hr : ContinuousCoefficients b r) (hs : ContinuousCoefficients c s) :
    ContinuousCoefficients (b.prod c) (r.prod s) := by
  intro i j
  change Continuous (fun g => (b.prod c).repr
    (r g ((b.prod c) j).1, s g ((b.prod c) j).2) i)
  cases i <;> cases j <;>
    simp only [Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd, map_zero]
  · exact hr _ _
  · exact continuous_const
  · exact continuous_const
  · exact hs _ _

private theorem coefficients_dual {K V I : Type*} [_root_.Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] [AddCommGroup V] [Module ℂ V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I ℂ V) (r : Representation ℂ K V)
    (hr : ContinuousCoefficients b r) : ContinuousCoefficients b.dualBasis r.dual := by
  intro i j
  simpa only [Module.Basis.coord_apply, Module.Basis.dualBasis_repr,
    Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, Module.Basis.dualBasis_apply, Function.comp_def]
      using (hr j i).comp continuous_inv

private theorem coefficients_twist {V I : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis I ℂ V) (r : Representation ℂ GaugeGroup V)
    (hr : ContinuousCoefficients b r) (y : ℤ) :
    ContinuousCoefficients b (twist r y) := by
  intro i j
  change Continuous (fun g => b.coord i (phase y g • r g (b j)))
  simp only [map_smul, smul_eq_mul]
  apply Continuous.mul _ (hr i j)
  change Continuous (fun g : GaugeGroup => ((g.2.2 ^ y : Circle) : ℂ))
  exact continuous_subtype_val.comp
    ((continuous_snd.comp continuous_snd : Continuous (fun g : GaugeGroup => g.2.2)).zpow y)

private theorem coefficients_charged {V I : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis I ℂ V) (r : Representation ℂ GaugeGroup V)
    (hr : ContinuousCoefficients b r) (chi : Residual →* Circle) :
    ContinuousCoefficients b (charged r chi) := by
  intro i j
  change Continuous (fun g : Group => b.coord i ((chi g.2 : ℂ) • r g.1 (b j)))
  simp only [map_smul, smul_eq_mul]
  exact ((continuous_subtype_val.comp
    (continuous_of_discreteTopology : Continuous chi)).comp continuous_snd).mul
      ((hr i j).comp continuous_fst)

private theorem color_coefficients : ContinuousCoefficients colorBasis color := by
  intro i j
  have hm : Continuous (fun g : GaugeGroup => (g.1 : Matrix (Fin 3) (Fin 3) ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  change Continuous (fun g : GaugeGroup =>
    ((g.1 : Matrix (Fin 3) (Fin 3) ℂ).mulVec (colorBasis j)) i)
  unfold Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro k _
  apply Continuous.mul _ continuous_const
  exact (continuous_apply k).comp ((continuous_apply i).comp hm)

private theorem weak_coefficients : ContinuousCoefficients weakBasis weak := by
  intro i j
  have hm : Continuous (fun g : GaugeGroup => (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  change Continuous (fun g : GaugeGroup =>
    ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec (weakBasis j)) i)
  unfold Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro k _
  apply Continuous.mul _ continuous_const
  exact (continuous_apply k).comp ((continuous_apply i).comp hm)

private theorem tensor_coefficients :
    ContinuousCoefficients quarkBasis (color.tprod weak) := by
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [quarkBasis, Module.Basis.coord_apply, Module.Basis.tensorProduct_apply,
    Representation.tprod_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  exact (weak_coefficients j l).mul (color_coefficients i k)

theorem generation_coefficients :
    ∀ i j, Continuous fun g => generationBasis.coord i (generation g (generationBasis j)) := by
  apply coefficients_prod
  · exact coefficients_charged _ _ (coefficients_twist _ _ tensor_coefficients 1) _
  · apply coefficients_prod
    · exact coefficients_charged _ _
        (coefficients_dual _ _ (coefficients_twist _ _ color_coefficients 4)) _
    · apply coefficients_prod
      · exact coefficients_charged _ _
          (coefficients_dual _ _ (coefficients_twist _ _ color_coefficients (-2))) _
      · apply coefficients_prod
        · exact coefficients_charged _ _ (coefficients_twist _ _ weak_coefficients (-3)) _
        · exact coefficients_charged _ _ (coefficients_dual _ _
            (coefficients_twist scalarBasis (Representation.trivial ℂ GaugeGroup ℂ)
              (by
                intro i j
                change Continuous (fun _ : GaugeGroup => scalarBasis.coord i (scalarBasis j))
                exact continuous_const) (-6))) _

theorem matter_coefficients :
    ∀ i j, Continuous fun g => matterBasis.coord i (matter g (matterBasis j)) :=
  coefficients_prod _ _ _ _ generation_coefficients
    (coefficients_prod _ _ _ _ generation_coefficients generation_coefficients)

local instance : MeasurableSpace Group := borel Group
local instance : BorelSpace Group := ⟨rfl⟩

abbrev HilbertMatter := Copy matterBasis

def unitaryModel : ContRepresentation ℂ Group HilbertMatter :=
  FiniteBasisUnitaryModel.model matterBasis matter matter_coefficients

def modelEquiv : Representation.Equiv matter unitaryModel.toRepresentation :=
  FiniteBasisUnitaryModel.modelEquiv matterBasis matter matter_coefficients

def rho : Representation ℂ Group HilbertMatter := unitaryModel.toRepresentation

theorem model_continuous : Continuous unitaryModel :=
  FiniteBasisUnitaryModel.model_continuous _ _ _

theorem model_jointlyContinuous :
    Continuous (fun p : Group × HilbertMatter => unitaryModel p.1 p.2) :=
  FiniteBasisUnitaryModel.model_jointlyContinuous _ _ _

theorem model_unitary : ContRepresentation.IsUnitary unitaryModel :=
  FiniteBasisUnitaryModel.model_unitary _ _ _

theorem model_finrank : Module.finrank ℂ HilbertMatter = 45 := by
  rw [← modelEquiv.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis matterBasis]
  decide

theorem gauge_residual_commute (g : GaugeGroup) (h : Residual) (v : HilbertMatter) :
    unitaryModel (g, 1) (unitaryModel (1, h) v) =
      unitaryModel (1, h) (unitaryModel (g, 1) v) := by
  change rho (g, 1) (rho (1, h) v) = rho (1, h) (rho (g, 1) v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

def mass : SymmetricMass unitaryModel.toRepresentation :=
  SymmetricMass.zero unitaryModel.toRepresentation

def radicalEquiv : Representation.Equiv mass.radical.toRepresentation matter :=
  (SymmetricMass.zeroRadicalEquiv unitaryModel.toRepresentation).trans modelEquiv.symm

theorem radical_finrank : Module.finrank ℂ mass.radical.toSubmodule = 45 := by
  rw [radicalEquiv.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis matterBasis]
  decide

theorem radical_character (g : Group) :
    mass.radical.toRepresentation.character g = matter.character g :=
  congrFun (Representation.char_iso radicalEquiv) g

theorem radical_dual_character (g : Group) :
    mass.radical.toRepresentation.character g - mass.radical.toRepresentation.dual.character g =
      matter.character g - matter.character g⁻¹ := by
  rw [Representation.char_dual, radical_character, radical_character]

private theorem character_prod {K V W : Type*} [_root_.Group K]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : Representation ℂ K V) (s : Representation ℂ K W) (g : K) :
    (r.prod s).character g = r.character g + s.character g :=
  LinearMap.trace_prodMap' (r g) (s g)

private theorem character_charged {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (r : Representation ℂ GaugeGroup V)
    (chi : Residual →* Circle) (g : Group) :
    (charged r chi).character g = (chi g.2 : ℂ) * r.character g.1 := by
  change LinearMap.trace ℂ V ((chi g.2 : ℂ) • r g.1) = _
  rw [map_smul]
  rfl

/-- Full-group trace of one generation in physical SM conventions. -/
def generationTrace (g : Group) : ℂ :=
  quark.character g.1 + (upRight.character g.1⁻¹ +
    (downRight.character g.1⁻¹ +
      ((character g.2 : ℂ) * lepton.character g.1 +
        ((character g.2)⁻¹ : Circle) * electronRight.character g.1⁻¹)))

theorem generation_character (g : Group) : generation.character g = generationTrace g := by
  simp [generation, character_prod, character_charged, assignment, charges, label,
    Representation.char_dual, generationTrace]

theorem matter_character (g : Group) : matter.character g = 3 * generationTrace g := by
  rw [matter, character_prod, character_prod, generation_character]
  ring

theorem radical_character_formula (g : Group) :
    mass.radical.toRepresentation.character g = 3 * generationTrace g := by
  rw [radical_character, matter_character]

theorem radical_dual_character_formula (g : Group) :
    mass.radical.toRepresentation.character g - mass.radical.toRepresentation.dual.character g =
      3 * (generationTrace g - generationTrace g⁻¹) := by
  rw [radical_dual_character, matter_character, matter_character]
  ring

def speciesCharge : SpeciesIndex → FiniteAbelianChargeSectors.ChargeLabel Residual :=
  Sum.elim (fun _ => assignment.quark)
    (Sum.elim (fun _ => assignment.up) (Sum.elim (fun _ => assignment.down)
      (Sum.elim (fun _ => assignment.lepton) (fun _ => assignment.electron))))

def matterCharge : MatterIndex → FiniteAbelianChargeSectors.ChargeLabel Residual :=
  Sum.elim speciesCharge (Sum.elim speciesCharge speciesCharge)

theorem generation_residual_basis (h : Residual) (i : SpeciesIndex) :
    generation (1, h) (generationBasis i) =
      (speciesCharge i |>.toMul h : ℂ) • generationBasis i := by
  rcases i with i | i | i | i | i <;>
    simp [generation, generationBasis, Representation.prod, charged,
      Module.Basis.prod_apply, speciesCharge]
  all_goals rfl

theorem matter_residual_basis (h : Residual) (i : MatterIndex) :
    matter (1, h) (matterBasis i) =
      (matterCharge i |>.toMul h : ℂ) • matterBasis i := by
  rcases i with i | i | i <;>
    simp [matter, matterBasis, Representation.prod, Module.Basis.prod_apply,
      matterCharge, generation_residual_basis]

/-- Actual nonzero vectors in the mass radical carry the assigned residual
characters. Joint gauge-weight support is a separate torus calculation. -/
theorem exists_charged_zeroMode (i : MatterIndex) :
    ∃ v : mass.radical.toSubmodule, v ≠ 0 ∧ ∀ h : Residual,
      mass.radical.toRepresentation (1, h) v = (matterCharge i |>.toMul h : ℂ) • v := by
  let b := matterBasis.map radicalEquiv.symm.toLinearEquiv
  refine ⟨b i, b.ne_zero i, ?_⟩
  intro h
  change mass.radical.toRepresentation (1, h) (radicalEquiv.symm (matterBasis i)) =
    (matterCharge i |>.toMul h : ℂ) • radicalEquiv.symm (matterBasis i)
  calc
    _ = radicalEquiv.symm (matter (1, h) (matterBasis i)) :=
      (radicalEquiv.symm.toIntertwiningMap.isIntertwining _ _ (1, h) (matterBasis i)).symm
    _ = _ := by
      rw [matter_residual_basis]
      exact map_smul _ _ _

end

end Physics.LeptonTrialitySource

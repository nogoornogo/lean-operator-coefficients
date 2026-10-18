import GUT.SU6.Yukawa.IndependentCouplings
import GUT.SU6.SelectionRules.Models.StandardSMUVStabilizer
import Physics.FieldTheory.Yukawa.ProjectedYukawaEvaluation

/-! Five mass directions realized by full-group equivariant Yukawa couplings.
This is a lower-bound construction, not completeness of the Yukawa space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6FiveCouplings
noncomputable section
open Representation InvariantWeylMass WeylYukawaMass StandardSMUVFields
open SU6IndependentCouplings StandardSMUVStabilizer
attribute [local irreducible] ConcreteWeylBenchmark.matter

def flavor (a b c d : ℂ) : IntertwiningMap uvRho uvRho where
  toLinearMap := ProjectedYukawa.flavorLinear a b c d
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change ((0, a • ConcreteSU6Representations.antifundamental.rho g x.1.2 +
        b • ConcreteSU6Representations.antifundamental.rho g x.2),
        c • ConcreteSU6Representations.antifundamental.rho g x.1.2 +
        d • ConcreteSU6Representations.antifundamental.rho g x.2) =
      ((ConcreteSU6Representations.exteriorTwo.rho g 0,
        ConcreteSU6Representations.antifundamental.rho g (a • x.1.2 + b • x.2)),
        ConcreteSU6Representations.antifundamental.rho g (c • x.1.2 + d • x.2))
    simp

theorem flavor_apply (a b c d : ℂ) (x : UV) :
    flavor a b c d x = ((0, a • x.1.2 + b • x.2), c • x.1.2 + d • x.2) := rfl

def coupling (a b u v w : ℂ) :=
  ProjectedYukawa.fiveFamily baseYukawa exteriorProjection
    (flavor 0 0 1 0) (flavor 0 0 0 1) (flavor 1 0 1 0)
    (flavor 1 0 0 0) (flavor 0 1 0 1) a b u v w

variable (H : Type*) [CommGroup H]

def mass (a b u v w : ℂ) := atVacuumOn (SymmetricMass.zero uvRho)
  (coupling a b u v w) (StandardSMGroup.withResidual H)
  (StandardSMUVYukawa.vacuum H) (StandardSMUVYukawa.vacuum_fixed H)

theorem mass_fiveForm (a b u v w : ℂ) :
    (mass H a b u v w).form =
      ProjectedYukawa.fiveForm (StandardSMUVMass.mass H).form exteriorProjection.toLinearMap
        (flavor 0 0 1 0).toLinearMap (flavor 0 0 0 1).toLinearMap
        (flavor 1 0 1 0).toLinearMap (flavor 1 0 0 0).toLinearMap
        (flavor 0 1 0 1).toLinearMap a b u v w :=
  ProjectedYukawa.fiveFamily_form baseYukawa exteriorProjection
    (flavor 0 0 1 0) (flavor 0 0 0 1) (flavor 1 0 1 0)
    (flavor 1 0 0 0) (flavor 0 1 0 1) a b u v w
    (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
    (StandardSMUVYukawa.vacuum_fixed H) (StandardSMUVMass.mass H).form (baseYukawa_vacuum H)

def fivePair (z : ConcreteSU6Representations.exteriorTwo.V)
    (f : ConcreteSU6Representations.antifundamental.V) : ℂ :=
  dualCoordinates f (contract (exteriorCoordinates z))

def singletCoordinate (f : ConcreteSU6Representations.antifundamental.V) : ℂ :=
  dualCoordinates f sixth

theorem base_coordinates (x y : UV) :
    (StandardSMUVMass.mass H).form x y =
      fivePair x.1.1 y.2 + singletCoordinate x.1.2 * singletCoordinate y.2 +
      fivePair y.1.1 x.2 + singletCoordinate y.1.2 * singletCoordinate x.2 := by
  rw [StandardSMUVStabilizer.mass_formula]
  simp only [fivePair, singletCoordinate, heavyVector, map_add, map_smul, smul_eq_mul, add_assoc]

theorem projected_coordinates_of (B : LinearMap.BilinForm ℂ UV)
    (hB : ∀ x y, B x y =
      fivePair x.1.1 y.2 + singletCoordinate x.1.2 * singletCoordinate y.2 +
      fivePair y.1.1 x.2 + singletCoordinate y.1.2 * singletCoordinate x.2)
    (a b u v w : ℂ) (x y : UV) :
    ProjectedYukawa.fiveForm B exteriorProjection.toLinearMap
        (ProjectedYukawa.flavorLinear 0 0 1 0) (ProjectedYukawa.flavorLinear 0 0 0 1)
        (ProjectedYukawa.flavorLinear 1 0 1 0) (ProjectedYukawa.flavorLinear 1 0 0 0)
        (ProjectedYukawa.flavorLinear 0 1 0 1) a b u v w x y =
      a * (fivePair x.1.1 y.1.2 + fivePair y.1.1 x.1.2) +
      b * (fivePair x.1.1 y.2 + fivePair y.1.1 x.2) +
      u * (singletCoordinate x.1.2 * singletCoordinate y.1.2) +
      v * (singletCoordinate x.1.2 * singletCoordinate y.2 +
        singletCoordinate x.2 * singletCoordinate y.1.2) +
      w * (singletCoordinate x.2 * singletCoordinate y.2) :=
  ProjectedYukawa.fiveForm_flavor_coordinates B
    fivePair singletCoordinate
    (by intro z; simp [fivePair]) (by simp [singletCoordinate]) exteriorProjection.toLinearMap
    hB exterior_apply a b u v w x y

/-- Keep the forms abstract while converting their pointwise evaluations;
direct conversion with the concrete UV mass is expensive in the kernel. -/
theorem mass_formula_of (M B : LinearMap.BilinForm ℂ UV)
    (hB : ∀ x y, B x y =
      fivePair x.1.1 y.2 + singletCoordinate x.1.2 * singletCoordinate y.2 +
      fivePair y.1.1 x.2 + singletCoordinate y.1.2 * singletCoordinate x.2)
    (a b u v w : ℂ)
    (hM : M = ProjectedYukawa.fiveForm B exteriorProjection.toLinearMap
        (flavor 0 0 1 0).toLinearMap (flavor 0 0 0 1).toLinearMap
        (flavor 1 0 1 0).toLinearMap (flavor 1 0 0 0).toLinearMap
        (flavor 0 1 0 1).toLinearMap a b u v w) (x y : UV) :
    M x y =
      a * (fivePair x.1.1 y.1.2 + fivePair y.1.1 x.1.2) +
      b * (fivePair x.1.1 y.2 + fivePair y.1.1 x.2) +
      u * (singletCoordinate x.1.2 * singletCoordinate y.1.2) +
      v * (singletCoordinate x.1.2 * singletCoordinate y.2 +
        singletCoordinate x.2 * singletCoordinate y.1.2) +
      w * (singletCoordinate x.2 * singletCoordinate y.2) :=
  (LinearMap.congr_fun (LinearMap.congr_fun hM x) y).trans
    (projected_coordinates_of B hB a b u v w x y)

theorem mass_formula (a b u v w : ℂ) (x y : UV) :
    (mass H a b u v w).form x y =
      a * (fivePair x.1.1 y.1.2 + fivePair y.1.1 x.1.2) +
      b * (fivePair x.1.1 y.2 + fivePair y.1.1 x.2) +
      u * (singletCoordinate x.1.2 * singletCoordinate y.1.2) +
      v * (singletCoordinate x.1.2 * singletCoordinate y.2 +
        singletCoordinate x.2 * singletCoordinate y.1.2) +
      w * (singletCoordinate x.2 * singletCoordinate y.2) :=
  mass_formula_of (mass H a b u v w).form (StandardSMUVMass.mass H).form
    (base_coordinates H) a b u v w (mass_fiveForm H a b u v w) x y

def dualProbe (i : Fin 6) : ConcreteSU6Representations.antifundamental.V :=
  dualCoordinates.symm (LinearMap.proj i)

def exteriorProbe : ConcreteSU6Representations.exteriorTwo.V :=
  exteriorCoordinates.symm (exteriorPower.ιMulti ℂ 2
    ![Pi.single (0 : Fin 6) (1 : ℂ), sixth])

theorem dualProbe_apply (i : Fin 6) (z : Six) : dualCoordinates (dualProbe i) z = z i := by
  unfold dualProbe
  rw [Representation.Equiv.apply_symm_apply]
  rfl

theorem exteriorProbe_contract :
    contract (exteriorCoordinates exteriorProbe) = Pi.single (0 : Fin 6) (1 : ℂ) := by
  unfold exteriorProbe
  rw [Representation.Equiv.apply_symm_apply, contract_wedge]
  simp [sixth]

def probeQ : UV := ((exteriorProbe, 0), 0)
def probeA (i : Fin 6) : UV := ((0, dualProbe i), 0)
def probeB (i : Fin 6) : UV := ((0, 0), dualProbe i)

theorem probe_values_of (M : LinearMap.BilinForm ℂ UV) (a b u v w : ℂ)
    (hM : ∀ x y, M x y =
      a * (fivePair x.1.1 y.1.2 + fivePair y.1.1 x.1.2) +
      b * (fivePair x.1.1 y.2 + fivePair y.1.1 x.2) +
      u * (singletCoordinate x.1.2 * singletCoordinate y.1.2) +
      v * (singletCoordinate x.1.2 * singletCoordinate y.2 +
        singletCoordinate x.2 * singletCoordinate y.1.2) +
      w * (singletCoordinate x.2 * singletCoordinate y.2)) :
    M probeQ (probeA 0) = a ∧ M probeQ (probeB 0) = b ∧
    M (probeA 5) (probeA 5) = u ∧ M (probeA 5) (probeB 5) = v ∧
    M (probeB 5) (probeB 5) = w := by
  simp [hM, probeQ, probeA, probeB, fivePair, singletCoordinate,
    exteriorProbe_contract, dualProbe_apply, sixth]

theorem probe_values (a b u v w : ℂ) :
    (mass H a b u v w).form probeQ (probeA 0) = a ∧
    (mass H a b u v w).form probeQ (probeB 0) = b ∧
    (mass H a b u v w).form (probeA 5) (probeA 5) = u ∧
    (mass H a b u v w).form (probeA 5) (probeB 5) = v ∧
    (mass H a b u v w).form (probeB 5) (probeB 5) = w :=
  probe_values_of (mass H a b u v w).form a b u v w (mass_formula H a b u v w)

theorem mass_eq_iff (a b u v w a' b' u' v' w' : ℂ) :
    mass H a b u v w = mass H a' b' u' v' w' ↔
      a = a' ∧ b = b' ∧ u = u' ∧ v = v' ∧ w = w' := by
  constructor
  · intro h
    have hp := probe_values H a b u v w
    have hq := probe_values H a' b' u' v' w'
    rw [h] at hp
    exact ⟨hp.1.symm.trans hq.1, hp.2.1.symm.trans hq.2.1,
      hp.2.2.1.symm.trans hq.2.2.1, hp.2.2.2.1.symm.trans hq.2.2.2.1,
      hp.2.2.2.2.symm.trans hq.2.2.2.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem coupling_eq_iff (a b u v w a' b' u' v' w' : ℂ) :
    coupling a b u v w = coupling a' b' u' v' w' ↔
      a = a' ∧ b = b' ∧ u = u' ∧ v = v' ∧ w = w' := by
  constructor
  · intro h
    apply (mass_eq_iff Unit a b u v w a' b' u' v' w').mp
    unfold mass
    rw [h]
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

def massMap : (Fin 5 → ℂ) →ₗ[ℂ] LinearMap.BilinForm ℂ UV where
  toFun c := (mass H (c 0) (c 1) (c 2) (c 3) (c 4)).form
  map_add' c d := by
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    simp only [mass_formula, Pi.add_apply, LinearMap.add_apply]
    ring
  map_smul' z c := by
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    simp only [mass_formula, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem massMap_injective : Function.Injective (massMap H) := by
  intro c d h
  have hm : mass H (c 0) (c 1) (c 2) (c 3) (c 4) =
      mass H (d 0) (d 1) (d 2) (d 3) (d 4) := SymmetricMass.ext h
  obtain ⟨h0, h1, h2, h3, h4⟩ := (mass_eq_iff H _ _ _ _ _ _ _ _ _ _).mp hm
  funext i
  fin_cases i <;> assumption

theorem massMap_range_finrank : Module.finrank ℂ (massMap H).range = 5 := by
  simpa using LinearMap.finrank_range_of_inj (massMap_injective H)

theorem mass_form_zero_iff (a b u v w : ℂ) :
    (mass H a b u v w).form = 0 ↔ a = 0 ∧ b = 0 ∧ u = 0 ∧ v = 0 ∧ w = 0 := by
  constructor
  · intro h
    have hp := probe_values H a b u v w
    rw [h] at hp
    simpa only [LinearMap.zero_apply, eq_comm] using hp
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    simp [mass_formula]

theorem range_realized (B : LinearMap.BilinForm ℂ UV) (hB : B ∈ (massMap H).range) :
    ∃ Y : EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho,
      Y.toLinearMap (StandardSMUVYukawa.vacuum H) = B := by
  obtain ⟨c, rfl⟩ := hB
  refine ⟨coupling (c 0) (c 1) (c 2) (c 3) (c 4), ?_⟩
  exact (ProjectedYukawa.zeroBare_form (coupling (c 0) (c 1) (c 2) (c 3) (c 4))
    (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
    (StandardSMUVYukawa.vacuum_fixed H)).symm

end
end GUT.SU6FiveCouplings

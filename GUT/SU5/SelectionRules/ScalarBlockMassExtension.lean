import GUT.SU5.SelectionRules.ScalarBlockQque
import Physics.FieldTheory.Mass.Algebra.OrthogonalMass

open Physics

/-! A bounded nonzero-mass control: add one actual ten/dual-ten pair to
scalar/block chiral matter. The orthogonal mass retains precisely the chiral
carrier when the heavy pair has nonzero mass. No mixing classification. -/
namespace GUT.SU5.ScalarBlockMassExtension
set_option autoImplicit false
noncomputable section
open Math Representation InvariantWeylMass StandardModelEmbedding Matter
open ScalarBlockQque
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup UV := inferInstance
variable {H : Type*} [CommGroup H] (S : Input H)

def heavyRho : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Ten :=
  (ten.comp hom).comp (MonoidHom.fst _ _)

abbrev Extended := UV × (Ten × Module.Dual ℂ Ten)

def mass (c : ℂ) := OrthogonalMass.prod
  (SymmetricMass.zero (joint S)) (OrthogonalMass.pair (heavyRho (H := H)) c)

theorem mass_apply (c : ℂ) (x y : Extended) :
    (mass S c).form x y = c * (y.2.2 x.2.1 + x.2.2 y.2.1) := by
  simp [mass, OrthogonalMass.prod_apply, OrthogonalMass.pair_apply, SymmetricMass.zero]

theorem retained_light (c : ℂ) (x : UV) :
    (x, 0) ∈ (mass S c).radical.toSubmodule := by
  unfold mass
  rw [OrthogonalMass.mem_radical]
  constructor
  · rw [SymmetricMass.mem_radical]; intro y; rfl
  · exact Submodule.zero_mem _

theorem radical_finrank (c : ℂ) :
    Module.finrank ℂ (mass S c).radical.toSubmodule =
      15 + if c = 0 then 20 else 0 := by
  unfold mass
  rw [OrthogonalMass.finrank_prod,
    (SymmetricMass.zeroRadicalEquiv (joint S)).toLinearEquiv.finrank_eq,
    OrthogonalMass.pair_radical]
  simp [UV, Module.finrank_prod, Nat.choose]

theorem mass_nonzero (c : ℂ) (hc : c ≠ 0) : (mass S c).form ≠ 0 := by
  have hn : Nontrivial Ten := Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [Nat.choose])
  obtain ⟨x, hx⟩ := exists_ne (0 : Ten)
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  intro hz
  have he := LinearMap.congr_fun (LinearMap.congr_fun hz
    ((0 : UV), (x, 0))) ((0 : UV), (0, phi))
  rw [mass_apply] at he
  simp [hphi] at he
  exact hc he

/-- The original participating ranges inject into actual extended zero
modes. The physical coefficient remains on those typed participating fields. -/
theorem exists_retained_exterior (c : ℂ) :
    (∀ x : QuarkSpace, (x.val, 0) ∈ (mass S c).radical.toSubmodule) ∧
    (∀ x : UpSpace, (x.val, 0) ∈ (mass S c).radical.toSubmodule) ∧
    (∀ x : ElectronSpace, (x.val, 0) ∈ (mass S c).radical.toSubmodule) ∧
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho S)
      (upLeftRho S).dual (electronLeftRho S).dual, f ≠ 0 :=
  ⟨fun x => retained_light S c x.val, fun x => retained_light S c x.val,
    fun x => retained_light S c x.val, exists_actual_exterior S⟩

end
end GUT.SU5.ScalarBlockMassExtension

import Physics.StandardModel.Gauge.StandardSMIrreducibility
import Math.RepresentationTheory.Multiplicity.FiniteSpectrum
import Math.LieGroups.Torus.CircleHomLattice

open Math

/-! An exact SM spectrum forgetting the residual action. Its equivalence is
only SM-equivariant: no residual target or generation action is supplied. -/

namespace GUT.ExactSMSpectrum
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor FiniteSpectrum

abbrev Generation := Quark × (Module.Dual ℂ Color ×
  (Module.Dual ℂ Color × (Weak × Module.Dual ℂ ℂ)))

abbrev generation : Representation ℂ GaugeGroup Generation :=
  quark.prod (upRight.dual.prod (downRight.dual.prod (lepton.prod electronRight.dual)))

abbrev Space (n s : ℕ) := (Fin n → Generation) × (Fin s → ℂ)

abbrev action (n s : ℕ) : Representation ℂ GaugeGroup (Space n s) :=
  (copies n generation).prod (Representation.trivial ℂ GaugeGroup (Fin s → ℂ))

def HasSpectrum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (n s : ℕ) : Prop :=
  Nonempty (Representation.Equiv rho (action n s))

def HasHypercharge {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (y : ℤ) : Prop :=
  ∀ (z : Circle) (v : V), rho (1, 1, z) v = ((z ^ y : Circle) : ℂ) • v

theorem hypercharge_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ GaugeGroup V} {y : ℤ}
    (hy : HasHypercharge rho y) : HasHypercharge rho.dual (-y) := by
  intro z f
  ext v
  change f (rho (1, 1, z)⁻¹ v) = (((z ^ (-y) : Circle) : ℂ) • f) v
  simp only [Prod.inv_mk, inv_one]
  rw [hy z⁻¹ v, map_smul]
  simp only [LinearMap.smul_apply, inv_zpow, zpow_neg]

@[simp] private theorem coeHom_apply (z : Circle) : Circle.coeHom z = (z : ℂ) := rfl

theorem quark_hypercharge : HasHypercharge quark 1 := by
  intro z v
  simp [quark, twist, phase, color, weak, Representation.tprod_apply]

theorem upRight_hypercharge : HasHypercharge upRight 4 := by
  intro z v
  simp [upRight, twist, phase, color]

theorem downRight_hypercharge : HasHypercharge downRight (-2) := by
  intro z v
  simp [downRight, twist, phase, color]

theorem lepton_hypercharge : HasHypercharge lepton (-3) := by
  intro z v
  simp [lepton, twist, phase, weak]

theorem electronRight_hypercharge : HasHypercharge electronRight (-6) := by
  intro z v
  simp [electronRight, twist, phase, Representation.trivial]

theorem trivial_hypercharge (V : Type*) [AddCommGroup V] [Module ℂ V] :
    HasHypercharge (Representation.trivial ℂ GaugeGroup V) 0 := by
  intro z v
  simp [Representation.trivial]

theorem intertwiner_eq_zero_of_hypercharge_ne
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ GaugeGroup V} {sigma : Representation ℂ GaugeGroup W}
    {a b : ℤ} (hr : HasHypercharge rho a) (hs : HasHypercharge sigma b)
    (hab : a ≠ b) (f : IntertwiningMap rho sigma) : f = 0 := by
  have hn : ∃ z : Circle, ((z ^ a : Circle) : ℂ) ≠ ((z ^ b : Circle) : ℂ) := by
    by_contra h
    push Not at h
    apply hab
    apply CircleHomLattice.circlePowerHom_injective
    ext z
    exact h z
  obtain ⟨z, hz⟩ := hn
  exact intertwiner_eq_zero_of_scalar rho sigma (1, 1, z) _ _ (hr z) (hs z) hz f

theorem hom_finrank_zero_of_hypercharge_ne
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ GaugeGroup V} {sigma : Representation ℂ GaugeGroup W}
    {a b : ℤ} (hr : HasHypercharge rho a) (hs : HasHypercharge sigma b)
    (hab : a ≠ b) : Module.finrank ℂ (IntertwiningMap rho sigma) = 0 := by
  let : Subsingleton (IntertwiningMap rho sigma) :=
    ⟨fun f g => (intertwiner_eq_zero_of_hypercharge_ne hr hs hab f).trans
      (intertwiner_eq_zero_of_hypercharge_ne hr hs hab g).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem upLeft_hypercharge : HasHypercharge upRight.dual (-4) :=
  hypercharge_dual upRight_hypercharge

theorem downLeft_hypercharge : HasHypercharge downRight.dual 2 :=
  hypercharge_dual downRight_hypercharge

theorem electronLeft_hypercharge : HasHypercharge electronRight.dual 6 :=
  hypercharge_dual electronRight_hypercharge

theorem quark_generation : Module.finrank ℂ (IntertwiningMap quark generation) = 1 := by
  let : IsIrreducible quark := StandardSMIrreducibility.quark_irreducible
  simp only [generation, hom_finrank_prod]
  rw [IsIrreducible.finrank_intertwiningMap_self,
    hom_finrank_zero_of_hypercharge_ne quark_hypercharge upLeft_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne quark_hypercharge downLeft_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne quark_hypercharge lepton_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne quark_hypercharge electronLeft_hypercharge (by decide)]

theorem up_generation : Module.finrank ℂ (IntertwiningMap upRight.dual generation) = 1 := by
  let : IsIrreducible upRight.dual := StandardSMIrreducibility.upLeft_irreducible
  simp only [generation, hom_finrank_prod]
  rw [IsIrreducible.finrank_intertwiningMap_self,
    hom_finrank_zero_of_hypercharge_ne upLeft_hypercharge quark_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne upLeft_hypercharge downLeft_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne upLeft_hypercharge lepton_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne upLeft_hypercharge electronLeft_hypercharge (by decide)]

theorem electron_generation :
    Module.finrank ℂ (IntertwiningMap electronRight.dual generation) = 1 := by
  let : IsIrreducible electronRight.dual := StandardSMIrreducibility.electronLeft_irreducible
  simp only [generation, hom_finrank_prod]
  rw [IsIrreducible.finrank_intertwiningMap_self,
    hom_finrank_zero_of_hypercharge_ne electronLeft_hypercharge quark_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne electronLeft_hypercharge upLeft_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne electronLeft_hypercharge downLeft_hypercharge (by decide),
    hom_finrank_zero_of_hypercharge_ne electronLeft_hypercharge lepton_hypercharge (by decide)]

theorem hom_generation_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {rho : Representation ℂ GaugeGroup V} {y : ℤ}
    (hy : HasHypercharge rho y)
    (hq : y ≠ 1) (hu : y ≠ -4) (hd : y ≠ 2) (hl : y ≠ -3) (he : y ≠ 6) :
    Module.finrank ℂ (IntertwiningMap rho generation) = 0 := by
  simp only [generation, hom_finrank_prod]
  rw [hom_finrank_zero_of_hypercharge_ne hy quark_hypercharge hq,
    hom_finrank_zero_of_hypercharge_ne hy upLeft_hypercharge hu,
    hom_finrank_zero_of_hypercharge_ne hy downLeft_hypercharge hd,
    hom_finrank_zero_of_hypercharge_ne hy lepton_hypercharge hl,
    hom_finrank_zero_of_hypercharge_ne hy electronLeft_hypercharge he]

theorem hom_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {rho : Representation ℂ GaugeGroup V} {y : ℤ}
    (hy : HasHypercharge rho y) (hy0 : y ≠ 0) (n s : ℕ) :
    Module.finrank ℂ (IntertwiningMap rho (action n s)) =
      n * Module.finrank ℂ (IntertwiningMap rho generation) := by
  rw [action, hom_finrank_prod, hom_finrank_copies,
    hom_finrank_zero_of_hypercharge_ne hy (trivial_hypercharge _) hy0, add_zero]

theorem hom_exact {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {rho : Representation ℂ GaugeGroup V} {r : Representation ℂ GaugeGroup W}
    {n s : ℕ} (h : HasSpectrum rho n s) {y : ℤ}
    (hy : HasHypercharge r y) (hy0 : y ≠ 0) :
    Module.finrank ℂ (IntertwiningMap r rho) =
      n * Module.finrank ℂ (IntertwiningMap r generation) := by
  obtain ⟨e⟩ := h
  rw [(homCongrRight r e).finrank_eq, hom_action hy hy0]

theorem exact_species_multiplicities {V : Type*} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ GaugeGroup V} {n s : ℕ} (h : HasSpectrum rho n s) :
    Module.finrank ℂ (IntertwiningMap quark rho) = n ∧
    Module.finrank ℂ (IntertwiningMap upRight.dual rho) = n ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual rho) = n := by
  simp only [hom_exact h quark_hypercharge (by decide),
    hom_exact h upLeft_hypercharge (by decide),
    hom_exact h electronLeft_hypercharge (by decide),
    quark_generation, up_generation, electron_generation, mul_one, and_self]

theorem exact_opposite_multiplicities {V : Type*} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ GaugeGroup V} {n s : ℕ} (h : HasSpectrum rho n s) :
    Module.finrank ℂ (IntertwiningMap quark.dual rho) = 0 ∧
    Module.finrank ℂ (IntertwiningMap upRight.dual.dual rho) = 0 ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual.dual rho) = 0 := by
  have hq := hypercharge_dual quark_hypercharge
  have hu := hypercharge_dual upLeft_hypercharge
  have he := hypercharge_dual electronLeft_hypercharge
  rw [hom_exact h hq (by decide), hom_exact h hu (by decide), hom_exact h he (by decide),
    hom_generation_zero hq (by decide) (by decide) (by decide) (by decide) (by decide),
    hom_generation_zero hu (by decide) (by decide) (by decide) (by decide) (by decide),
    hom_generation_zero he (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp

end
end GUT.ExactSMSpectrum

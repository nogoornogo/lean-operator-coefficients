import GUT.SU5.Branching.FortyElectronExclusion
import Physics.FieldTheory.Mass.HomSurplusMass

namespace GUT.SU5.ActualExoticMassBounds
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor InvariantMassNormalForm
open FortyHyperchargeExclusion ExoticHyperchargeBasis InvariantWeylMass
open BipartiteNormalForm HomSurplusMass
local instance : AddCommGroup Matter.Ten := inferInstance
local instance : AddCommGroup Kernel := inferInstance
local instance : Module ℂ Kernel := inferInstance
local instance : AddCommGroup Fifty := inferInstance
local instance : Module ℂ Fifty := inferInstance

abbrev Source (p s : ℕ) := (Fin p → Module.Dual ℂ Kernel) × (Fin s → Fifty)
def source (p s : ℕ) : Representation ℂ GaugeGroup (Source p s) :=
  (FiniteSpectrum.copies p forty).prod (FiniteSpectrum.copies s fifty)
abbrev Fields (p s q t : ℕ) := Source p s × Module.Dual ℂ (Source q t)
local instance (p s : ℕ) : FiniteDimensional ℂ (Source p s) := inferInstance
local instance (p s q t : ℕ) : FiniteDimensional ℂ (Fields p s q t) := inferInstance
def fields (p s q t : ℕ) : Representation ℂ GaugeGroup (Fields p s q t) :=
  (source p s).prod (source q t).dual

theorem source_no_pairings (p s : ℕ) :
    NoPairings quark (source p s) ∧
    NoPairings upRight.dual (source p s) ∧
    NoPairings electronRight.dual (source p s) := by
  have h40 := FortyHyperchargeExclusion.selected_no_pairings
  have h50 := ExoticHyperchargeBasis.selected_no_pairings
  exact ⟨prod_right (copies_right h40.1 p) (copies_right h50.1 s),
    prod_right (copies_right h40.2.1 p) (copies_right h50.2.1 s),
    prod_right (copies_right h40.2.2 p) (copies_right h50.2.2 s)⟩

abbrev qMultiplicity := Module.finrank ℂ (IntertwiningMap quark forty)
abbrev uMultiplicity := Module.finrank ℂ (IntertwiningMap upRight.dual forty)

theorem source_q_multiplicity (p s : ℕ) :
    Module.finrank ℂ (IntertwiningMap quark (source p s)) = p * qMultiplicity := by
  rw [source, FiniteSpectrum.hom_finrank_prod, FiniteSpectrum.hom_finrank_copies,
    FiniteSpectrum.hom_finrank_copies,
    fifty_hom_finrank_zero quark 1 quark_hypercharge (by decide), mul_zero, add_zero]

theorem source_u_multiplicity (p s : ℕ) :
    Module.finrank ℂ (IntertwiningMap upRight.dual (source p s)) = p * uMultiplicity := by
  rw [source, FiniteSpectrum.hom_finrank_prod, FiniteSpectrum.hom_finrank_copies,
    FiniteSpectrum.hom_finrank_copies,
    fifty_hom_finrank_zero upRight.dual (-4) upLeft_hypercharge (by decide), mul_zero, add_zero]

theorem source_e_multiplicity (p s : ℕ) :
    Module.finrank ℂ (IntertwiningMap electronRight.dual (source p s)) = 0 := by
  rw [source, FiniteSpectrum.hom_finrank_prod, FiniteSpectrum.hom_finrank_copies,
    FiniteSpectrum.hom_finrank_copies, FortyElectronExclusion.electron_multiplicity_zero,
    fifty_hom_finrank_zero electronRight.dual 6 electronLeft_hypercharge (by decide)]
  simp

theorem field_q_multiplicity (p s q t : ℕ) :
    Module.finrank ℂ (IntertwiningMap quark (fields p s q t)) = p * qMultiplicity :=
  (source_multiplicity quark (source p s) (source q t) (source_no_pairings q t).1).trans
    (source_q_multiplicity p s)

theorem mass_target_q_multiplicity (p s q t : ℕ) :
    Module.finrank ℂ (IntertwiningMap quark (fields p s q t).dual) = q * qMultiplicity :=
  (target_multiplicity quark (source p s) (source q t) (source_no_pairings p s).1).trans
    (source_q_multiplicity q t)

theorem field_u_multiplicity (p s q t : ℕ) :
    Module.finrank ℂ (IntertwiningMap upRight.dual (fields p s q t)) = p * uMultiplicity :=
  (source_multiplicity upRight.dual (source p s) (source q t) (source_no_pairings q t).2.1).trans
    (source_u_multiplicity p s)

theorem mass_target_u_multiplicity (p s q t : ℕ) :
    Module.finrank ℂ (IntertwiningMap upRight.dual (fields p s q t).dual) = q * uMultiplicity :=
  (target_multiplicity upRight.dual (source p s) (source q t) (source_no_pairings p s).2.1).trans
    (source_u_multiplicity q t)

theorem arbitrary_mass_lower_bounds (p s q t : ℕ) (B : SymmetricMass (fields p s q t)) :
    (p-q) * qMultiplicity ≤ Module.finrank ℂ (IntertwiningMap quark B.radical.toRepresentation) ∧
    (p-q) * uMultiplicity ≤ Module.finrank ℂ (IntertwiningMap upRight.dual B.radical.toRepresentation) := by
  have hq := radical_multiplicity_bound quark (fields p s q t) B
  have hu := radical_multiplicity_bound upRight.dual (fields p s q t) B
  have hq' : p * qMultiplicity ≤ q * qMultiplicity +
      Module.finrank ℂ (IntertwiningMap quark B.radical.toRepresentation) :=
    (field_q_multiplicity p s q t).symm.trans_le (hq.trans_eq
      (congrArg (fun n => n + Module.finrank ℂ (IntertwiningMap quark B.radical.toRepresentation))
        (mass_target_q_multiplicity p s q t)))
  have hu' : p * uMultiplicity ≤ q * uMultiplicity +
      Module.finrank ℂ (IntertwiningMap upRight.dual B.radical.toRepresentation) :=
    (field_u_multiplicity p s q t).symm.trans_le (hu.trans_eq
      (congrArg (fun n => n + Module.finrank ℂ (IntertwiningMap upRight.dual B.radical.toRepresentation))
        (mass_target_u_multiplicity p s q t)))
  simp only [Nat.sub_mul]
  constructor <;> omega

theorem field_e_multiplicity (p s q t : ℕ) :
    Module.finrank ℂ (IntertwiningMap electronRight.dual (fields p s q t)) = 0 :=
  (source_multiplicity electronRight.dual (source p s) (source q t)
    (source_no_pairings q t).2.2).trans (source_e_multiplicity p s)

theorem arbitrary_mass_q_u_survive (p s q t : ℕ) (hp : q < p)
    (B : SymmetricMass (fields p s q t)) :
    (∃ f : IntertwiningMap quark B.radical.toRepresentation, f ≠ 0) ∧
    (∃ f : IntertwiningMap upRight.dual B.radical.toRepresentation, f ≠ 0) := by
  have hm := FortySelectedCopies.selected_positive_multiplicities
  constructor
  · apply arbitrary_mass_survival quark (source p s) (source q t)
      (source_no_pairings p s).1 (source_no_pairings q t).1
    rw [source_q_multiplicity, source_q_multiplicity]
    exact Nat.mul_lt_mul_of_pos_right hp hm.1
  · apply arbitrary_mass_survival upRight.dual (source p s) (source q t)
      (source_no_pairings p s).2.1 (source_no_pairings q t).2.1
    rw [source_u_multiplicity, source_u_multiplicity]
    exact Nat.mul_lt_mul_of_pos_right hp hm.2

theorem arbitrary_mass_no_electron (p s q t : ℕ)
    (B : SymmetricMass (fields p s q t))
    (f : IntertwiningMap electronRight.dual B.radical.toRepresentation) : f = 0 := by
  apply radical_hom_zero electronRight.dual (fields p s q t) B _ f
  intro g
  have hs := (Module.finrank_zero_iff.mp (field_e_multiplicity p s q t))
  exact hs.elim g 0

theorem no_light_q_necessary (p s q t : ℕ) (B : SymmetricMass (fields p s q t))
    (hz : ∀ f : IntertwiningMap quark B.radical.toRepresentation, f = 0) : p ≤ q := by
  by_contra hn
  obtain ⟨⟨f,hf⟩,_⟩ := arbitrary_mass_q_u_survive p s q t (lt_of_not_ge hn) B
  exact hf (hz f)

theorem no_light_u_necessary (p s q t : ℕ) (B : SymmetricMass (fields p s q t))
    (hz : ∀ f : IntertwiningMap upRight.dual B.radical.toRepresentation, f = 0) : p ≤ q := by
  by_contra hn
  obtain ⟨_,f,hf⟩ := arbitrary_mass_q_u_survive p s q t (lt_of_not_ge hn) B
  exact hf (hz f)

open SMEpsilonTensor in
abbrev SMGeneration := Module.Dual ℂ Color × (Quark ×
  (Module.Dual ℂ ℂ × (Module.Dual ℂ Color × Weak)))
def smGeneration : Representation ℂ GaugeGroup SMGeneration :=
  upRight.dual.prod (quark.prod (electronRight.dual.prod (downRight.dual.prod lepton)))

def smElectron : IntertwiningMap electronRight.dual smGeneration :=
  (IntertwiningMap.inr ℂ upRight.dual
    (quark.prod (electronRight.dual.prod (downRight.dual.prod lepton)))).comp
      ((IntertwiningMap.inr ℂ quark (electronRight.dual.prod (downRight.dual.prod lepton))).comp
        (IntertwiningMap.inl ℂ electronRight.dual (downRight.dual.prod lepton)))

/-- The full standard five-species generation target, not a charge-only index.
All copy counts and the full original symmetric mass are arbitrary. -/
theorem no_exact_sm_light (p s q t N : ℕ) (hN : 0 < N)
    (B : SymmetricMass (fields p s q t)) :
    ¬ Nonempty (Representation.Equiv B.radical.toRepresentation
      (FiniteSpectrum.copies N smGeneration)) := by
  rintro ⟨e⟩
  let i : Fin N := ⟨0,hN⟩
  let ef : IntertwiningMap electronRight.dual (FiniteSpectrum.copies N smGeneration) :=
    (copySlot N smGeneration i).comp smElectron
  let f : IntertwiningMap electronRight.dual B.radical.toRepresentation :=
    e.symm.toIntertwiningMap.comp ef
  have hz := arbitrary_mass_no_electron p s q t B f
  have he := congrArg (fun k : IntertwiningMap electronRight.dual B.radical.toRepresentation =>
    e (k (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) hz
  change e (e.symm (copySlot N smGeneration i (smElectron LinearMap.id))) = e 0 at he
  have hc (v : Fin N → SMGeneration) : e (e.symm v) = v :=
    e.toLinearEquiv.apply_symm_apply v
  have hzero : e 0 = 0 := e.toLinearEquiv.map_zero
  have hr : copySlot N smGeneration i (smElectron LinearMap.id) = 0 :=
    (hc _).symm.trans (he.trans hzero)
  have ht := congrArg (fun v : Fin N → SMGeneration => (v i).2.2.1 1) hr
  change ((Pi.single i (0,(0,(LinearMap.id,(0,0)))) : Fin N → SMGeneration) i).2.2.1 1 = 0 at ht
  simp at ht

end
end GUT.SU5.ActualExoticMassBounds

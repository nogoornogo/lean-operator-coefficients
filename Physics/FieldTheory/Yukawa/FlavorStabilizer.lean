import Math.RepresentationTheory.FamilyStabilizer
import Physics.FieldTheory.Yukawa.SymmetricScalarYukawa

open Math

/-! Specified coupling and mass stabilizers; candidate flavor actions are inputs,
not asserted to be symmetries of the coupling before its stabilizer is taken. -/
namespace GUT.FlavorStabilizer
set_option autoImplicit false
noncomputable section
variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup V] [Module ℂ V]
variable (a : Representation ℂ G S) (b : Representation ℂ G V)

def formAction : Representation ℂ G (LinearMap.BilinForm ℂ V) := b.linHom b.dual
def couplingAction : Representation ℂ G (S →ₗ[ℂ] LinearMap.BilinForm ℂ V) :=
  a.linHom (formAction b)

def massSubgroup (B : LinearMap.BilinForm ℂ V) : Subgroup G :=
  FamilyStabilizer.subgroup (formAction b) (fun _ : Unit => B)

def couplingSubgroup (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) : Subgroup G :=
  FamilyStabilizer.subgroup (couplingAction a b) (fun _ : Unit => Y)

def vacuumSubgroup (v : S) : Subgroup G :=
  FamilyStabilizer.subgroup a (fun _ : Unit => v)

theorem mass_mem_iff (B : LinearMap.BilinForm ℂ V) (g : G) :
    g ∈ massSubgroup b B ↔ ∀ x y, B (b g x) (b g y) = B x y := by
  change (∀ _ : Unit, formAction b g B = B) ↔ _
  constructor
  · intro h x y
    have he := congrArg (fun C : LinearMap.BilinForm ℂ V => C (b g x) (b g y)) (h ())
    change B (b g⁻¹ (b g x)) (b g⁻¹ (b g y)) = B (b g x) (b g y) at he
    simpa using he.symm
  · intro h _
    ext x y
    exact (h (b g⁻¹ x) (b g⁻¹ y)).symm.trans (by simp)

theorem coupling_mem_iff (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (g : G) :
    g ∈ couplingSubgroup a b Y ↔
      ∀ s x y, Y (a g s) (b g x) (b g y) = Y s x y := by
  change (∀ _ : Unit, couplingAction a b g Y = Y) ↔ _
  constructor
  · intro h s x y
    have he := congrArg (fun T : S →ₗ[ℂ] LinearMap.BilinForm ℂ V =>
      T (a g s) (b g x) (b g y)) (h ())
    change Y (a g⁻¹ (a g s)) (b g⁻¹ (b g x)) (b g⁻¹ (b g y)) =
      Y (a g s) (b g x) (b g y) at he
    simpa using he.symm
  · intro h _
    ext s x y
    exact (h (a g⁻¹ s) (b g⁻¹ x) (b g⁻¹ y)).symm.trans (by simp)

def fullSubgroup (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : S) : Subgroup G :=
  couplingSubgroup a b Y ⊓ vacuumSubgroup a v

theorem full_le_mass (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : S) :
    fullSubgroup a b Y v ≤ massSubgroup b (Y v) := by
  intro g hg
  apply (mass_mem_iff b (Y v) g).mpr
  have hv : a g v = v := hg.2 ()
  intro x y
  have he := (coupling_mem_iff a b Y g).mp hg.1 v x y
  rwa [hv] at he

/-- Orbit discrepancy: evaluation can hide a nonzero change of the coupling. -/
def defect (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (g : G) :
    S →ₗ[ℂ] LinearMap.BilinForm ℂ V := couplingAction a b g Y - Y

theorem defect_zero_iff (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (g : G) :
    defect a b Y g = 0 ↔ g ∈ couplingSubgroup a b Y := by
  change couplingAction a b g Y - Y = 0 ↔ ∀ _ : Unit, couplingAction a b g Y = Y
  exact ⟨fun h _ => sub_eq_zero.mp h, fun h => sub_eq_zero.mpr (h ())⟩

theorem mass_iff_defect_at_vacuum (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (v : S) (g : G) (hv : g ∈ vacuumSubgroup a v) :
    g ∈ massSubgroup b (Y v) ↔ defect a b Y g v = 0 := by
  have hvi : a g⁻¹ v = v := (vacuumSubgroup a v).inv_mem hv ()
  change (∀ _ : Unit, formAction b g (Y v) = Y v) ↔ _
  simp only [defect, LinearMap.sub_apply, sub_eq_zero, couplingAction,
    Representation.linHom_apply, LinearMap.comp_apply, hvi]
  exact ⟨fun h => h (), fun h _ => h⟩

/-- Exact obstruction to equality, on the vacuum-fixing candidate subgroup. -/
theorem equality_iff_no_hidden_defect (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : S) :
    fullSubgroup a b Y v = massSubgroup b (Y v) ⊓ vacuumSubgroup a v ↔
      ∀ g ∈ vacuumSubgroup a v, defect a b Y g v = 0 → defect a b Y g = 0 := by
  constructor
  · intro h g hv hd
    have hm := (mass_iff_defect_at_vacuum a b Y v g hv).mpr hd
    have hf : g ∈ fullSubgroup a b Y v := by rw [h]; exact ⟨hm, hv⟩
    exact (defect_zero_iff a b Y g).mpr hf.1
  · intro h
    apply le_antisymm
    · exact fun g hg => ⟨full_le_mass a b Y v hg, hg.2⟩
    · intro g hg
      exact ⟨(defect_zero_iff a b Y g).mp
        (h g hg.2 ((mass_iff_defect_at_vacuum a b Y v g hg.2).mp hg.1)), hg.2⟩

/-- A generating family of scalar values determines the entire coupling defect. -/
theorem defect_zero_of_generators (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (g : G) (T : Set S) (hspan : Submodule.span ℂ T = ⊤)
    (h : ∀ s ∈ T, defect a b Y g s = 0) : defect a b Y g = 0 := by
  apply LinearMap.ext
  intro s
  have hs : s ∈ Submodule.span ℂ T := by rw [hspan]; trivial
  exact Submodule.span_induction h (by simp) (by
    intro x y _ _ hx hy
    simp [hx, hy]) (by
    intro c x _ hx
    simp [hx]) hs

theorem coupling_of_generating_masses (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (g : G) (T : Set S) (hspan : Submodule.span ℂ T = ⊤)
    (hv : ∀ s ∈ T, a g s = s) (hm : ∀ s ∈ T, g ∈ massSubgroup b (Y s)) :
    g ∈ couplingSubgroup a b Y := by
  apply (defect_zero_iff a b Y g).mp
  apply defect_zero_of_generators a b Y g T hspan
  intro s hs
  exact (mass_iff_defect_at_vacuum a b Y s g (fun _ => hv s hs)).mp (hm s hs)

/-- Simultaneously preserve an arbitrary specified family of couplings,
scalar VEVs and bare forms. Empty families impose no constraints. -/
def dataSubgroup {P Q R : Type*}
    (Y : P → S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : Q → S)
    (B : R → LinearMap.BilinForm ℂ V) : Subgroup G :=
  FamilyStabilizer.subgroup (couplingAction a b) Y ⊓
    (FamilyStabilizer.subgroup a v ⊓ FamilyStabilizer.subgroup (formAction b) B)

theorem data_mem_iff {P Q R : Type*}
    (Y : P → S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : Q → S)
    (B : R → LinearMap.BilinForm ℂ V) (g : G) :
    g ∈ dataSubgroup a b Y v B ↔
      (∀ p, g ∈ couplingSubgroup a b (Y p)) ∧
      (∀ q, a g (v q) = v q) ∧ (∀ r, g ∈ massSubgroup b (B r)) := by
  constructor
  · intro h
    exact ⟨fun p _ => h.1 p, h.2.1, fun r _ => h.2.2 r⟩
  · rintro ⟨hY, hv, hB⟩
    exact ⟨fun p => hY p (), hv, fun r => hB r ()⟩

def restrictedYukawa (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (hY : ∀ s, (Y s).IsSymm) (v : S) :
    WeylYukawaMass.EquivariantYukawa
      (a.comp (fullSubgroup a b Y v).subtype) (b.comp (fullSubgroup a b Y v).subtype) where
  toLinearMap := Y
  symmetric := hY
  invariant g := (coupling_mem_iff a b Y g.val).mp g.property.1

def restrictedVacuum (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : S) :
    DiracYukawaMass.InvariantVacuum (a.comp (fullSubgroup a b Y v).subtype) :=
  ⟨v, fun g => g.property.2 ()⟩

/-- Connect the derived stabilizer to the existing Yukawa-sector mass API. -/
def sector (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (hY : ∀ s, (Y s).IsSymm) (v : S) :
    WeylYukawaMass.Sector
      (a.comp (fullSubgroup a b Y v).subtype) (b.comp (fullSubgroup a b Y v).subtype) where
  bareMass := InvariantWeylMass.SymmetricMass.zero _
  yukawa := restrictedYukawa a b Y hY v
  vacuum := restrictedVacuum a b Y v

@[simp] theorem sector_mass (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (hY : ∀ s, (Y s).IsSymm) (v : S) : (sector a b Y hY v).mass.form = Y v := by
  ext x y
  simp [sector, WeylYukawaMass.Sector.mass, InvariantWeylMass.SymmetricMass.zero,
    restrictedYukawa, restrictedVacuum]

def residualHomEquiv {U W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W]
    (Y : S →ₗ[ℂ] LinearMap.BilinForm ℂ V) (v : S)
    (d : Representation ℂ G U) (c : Representation ℂ G W) :
    (Representation.linHom (d.comp (fullSubgroup a b Y v).subtype)
      (c.comp (fullSubgroup a b Y v).subtype)).invariants ≃ₗ[ℂ]
      Representation.IntertwiningMap (d.comp (fullSubgroup a b Y v).subtype)
        (c.comp (fullSubgroup a b Y v).subtype) :=
  Representation.invariantsEquivIntertwiningMap _ _

end
end GUT.FlavorStabilizer

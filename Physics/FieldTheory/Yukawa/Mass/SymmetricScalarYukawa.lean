import Physics.FieldTheory.Yukawa.Mass.WeylYukawaMass

/-!
# A universal scalar representation for symmetric mass coefficients

Symmetric bilinear forms carry the pullback action of the full ambient
group. Evaluation is a single, mass-independent equivariant Yukawa family.
Any invariant symmetric mass on a restricted representation is recovered
at its corresponding scalar vacuum, with zero bare mass. This constructs
an algebraic UV completion, not a potential or a dynamically selected VEV.
-/

set_option autoImplicit false

namespace Physics.SymmetricScalarYukawa

noncomputable section

open InvariantWeylMass WeylYukawaMass

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
variable (rho : Representation ℂ G V)

def bilinRho : Representation ℂ G (LinearMap.BilinForm ℂ V) := rho.linHom rho.dual

@[simp] theorem bilinRho_apply (g : G) (B : LinearMap.BilinForm ℂ V) (x y : V) :
    bilinRho rho g B x y = B (rho g⁻¹ x) (rho g⁻¹ y) := rfl

def symmetricForms : Subrepresentation (bilinRho rho) where
  toSubmodule :=
    { carrier := {B | B.IsSymm}
      zero_mem' := LinearMap.BilinForm.isSymm_zero
      add_mem' := fun hB hC => hB.add hC
      smul_mem' := fun c _ hB => hB.smul c }
  apply_mem_toSubmodule g _B hB := ⟨fun x y => hB.eq (rho g⁻¹ x) (rho g⁻¹ y)⟩

abbrev Scalar := (symmetricForms rho).toSubmodule

def scalarRho : Representation ℂ G (Scalar rho) := (symmetricForms rho).toRepresentation

@[simp] theorem scalarRho_apply (g : G) (s : Scalar rho) (x y : V) :
    (scalarRho rho g s).val x y = s.val (rho g⁻¹ x) (rho g⁻¹ y) := rfl

def yukawa : EquivariantYukawa (S := Scalar rho) (scalarRho rho) rho where
  toLinearMap := (symmetricForms rho).toSubmodule.subtype
  symmetric s := s.property
  invariant g s x y := by
    change s.val (rho g⁻¹ (rho g x)) (rho g⁻¹ (rho g y)) = s.val x y
    simp

@[simp] theorem yukawa_apply (s : Scalar rho) (x y : V) :
    (yukawa rho).toLinearMap s x y = s.val x y := rfl

/-- The stabilizer is exactly the subgroup preserving the bilinear form;
it is not asserted to equal any prescribed infrared gauge group. -/
theorem fixed_iff (s : Scalar rho) (g : G) :
    scalarRho rho g s = s ↔ ∀ x y, s.val (rho g x) (rho g y) = s.val x y := by
  constructor
  · intro h x y
    have he := congrArg (fun t : Scalar rho => t.val (rho g x) (rho g y)) h
    simpa using he.symm
  · intro h
    apply Subtype.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    have he := h (rho g⁻¹ x) (rho g⁻¹ y)
    simpa using he.symm

variable {K : Type*} [Group K]

def vacuum (f : K →* G) (B : SymmetricMass (rho.comp f)) : Scalar rho :=
  ⟨B.form, B.symmetric⟩

theorem vacuum_fixed (f : K →* G) (B : SymmetricMass (rho.comp f)) (k : K) :
    scalarRho rho (f k) (vacuum rho f B) = vacuum rho f B :=
  (fixed_iff rho _ _).mpr (B.invariant k)

theorem vacuum_nonzero (f : K →* G) (B : SymmetricMass (rho.comp f)) (hB : B.form ≠ 0) :
    vacuum rho f B ≠ 0 := by
  intro h
  exact hB (congrArg Subtype.val h)

def inducedMass (f : K →* G) (B : SymmetricMass (rho.comp f)) : SymmetricMass (rho.comp f) :=
  atVacuumOn (SymmetricMass.zero rho) (yukawa rho) f (vacuum rho f B) (vacuum_fixed rho f B)

theorem inducedMass_eq (f : K →* G) (B : SymmetricMass (rho.comp f)) :
    inducedMass rho f B = B := by
  cases B
  simp [inducedMass, atVacuumOn, SymmetricMass.zero, yukawa, vacuum]

end

end Physics.SymmetricScalarYukawa

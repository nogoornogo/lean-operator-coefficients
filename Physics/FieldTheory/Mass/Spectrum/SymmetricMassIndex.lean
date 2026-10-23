import Physics.FieldTheory.Mass.Algebra.InvariantMassData
import Math.RepresentationTheory.Characters.CharacterExact
import Mathlib.LinearAlgebra.Quotient.Bilinear

open Math

/-!
# Symmetric-mass dual index for arbitrary groups

The invariant massive quotient is self-dual. Exact character additivity
therefore identifies the dual character difference with that of the radical.
No norm, unitarity, semisimplicity, or ultraviolet gauge group is assumed.
-/

set_option autoImplicit false

namespace Physics.InvariantWeylMass

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

namespace SymmetricMass

variable {rho : Representation ℂ G V} (B : SymmetricMass rho)

/-- The mass coefficient transforms a field into a contragredient covector. -/
theorem form_covariant (g : G) (x y : V) :
    B.form (rho g x) y = B.form x (rho g⁻¹ y) := by
  have hy : rho g (rho g⁻¹ y) = y := by simp
  calc
    B.form (rho g x) y = B.form (rho g x) (rho g (rho g⁻¹ y)) :=
      congrArg (B.form (rho g x)) hy.symm
    _ = B.form x (rho g⁻¹ y) := B.invariant g x (rho g⁻¹ y)

def toIntertwiningMap : Representation.IntertwiningMap rho rho.dual where
  toLinearMap := B.form
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    exact B.form_covariant g x

/-- No nondegeneracy hypothesis is imposed on the original mass sector. -/
def radical : Subrepresentation rho := B.toIntertwiningMap.ker

@[simp]
theorem mem_radical (x : V) :
    x ∈ B.radical.toSubmodule ↔ ∀ y, B.form x y = 0 := by
  change B.form x = 0 ↔ _
  exact LinearMap.ext_iff

/-- With zero mass the radical is the original field representation, not
merely a space with the same character or dimension. -/
def zeroRadicalEquiv (rho : Representation ℂ G V) :
    Representation.Equiv (zero rho).radical.toRepresentation rho :=
  .mk
    { toFun := Subtype.val
      invFun := fun x => ⟨x, by change (0 : V →ₗ[ℂ] Module.Dual ℂ V) x = 0; rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by intro g; rfl)

@[simp] theorem zeroRadicalEquiv_apply (rho : Representation ℂ G V)
    (x : (zero rho).radical.toSubmodule) : zeroRadicalEquiv rho x = x.val := rfl

def quotientRepresentation :
    Representation ℂ G (V ⧸ B.radical.toSubmodule) :=
  rho.quotient B.radical.toSubmodule (fun g _ hx =>
    B.radical.apply_mem_toSubmodule g hx)

/-- The mass form descends on both arguments, using its symmetry. -/
def quotientForm : LinearMap.BilinForm ℂ (V ⧸ B.radical.toSubmodule) :=
  B.form.liftQ₂ B.radical.toSubmodule B.radical.toSubmodule le_rfl (by
    intro x hx
    apply LinearMap.ext
    intro y
    change B.form y x = 0
    rw [B.symmetric.eq]
    exact (B.mem_radical x).mp hx y)

@[simp]
theorem quotientForm_mk (x y : V) :
    B.quotientForm (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B.form x y := rfl

theorem quotientForm_symmetric : B.quotientForm.IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
      exact B.symmetric.eq x y

theorem quotientForm_invariant (g : G)
    (x y : V ⧸ B.radical.toSubmodule) :
    B.quotientForm (B.quotientRepresentation g x)
      (B.quotientRepresentation g y) = B.quotientForm x y := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
      exact B.invariant g x y

/-- After dividing out all zero modes the induced mass coefficient is
nondegenerate; this is a theorem, not an input certificate. -/
theorem quotientForm_nondegenerate : B.quotientForm.Nondegenerate := by
  have hleft : B.quotientForm.SeparatingLeft := by
    intro x hx
    induction x using Submodule.Quotient.induction_on with | _ x =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (B.mem_radical x).mpr (fun y => hx (Submodule.Quotient.mk y))
  refine ⟨hleft, ?_⟩
  intro y hy
  exact hleft y (fun x => (B.quotientForm_symmetric.eq y x).trans (hy x))

/-- Package the induced bilinear with its invariance, without assuming a
Hilbert structure or a unitary action on the quotient. -/
def quotientMass : SymmetricMass B.quotientRepresentation where
  form := B.quotientForm
  symmetric := B.quotientForm_symmetric
  invariant := B.quotientForm_invariant

/-- Any invariant complement identifies equivariantly with the quotient.
The direction used here is the canonical quotient map on the complement. -/
def complementQuotientEquiv (S : Subrepresentation rho)
    (h : IsCompl B.radical.toSubmodule S.toSubmodule) :
    Representation.Equiv S.toRepresentation B.quotientRepresentation :=
  CharacterExact.complementQuotientEquiv B.radical S h

variable [FiniteDimensional ℂ V]

/-- Massive states are self-dual as representations of the entire unbroken
group, including any finite Abelian residual group. -/
def quotientSelfDualEquiv :
    Representation.Equiv B.quotientRepresentation B.quotientRepresentation.dual :=
  .mk (B.quotientForm.toDual B.quotientForm_nondegenerate) (by
    intro g
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    exact B.quotientMass.form_covariant g x)

theorem quotient_character_eq_dual (g : G) :
    B.quotientRepresentation.character g =
      B.quotientRepresentation.dual.character g :=
  congrFun (Representation.char_iso B.quotientSelfDualEquiv) g

/-- Exact-sequence additivity and self-duality of the massive quotient
preserve the dual character difference, without an invariant inner product. -/
theorem radical_dual_character_eq (g : G) :
    B.radical.toRepresentation.character g -
        B.radical.toRepresentation.dual.character g =
      rho.character g - rho.dual.character g := by
  have hchar (a : G) : rho.character a =
      B.radical.toRepresentation.character a + B.quotientRepresentation.character a :=
    CharacterExact.character_eq_sub_add_quotient B.radical a
  have hself : B.quotientRepresentation.character g =
      B.quotientRepresentation.character g⁻¹ := by
    rw [B.quotient_character_eq_dual g, Representation.char_dual]
  rw [Representation.char_dual, Representation.char_dual, hchar g, hchar g⁻¹, hself]
  abel

omit [FiniteDimensional ℂ V] in
theorem radical_zero : (zero rho).radical.toSubmodule = ⊤ := by
  ext x
  simp [mem_radical, zero]

omit [FiniteDimensional ℂ V] in
theorem radical_eq_bot_of_nondegenerate (h : B.form.Nondegenerate) :
    B.radical.toSubmodule = ⊥ := h.ker_eq_bot

end SymmetricMass

end

end Physics.InvariantWeylMass

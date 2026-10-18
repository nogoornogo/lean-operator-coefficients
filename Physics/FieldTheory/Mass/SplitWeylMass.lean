import Physics.FieldTheory.Mass.InvariantWeylMass

/-!
# A gauge-equivariant mass with a prescribed light summand

On (L + F) + F*, the Dirac projection onto F pairs precisely the heavy
summands. The actual symmetric-mass radical is equivariantly isomorphic
to L for an arbitrary unbroken group, not merely its maximal torus.
-/

set_option autoImplicit false

namespace GUT.SplitWeylMass

noncomputable section

open InvariantWeylMass

variable {G L F : Type*} [Group G]
variable [AddCommGroup L] [Module ℂ L] [AddCommGroup F] [Module ℂ F]
variable (rhoL : Representation ℂ G L) (rhoF : Representation ℂ G F)

abbrev Fields := (L × F) × Module.Dual ℂ F

def representation : Representation ℂ G (Fields (L := L) (F := F)) :=
  (rhoL.prod rhoF).prod rhoF.dual

def mass : SymmetricMass (representation rhoL rhoF) :=
  ofDirac (Representation.IntertwiningMap.snd ℂ rhoL rhoF)

@[simp] theorem mass_apply (x y : Fields (L := L) (F := F)) :
    (mass rhoL rhoF).form x y = y.2 x.1.2 + x.2 y.1.2 := rfl

theorem mem_radical_iff (x : Fields (L := L) (F := F)) :
    x ∈ (mass rhoL rhoF).radical.toSubmodule ↔ x.1.2 = 0 ∧ x.2 = 0 := by
  change x ∈ DiracWeylConvention.radical (LinearMap.snd ℂ L F) ↔ _
  rw [DiracWeylConvention.mem_radical_iff]
  constructor
  · rintro ⟨hf, hphi⟩
    refine ⟨hf, LinearMap.ext fun f => ?_⟩
    exact hphi (0, f)
  · rintro ⟨hf, hphi⟩
    exact ⟨hf, by simp [hphi]⟩

def radicalLinearEquiv : (mass rhoL rhoF).radical.toSubmodule ≃ₗ[ℂ] L where
  toFun x := x.val.1.1
  invFun l := ⟨((l, 0), 0), (mem_radical_iff rhoL rhoF _).mpr ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨hf, hphi⟩ := (mem_radical_iff rhoL rhoF x.val).mp x.property
    exact Prod.ext (Prod.ext rfl hf.symm) hphi.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def radicalEquiv : Representation.Equiv (mass rhoL rhoF).radical.toRepresentation rhoL where
  toLinearEquiv := radicalLinearEquiv rhoL rhoF
  isIntertwining' _ := by apply LinearMap.ext; intro x; rfl

theorem radical_finrank [FiniteDimensional ℂ L] :
    Module.finrank ℂ (mass rhoL rhoF).radical.toSubmodule = Module.finrank ℂ L :=
  (radicalLinearEquiv rhoL rhoF).finrank_eq

theorem radical_character [FiniteDimensional ℂ L] (g : G) :
    (mass rhoL rhoF).radical.toRepresentation.character g = rhoL.character g :=
  congrFun (Representation.char_iso (radicalEquiv rhoL rhoF)) g

theorem mass_pair (f : F) (phi : Module.Dual ℂ F) :
    (mass rhoL rhoF).form ((0, f), 0) ((0, 0), phi) = phi f := by simp

theorem mass_nonzero (f : F) (phi : Module.Dual ℂ F) (h : phi f ≠ 0) :
    (mass rhoL rhoF).form ≠ 0 := by
  intro he
  have hz := LinearMap.congr_fun (LinearMap.congr_fun he ((0, f), 0)) ((0, 0), phi)
  exact h (by simpa using hz)

end

end GUT.SplitWeylMass

import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex

/-! A prescribed light subspace exhausts the radical iff the quotient mass is nondegenerate. -/
set_option autoImplicit false
namespace Physics.ExactRadical
noncomputable section
open InvariantWeylMass
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {rho : Representation ℂ G V} (B : SymmetricMass rho) (L : Submodule ℂ V)

def quotientForm (h : L ≤ B.radical.toSubmodule) : LinearMap.BilinForm ℂ (V ⧸ L) :=
  B.form.liftQ₂ L L h (by
    intro x hx
    apply LinearMap.ext
    intro y
    change B.form y x = 0
    rw [B.symmetric.eq]
    exact (B.mem_radical x).mp (h hx) y)

@[simp] theorem quotientForm_mk (h : L ≤ B.radical.toSubmodule) (x y : V) :
    quotientForm B L h (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B.form x y := rfl

theorem quotientForm_symmetric (h : L ≤ B.radical.toSubmodule) :
    (quotientForm B L h).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
      exact B.symmetric.eq x y

theorem nondegenerate_iff (h : L ≤ B.radical.toSubmodule) :
    (quotientForm B L h).Nondegenerate ↔ B.radical.toSubmodule = L := by
  constructor
  · intro hn
    apply le_antisymm _ h
    intro x hx
    have hz : (Submodule.Quotient.mk x : V ⧸ L) = 0 := hn.1 _ (by
      intro y
      induction y using Submodule.Quotient.induction_on with | _ y =>
        exact (B.mem_radical x).mp hx y)
    exact (Submodule.Quotient.mk_eq_zero L).mp hz
  · intro he
    have hl : (quotientForm B L h).SeparatingLeft := by
      intro x hx
      induction x using Submodule.Quotient.induction_on with | _ x =>
        apply (Submodule.Quotient.mk_eq_zero L).mpr
        rw [← he]
        exact (B.mem_radical x).mpr (fun y => hx (Submodule.Quotient.mk y))
    refine ⟨hl, ?_⟩
    intro y hy
    exact hl y (fun x => (quotientForm_symmetric B L h).eq y x |>.trans (hy x))

theorem exact_iff : B.radical.toSubmodule = L ↔
    ∃ h : L ≤ B.radical.toSubmodule, (quotientForm B L h).Nondegenerate := by
  constructor
  · intro he
    have h : L ≤ B.radical.toSubmodule := by rw [he]
    exact ⟨h, (nondegenerate_iff B L h).mpr he⟩
  · rintro ⟨h, hn⟩
    exact (nondegenerate_iff B L h).mp hn

theorem family_exists_iff {P : Type*} (F : P → SymmetricMass rho) :
    (∃ p, (F p).radical.toSubmodule = L) ↔
      ∃ p, ∃ h : L ≤ (F p).radical.toSubmodule,
        (quotientForm (F p) L h).Nondegenerate := by
  simp only [exact_iff]

end
end Physics.ExactRadical

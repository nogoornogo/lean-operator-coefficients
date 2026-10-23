import GUT.SU5.SelectionRules.ActualFullFamilyIndex
import Math.RepresentationTheory.Multiplicity.CopySumEquivalence
import Physics.FieldTheory.Mass.Surplus.ConstructedSpectatorRadical
import Physics.FieldTheory.Mass.Algebra.EquivariantWeylMassTransport

open Physics

namespace GUT.SU5.ActualFullFamilyMassExistence
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding StandardSMGaugeTensor
open ActualFullFamilyIndex SplitRepresentationProjection CopySumEquivalence InvariantWeylMass
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup FortyHyperchargeExclusion.Kernel := inferInstance
local instance : Module ℂ FortyHyperchargeExclusion.Kernel := inferInstance
local instance : AddCommGroup ExoticHyperchargeBasis.Fifty := inferInstance
local instance : Module ℂ ExoticHyperchargeBasis.Fifty := inferInstance

local instance (p : Counts) : FiniteDimensional ℂ (Source p) := inferInstance
local instance (p q : Counts) : FiniteDimensional ℂ (Fields p q) := inferInstance

def positive (q : Counts) (N : ℕ) : Counts := ![N+q 0,N+q 1,q 2,q 3]

def sourceSplit (q : Counts) (N : ℕ) :
    Representation.Equiv (source (positive q N))
      ((FiniteSpectrum.copies N smGeneration).prod (source q)) := by
  let e := prodEquiv (copiesAdd N (q 0) (ten.comp hom))
    (prodEquiv (copiesAdd N (q 1) (antifundamental.comp hom))
      (Representation.Equiv.refl ((FiniteSpectrum.copies (q 2) FortyHyperchargeExclusion.forty).prod
        (FiniteSpectrum.copies (q 3) ExoticHyperchargeBasis.fifty))))
  refine e.trans ?_
  refine Representation.Equiv.mk
    { toFun := fun x => (fun i => (x.1.1 i,x.2.1.1 i), (x.1.2,(x.2.1.2,x.2.2)))
      invFun := fun x => ((fun i => (x.1 i).1,x.2.1),
        ((fun i => (x.1 i).2,x.2.2.1),x.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ?_
  intro g
  apply LinearMap.ext
  intro x
  rfl

theorem counts_positive (p q : Counts) (N : ℕ)
    (h : (p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3) :
    p = positive q N := by
  ext i
  fin_cases i <;> simp [positive] <;> omega

theorem exists_mass_of_counts (p q : Counts) (N : ℕ)
    (h : (p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3) :
    ∃ B : SymmetricMass (fields p q),
      Nonempty (Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) := by
  have hp := counts_positive p q N h
  subst p
  let l := FiniteSpectrum.copies N smGeneration
  let s := source q
  let ef := (prodEquiv (sourceSplit q N) (Representation.Equiv.refl s.dual)).trans (assoc l s s.dual)
  let D := ConstructedSpectatorRadical.mass l s
  let B := EquivariantWeylMassTransport.pullback ef D
  exact ⟨B,⟨(EquivariantWeylMassTransport.radicalEquiv ef D).trans
    (ConstructedSpectatorRadical.radicalEquiv l s)⟩⟩

theorem exists_mass_iff (p q : Counts) (N : ℕ) :
    (∃ B : SymmetricMass (fields p q),
      Nonempty (Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration))) ↔
    (p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3 := by
  constructor
  · rintro ⟨B,⟨e⟩⟩
    exact net_constraints_of_exact_sm p q B N e
  · exact exists_mass_of_counts p q N

/-- Count consistency does not force a chosen degenerate mass to realize SM. -/
theorem zero_mass_control :
    let q : Counts := ![1,0,0,0]
    let p := positive q 1
    (∃ B : SymmetricMass (fields p q),
      Nonempty (Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies 1 smGeneration))) ∧
    ¬ Nonempty (Representation.Equiv (SymmetricMass.zero (fields p q)).radical.toRepresentation
      (FiniteSpectrum.copies 1 smGeneration)) := by
  dsimp only
  constructor
  · apply exists_mass_of_counts
    simp [positive]
  · rintro ⟨e⟩
    let q : Counts := ![1,0,0,0]
    let l := FiniteSpectrum.copies 1 smGeneration
    let s := source q
    let ef := (prodEquiv (sourceSplit q 1) (Representation.Equiv.refl s.dual)).trans (assoc l s s.dual)
    have hd := ((SymmetricMass.zeroRadicalEquiv _).symm.trans e).toLinearEquiv.finrank_eq
    rw [ef.toLinearEquiv.finrank_eq,Module.finrank_prod,Module.finrank_prod,
      Subspace.dual_finrank_eq] at hd
    have : Nontrivial Ten := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [ten_finrank]; norm_num)
    have : Nontrivial (Source q) := by
      dsimp [Source,q]
      infer_instance
    have hs : 0 < Module.finrank ℂ (Source q) := Module.finrank_pos
    omega
end
end GUT.SU5.ActualFullFamilyMassExistence

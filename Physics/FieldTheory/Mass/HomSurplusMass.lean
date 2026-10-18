import Physics.FieldTheory.Mass.BipartiteNormalForm
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.RepresentationTheory.Decomposition.SpeciesCopySurplus

/-! Selected species in arbitrary original mass radicals, without a supplied
sector presentation. Source/partner spaces need not be irreducible. -/
namespace GUT.HomSurplusMass
set_option autoImplicit false
noncomputable section
open Math Representation SplitRepresentationProjection BipartiteNormalForm InvariantWeylMass

variable {G R A C : Type*} [Group G]
  [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]
  [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  (r : Representation ℂ G R) (a : Representation ℂ G A) (c : Representation ℂ G C)

omit [FiniteDimensional ℂ R] [FiniteDimensional ℂ A] in
theorem noPairings_finrank_zero (h : NoPairings r a) :
    Module.finrank ℂ (IntertwiningMap r a.dual) = 0 := by
  have : Subsingleton (IntertwiningMap r a.dual) := ⟨fun f g => (h f).trans (h g).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem source_multiplicity (hc : NoPairings r c) :
    Module.finrank ℂ (IntertwiningMap r (a.prod c.dual)) =
      Module.finrank ℂ (IntertwiningMap r a) := by
  rw [FiniteSpectrum.hom_finrank_prod, noPairings_finrank_zero r c hc, add_zero]

theorem target_multiplicity (ha : NoPairings r a) :
    Module.finrank ℂ (IntertwiningMap r (a.prod c.dual).dual) =
      Module.finrank ℂ (IntertwiningMap r c) := by
  rw [(FiniteSpectrum.homCongrRight r (dualProdEquiv a c.dual).symm).finrank_eq,
    FiniteSpectrum.hom_finrank_prod, noPairings_finrank_zero r a ha, zero_add]
  exact (FiniteSpectrum.homCongrRight r (bidualEquiv c).symm).finrank_eq

/-- A full original mass, including arbitrary mixing among all components.
No same-side mass normal form or maximal-rank hypothesis is supplied. -/
theorem arbitrary_mass_survival (ha : NoPairings r a) (hc : NoPairings r c)
    (hd : Module.finrank ℂ (IntertwiningMap r c) <
      Module.finrank ℂ (IntertwiningMap r a))
    (B : SymmetricMass (a.prod c.dual)) :
    ∃ f : IntertwiningMap r B.radical.toRepresentation, f ≠ 0 := by
  apply SpeciesCopySurplus.exists_nonzero_kernel_map r (a.prod c.dual)
    (a.prod c.dual).dual B.toIntertwiningMap
  change Module.finrank ℂ (IntertwiningMap r (a.prod c.dual).dual) <
    Module.finrank ℂ (IntertwiningMap r (a.prod c.dual))
  rw [source_multiplicity r a c hc, target_multiplicity r a c ha]
  exact hd

theorem no_light_species_necessary (ha : NoPairings r a) (hc : NoPairings r c)
    (B : SymmetricMass (a.prod c.dual))
    (hz : ∀ f : IntertwiningMap r B.radical.toRepresentation, f = 0) :
    Module.finrank ℂ (IntertwiningMap r a) ≤ Module.finrank ℂ (IntertwiningMap r c) := by
  by_contra hn
  obtain ⟨f,hf⟩ := arbitrary_mass_survival r a c ha hc (lt_of_not_ge hn) B
  exact hf (hz f)

omit [FiniteDimensional ℂ R] in
/-- No selected species can be created by mass removal. -/
theorem radical_hom_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (B : SymmetricMass rho)
    (hz : ∀ f : IntertwiningMap r rho, f = 0)
    (f : IntertwiningMap r B.radical.toRepresentation) : f = 0 := by
  have h := hz ((CharacterExact.subtypeIntertwiner B.radical).comp f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (congrArg IntertwiningMap.toLinearMap h) x

theorem radical_multiplicity_bound {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (rho : Representation ℂ G V) (B : SymmetricMass rho) :
    Module.finrank ℂ (IntertwiningMap r rho) ≤
      Module.finrank ℂ (IntertwiningMap r rho.dual) +
        Module.finrank ℂ (IntertwiningMap r B.radical.toRepresentation) := by
  let M := SpeciesCopySurplus.postcompose r rho rho.dual B.toIntertwiningMap
  have hd := LinearMap.finrank_range_add_finrank_ker M
  have hk := (SpeciesCopySurplus.homKernelEquiv r rho rho.dual B.toIntertwiningMap).finrank_eq
  change Module.finrank ℂ (IntertwiningMap r B.radical.toRepresentation) =
    Module.finrank ℂ M.ker at hk
  have hl := Submodule.finrank_le (LinearMap.range M)
  rw [← hk] at hd
  omega

end
end GUT.HomSurplusMass

import Math.RepresentationTheory.Unitary.UnitaryIntertwiner
import Math.RepresentationTheory.Multiplicity.UnitaryCentralizerTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthogonal multiplicity coordinates for an actual unitary representation

The constituent spaces carry the inner products inherited from the original
space. Repeated copies and distinct constituents are combined using `PiLp 2`,
not the supremum norm on a plain product. Polar normalization upgrades the
existing algebraic decomposition to an isometric equivariant equivalence.
-/

namespace Math.IsometricMultiplicity

noncomputable section

open scoped MonoidAlgebra

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E)

scoped instance asModuleNormedAddCommGroup : NormedAddCommGroup rho.asModule :=
  inferInstanceAs (NormedAddCommGroup E)

scoped instance asModuleInnerProductSpace : InnerProductSpace ℂ rho.asModule :=
  inferInstanceAs (InnerProductSpace ℂ E)

scoped instance componentInnerProductSpace (c : isotypicComponents ℂ[G] rho.asModule) :
    InnerProductSpace ℂ c.1 :=
  InnerProductSpace.induced (c.1.subtype.restrictScalars ℂ)

variable (D : MultiplicityCommutant.Model ℂ[G] rho.asModule)

scoped instance simpleInnerProductSpace (c : isotypicComponents ℂ[G] rho.asModule) :
    InnerProductSpace ℂ (D.simple c) :=
  InnerProductSpace.induced ((D.simple c).subtype.restrictScalars ℂ)

/-- The actual chosen constituent, with its inherited Hilbert structure. -/
abbrev constituent (c : isotypicComponents ℂ[G] rho.asModule) :
    Representation ℂ G (D.simple c) := Representation.ofModule' (D.simple c)

omit [FiniteDimensional ℂ E] in
theorem constituent_unitary (h : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (c : isotypicComponents ℂ[G] rho.asModule) :
    UnitaryMultiplicity.IsUnitaryRepresentation (E := D.simple c) (constituent rho D c) := by
  intro g x y
  change inner ℂ
    (rho.asModuleEquiv ((MonoidAlgebra.single g (1 : ℂ)) • x.1.1))
    (rho.asModuleEquiv ((MonoidAlgebra.single g (1 : ℂ)) • y.1.1)) = _
  rw [Representation.single_smul, Representation.single_smul, one_smul, one_smul]
  exact h g x.1.1 y.1.1

/-- The future determinant exponents are positive dimensions of actual simple constituents. -/
theorem constituent_finrank_pos (c : isotypicComponents ℂ[G] rho.asModule) :
    0 < Module.finrank ℂ (D.simple c) := by
  let := D.isSimple c
  let := IsSimpleModule.nontrivial ℂ[G] (D.simple c)
  exact Module.finrank_pos (R := ℂ) (M := D.simple c)

variable [Fintype (isotypicComponents ℂ[G] rho.asModule)]

/-- Standard Hilbert sum of the multiplicity copies of the chosen constituents. -/
abbrev Space := PiLp 2 fun c : isotypicComponents ℂ[G] rho.asModule =>
  PiLp 2 fun _ : Fin (D.multiplicity c) => D.simple c

scoped instance spaceInnerProductSpace : InnerProductSpace ℂ (Space rho D) :=
  @PiLp.innerProductSpace ℂ _ _ _ _ _ (fun c =>
    @PiLp.innerProductSpace ℂ _ _ _ _ _ (fun _ => simpleInnerProductSpace rho D c))

scoped instance spaceFiniteDimensional : FiniteDimensional ℂ (Space rho D) := by
  let : ∀ c, FiniteDimensional ℂ (D.simple c) :=
    fun c => MultiplicityCommutant.Model.simple_finiteDimensional (k := ℂ) D c
  let : ∀ c, FiniteDimensional ℂ (PiLp 2 fun _ : Fin (D.multiplicity c) => D.simple c) :=
    fun _ => Module.Finite.equiv (WithLp.linearEquiv 2 ℂ _).symm
  exact Module.Finite.equiv (WithLp.linearEquiv 2 ℂ _).symm

abbrev action : Representation ℂ G (Space rho D) := Representation.ofModule' (Space rho D)

omit [FiniteDimensional ℂ E] in
theorem action_unitary (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    UnitaryMultiplicity.IsUnitaryRepresentation (E := Space rho D) (action rho D) := by
  intro g x y
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro j _
  exact constituent_unitary rho D h c g (x c j) (y c j)

/-- The existing algebraic decomposition, with the Hilbert-sum carrier. -/
def algebraicEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    rho.asModule ≃ₗ[ℂ[G]] Space rho D := by
  classical
  let _ := rho.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mp
    (UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary rho h)
  let e := ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents ℂ[G] rho.asModule)).linearEquiv
    ((sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents ℂ[G] rho.asModule))
  exact e.symm.trans ((DFinsupp.linearEquivFunOnFintype (R := ℂ[G])).trans
    ((LinearEquiv.piCongrRight fun c => (D.equiv c).trans
      (WithLp.linearEquiv 2 ℂ[G] (Fin (D.multiplicity c) → D.simple c)).symm).trans
      (WithLp.linearEquiv 2 ℂ[G] _).symm))

/-- Multiplicities and constituent dimensions account for the entire original space. -/
theorem finrank_eq_sum (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    Module.finrank ℂ E = ∑ c, D.multiplicity c * Module.finrank ℂ (D.simple c) := by
  rw [← rho.asModuleEquiv.finrank_eq, (algebraicEquiv rho D h).restrictScalars ℂ |>.finrank_eq,
    (WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro c _
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Every finite-dimensional unitary representation has isometric multiplicity coordinates. -/
theorem exists_isometricEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    ∃ u : E ≃ₗᵢ[ℂ] Space rho D, ∀ g x, u (rho g x) = action rho D g (u x) := by
  let e := rho.asModuleEquiv.symm.trans ((algebraicEquiv rho D h).restrictScalars ℂ)
  let : FiniteDimensional ℂ (Space rho D) := Module.Finite.equiv e
  refine UnitaryIntertwiner.exists_isometric_intertwiner
    (E := E) (F := Space rho D) (rho := rho) (sigma := action rho D)
    h (action_unitary rho D h) e ?_
  intro g x
  change algebraicEquiv rho D h (rho.asModuleEquiv.symm (rho g x)) = _
  rw [rho.asModuleEquiv_symm_map_rho, map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A chosen isometric multiplicity decomposition, constructed rather than assumed. -/
def isometricEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    E ≃ₗᵢ[ℂ] Space rho D := (exists_isometricEquiv rho D h).choose

set_option backward.isDefEq.respectTransparency false in
theorem isometricEquiv_intertwines (h : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (g : G) (x : E) :
    isometricEquiv rho D h (rho g x) = action rho D g (isometricEquiv rho D h x) :=
  (exists_isometricEquiv rho D h).choose_spec g x

set_option backward.isDefEq.respectTransparency false in
/-- Transport the actual U centralizer to the Hilbert multiplicity coordinates. -/
def unitaryCentralizerEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    UnitaryCentralizerTransport.unitaryCentralizer rho ≃ₜ*
      UnitaryCentralizerTransport.unitaryCentralizer (action rho D) :=
  UnitaryCentralizerTransport.unitaryCentralizerEquiv
    (isometricEquiv rho D h) (isometricEquiv_intertwines rho D h)

set_option backward.isDefEq.respectTransparency false in
/-- The same transport preserves the full SU subgroup, including disconnected components. -/
def specialCentralizerEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    UnitaryCentralizerTransport.specialCentralizer rho ≃ₜ*
      UnitaryCentralizerTransport.specialCentralizer (action rho D) :=
  UnitaryCentralizerTransport.specialCentralizerEquiv
    (isometricEquiv rho D h) (isometricEquiv_intertwines rho D h)

end

end Math.IsometricMultiplicity

import Math.RepresentationTheory.Characters.CompactWeylExtraction
import Math.LinearAlgebra.SelectionCriteria
import Mathlib.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Continuous.LinHom

/-! Joint occurrence and irreducible matching from a character presentation.
The only external premise is the existing Weyl torus-reduction interface.
No coefficient is evaluated and no numerical certificate is imported. -/
namespace Math.CompactWeylHom
set_option autoImplicit false
noncomputable section
open MeasureTheory Representation ContinuousRepresentationScope

variable {K V W L T : Type*} [Group K] [TopologicalSpace K]
  [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup L] [DecidableEq L] [Group T]
  (rho : Representation ℂ K V) (sigma : Representation ℂ K W)

def model : Representation ℂ K (V →L[ℂ] W) :=
  (ContRepresentation.linHom (CompactHomDimension.asContinuous rho)
    (CompactHomDimension.asContinuous sigma)).toRepresentation

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem character (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) (g : K) :
    (model rho sigma).character g = rho.character g⁻¹ * sigma.character g := by
  simpa only [model, TauCeti.ContRepresentation.coe_character,
    CompactHomDimension.asContinuous_toRepresentation] using
    (ContRepresentation.character_linHom (CompactHomDimension.asContinuous rho)
      (CompactHomDimension.asContinuous sigma)
      (CompactHomDimension.continuous_asContinuous rho hr)
      (CompactHomDimension.continuous_asContinuous sigma hs) g)

variable (torus : T →* K) (monomial : L → T → ℂ) (roots : List L)

omit [DecidableEq L] [AddCommGroup L] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem presents_of_characters (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (P : L →₀ ℤ)
    (hp : ∀ t, rho.character (torus t) * sigma.character ((torus t)⁻¹) =
      P.sum (fun w c => (c : ℂ) * monomial w t)) :
    CompactWeylExtraction.Presents (model rho sigma) torus monomial P := by
  intro t
  rw [character rho sigma hr hs,inv_inv]
  exact hp t

omit [DecidableEq L] in
theorem dimension (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (input : CompactWeylExtraction.TorusReduction (model rho sigma) torus monomial roots)
    (P : L →₀ ℤ) (hp : CompactWeylExtraction.Presents (model rho sigma) torus monomial P) :
    (Module.finrank ℂ (IntertwiningMap rho sigma) : ℤ) =
      CompactWeylExtraction.constantTerm roots P := by
  have hi := CompactHomDimension.integral_character_mul_eq_finrank rho sigma hr hs
  have he := input.reduce P hp
  rw [integral_inv_eq_self] at he
  simp_rw [character rho sigma hr hs] at he
  rw [CompactWeylExtraction.intCast_constantTerm] at he
  exact_mod_cast hi.symm.trans he

omit [DecidableEq L] in
/-- Positivity can equivalently be tested by nonvanishing; no exact dimension
has to be calculated. The representation and its full commuting actions stay
inside the character presentation. -/
theorem allowed_iff (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (input : CompactWeylExtraction.TorusReduction (model rho sigma) torus monomial roots)
    (P : L →₀ ℤ) (hp : CompactWeylExtraction.Presents (model rho sigma) torus monomial P) :
    SelectionCriteria.Allowed (IntertwiningMap rho sigma) ↔
      CompactWeylExtraction.constantTerm roots P ≠ 0 := by
  rw [SelectionCriteria.Allowed, ← Module.finrank_pos_iff_exists_ne_zero (R := ℂ)]
  have he := dimension rho sigma torus monomial roots hr hs input P hp
  constructor
  · intro hn hz
    have : (Module.finrank ℂ (IntertwiningMap rho sigma) : ℤ) = 0 := he.trans hz
    have : Module.finrank ℂ (IntertwiningMap rho sigma) = 0 := by exact_mod_cast this
    omega
  · intro hn
    by_contra hz
    apply hn
    have hz' : Module.finrank ℂ (IntertwiningMap rho sigma) = 0 := by omega
    rw [← he,hz',Int.natCast_zero]

omit [DecidableEq L] in
/-- For irreducibles this also eliminates the representation-isomorphism
test, without choosing matrices or computing their ranks. -/
theorem equiv_iff [IsIrreducible rho] [IsIrreducible sigma]
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (input : CompactWeylExtraction.TorusReduction (model rho sigma) torus monomial roots)
    (P : L →₀ ℤ) (hp : CompactWeylExtraction.Presents (model rho sigma) torus monomial P) :
    Nonempty (Representation.Equiv rho sigma) ↔
      CompactWeylExtraction.constantTerm roots P ≠ 0 := by
  rw [← allowed_iff rho sigma torus monomial roots hr hs input P hp]
  constructor
  · rintro ⟨e⟩
    let : Nontrivial V := IsIrreducible.nontrivial (ρ := rho) inferInstance
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    refine ⟨e.toIntertwiningMap, ?_⟩
    intro hz
    apply hv
    apply e.injective
    simpa using DFunLike.congr_fun hz v
  · rintro ⟨f,hf⟩
    exact ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

end
end Math.CompactWeylHom

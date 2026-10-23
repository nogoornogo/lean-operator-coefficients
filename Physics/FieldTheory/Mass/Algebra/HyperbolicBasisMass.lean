import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Math.LinearAlgebra.Constructions.EigenbasisTrace

open Math

/-!
# Pairing opposite-weight basis vectors and retaining the light basis

On a basis indexed by L + (P + P), pair the two P copies by a symmetric
bilinear form. Opposite scalar characters make it invariant. Its radical
has exactly the L basis and hence its full (not antisymmetrized) character.
-/

set_option autoImplicit false

namespace Physics.HyperbolicBasisMass

noncomputable section

open InvariantWeylMass

variable {G V L P : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
variable [FiniteDimensional ℂ V] [Fintype L] [Fintype P]

abbrev Index (L P : Type*) := L ⊕ (P ⊕ P)

variable (b : Module.Basis (Index L P) ℂ V)

def form : LinearMap.BilinForm ℂ V :=
  ∑ i : P,
    ((LinearMap.mul ℂ ℂ).compl₁₂ (b.coord (.inr (.inl i))) (b.coord (.inr (.inr i))) +
    (LinearMap.mul ℂ ℂ).compl₁₂ (b.coord (.inr (.inr i))) (b.coord (.inr (.inl i))))

omit [FiniteDimensional ℂ V] [Fintype L] in
theorem form_apply (x y : V) : form b x y =
    ∑ i : P, (b.coord (.inr (.inl i)) x * b.coord (.inr (.inr i)) y +
      b.coord (.inr (.inr i)) x * b.coord (.inr (.inl i)) y) := by
  simp [form, LinearMap.sum_apply]

omit [FiniteDimensional ℂ V] [Fintype L] in
theorem form_symmetric : (form b).IsSymm := by
  constructor
  intro x y
  simp only [form_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℂ V] [Fintype L] in
theorem form_pair (i : P) : form b (b (.inr (.inl i))) (b (.inr (.inr i))) = 1 := by
  classical
  simp [form_apply, Module.Basis.coord_apply, Finsupp.single_apply]

omit [FiniteDimensional ℂ V] [Fintype L] in
theorem form_ne_zero (i : P) : form b ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun
    (LinearMap.congr_fun h (b (.inr (.inl i)))) (b (.inr (.inr i)))
  rw [form_pair] at he
  exact one_ne_zero he

variable (rho : Representation ℂ G V) (chi : Index L P → G →* ℂ)
variable (hb : ∀ g i, rho g (b i) = chi i g • b i)

include hb in
omit [FiniteDimensional ℂ V] [Fintype L] [Fintype P] in
theorem coord_action (g : G) (i : Index L P) (x : V) :
    b.coord i (rho g x) = chi i g * b.coord i x := by
  classical
  have he : (b.coord i).comp (rho g) = chi i g • b.coord i := by
    apply b.ext
    intro j
    by_cases h : j = i
    · subst j
      simp [hb, Module.Basis.coord_apply]
    · simp [hb, Module.Basis.coord_apply, h]
  exact LinearMap.congr_fun he x

variable (hp : ∀ i g, chi (.inr (.inl i)) g * chi (.inr (.inr i)) g = 1)

include hb hp

def mass : SymmetricMass rho where
  form := form b
  symmetric := form_symmetric b
  invariant := by
    intro g x y
    simp only [form_apply, coord_action b rho chi hb]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (chi (.inr (.inl i)) g * chi (.inr (.inr i)) g) *
        (b.coord (.inr (.inl i)) x * b.coord (.inr (.inr i)) y +
          b.coord (.inr (.inr i)) x * b.coord (.inr (.inl i)) y) := by ring
      _ = _ := by rw [hp, one_mul]

omit [FiniteDimensional ℂ V] [Fintype L] in
theorem mem_radical_iff (x : V) :
    x ∈ (mass b rho chi hb hp).radical.toSubmodule ↔
      (∀ i : P, b.coord (.inr (.inl i)) x = 0) ∧
        (∀ i : P, b.coord (.inr (.inr i)) x = 0) := by
  classical
  rw [SymmetricMass.mem_radical]
  change (∀ y, form b x y = 0) ↔ _
  constructor
  · intro h
    constructor
    · intro i
      simpa [form_apply, Module.Basis.coord_apply, Finsupp.single_apply] using h (b (.inr (.inr i)))
    · intro i
      simpa [form_apply, Module.Basis.coord_apply, Finsupp.single_apply] using h (b (.inr (.inl i)))
  · rintro ⟨hl, hr⟩ y
    simp [form_apply, hl, hr]

def lightCoordinates : (mass b rho chi hb hp).radical.toSubmodule →ₗ[ℂ] (L → ℂ) :=
  LinearMap.pi fun i => (b.coord (.inl i)).comp (mass b rho chi hb hp).radical.toSubmodule.subtype

omit [FiniteDimensional ℂ V] in
theorem lightCoordinates_bijective : Function.Bijective (lightCoordinates b rho chi hb hp) := by
  classical
  constructor
  · intro x y h
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rcases i with i | (i | i)
    · exact congrFun h i
    · have hx := ((mem_radical_iff b rho chi hb hp x).mp x.property).1 i
      have hy := ((mem_radical_iff b rho chi hb hp y).mp y.property).1 i
      exact hx.trans hy.symm
    · have hx := ((mem_radical_iff b rho chi hb hp x).mp x.property).2 i
      have hy := ((mem_radical_iff b rho chi hb hp y).mp y.property).2 i
      exact hx.trans hy.symm
  · intro z
    let x := b.equivFun.symm (Sum.elim z (fun _ => 0))
    have hx : x ∈ (mass b rho chi hb hp).radical.toSubmodule := by
      rw [mem_radical_iff]
      simp [x]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext i
    change b.coord (.inl i) x = z i
    exact b.coord_equivFun_symm _ _

def lightEquiv : (mass b rho chi hb hp).radical.toSubmodule ≃ₗ[ℂ] (L → ℂ) :=
  LinearEquiv.ofBijective (lightCoordinates b rho chi hb hp) (lightCoordinates_bijective b rho chi hb hp)

omit [FiniteDimensional ℂ V] in
theorem radical_finrank : Module.finrank ℂ (mass b rho chi hb hp).radical.toSubmodule =
    Fintype.card L := by
  rw [(lightEquiv b rho chi hb hp).finrank_eq]
  simp

def lightBasis : Module.Basis L ℂ (mass b rho chi hb hp).radical.toSubmodule :=
  (Pi.basisFun ℂ L).map (lightEquiv b rho chi hb hp).symm

omit [FiniteDimensional ℂ V] in
theorem lightBasis_action (g : G) (i : L) :
    (mass b rho chi hb hp).radical.toRepresentation g (lightBasis b rho chi hb hp i) =
      chi (.inl i) g • lightBasis b rho chi hb hp i := by
  classical
  apply (lightEquiv b rho chi hb hp).injective
  rw [map_smul]
  ext j
  change b.coord (.inl j) (rho g _) = _
  rw [coord_action b rho chi hb]
  have he : lightEquiv b rho chi hb hp (lightBasis b rho chi hb hp i) = Pi.basisFun ℂ L i := by
    simp [lightBasis]
  have hj := congrFun he j
  change b.coord (.inl j) _ = Pi.basisFun ℂ L i j at hj
  change _ = chi (.inl i) g * b.coord (.inl j) _
  rw [hj]
  by_cases h : i = j
  · subst j; rfl
  · simp [Pi.basisFun_apply, h]

omit [FiniteDimensional ℂ V] in
theorem radical_character (g : G) :
    (mass b rho chi hb hp).radical.toRepresentation.character g =
      ∑ i : L, chi (.inl i) g := by
  classical
  exact WeightTheory.trace_eq_sum_of_basis_eigen (lightBasis b rho chi hb hp) _ _
    (lightBasis_action b rho chi hb hp g)

end

end Physics.HyperbolicBasisMass

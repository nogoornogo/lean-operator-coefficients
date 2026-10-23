import Math.RepresentationTheory.Relations.SignedRelationQuotient
import Mathlib.RepresentationTheory.Invariants

/-! Finite statistics coinvariants are invariants, equivariantly for a commuting
residual action. The cardinal must be invertible in the scalar field. -/
namespace Math.FiniteStatisticsQuotient
set_option autoImplicit false
noncomputable section
open Representation
variable {k H S U : Type*} [Field k] [Group H] [Group S] [Fintype S]
  [Invertible (Fintype.card S : k)] [AddCommGroup U] [Module k U]
  (rho : Representation k H U) (b : Representation k S U)
  (commutes : ∀ g h u, b g (rho h u) = rho h (b g u))

def exchange (g : S) : IntertwiningMap rho rho where
  toLinearMap := b g
  isIntertwining' h := by ext u; exact commutes g h u

abbrev relations := SignedRelationQuotient.relations rho (exchange rho b commutes) (fun _ => 1)

theorem average_formula (u : U) : b.averageMap u =
    ⅟(Fintype.card S : k) • ∑ g : S, b g u := by
  simp [Representation.averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]

theorem average_right (g : S) (u : U) : b.averageMap (b g u) = b.averageMap u := by
  change b.asAlgebraHom (GroupAlgebra.average k S) (b g u) = _
  rw [← b.asAlgebraHom_single_one g, ← Module.End.mul_apply, ← map_mul,
    GroupAlgebra.mul_average_right]
  rfl

include commutes in
theorem average_commutes (h : H) (u : U) :
    b.averageMap (rho h u) = rho h (b.averageMap u) := by
  rw [average_formula, average_formula, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => commutes g h u)

include commutes in
omit [Invertible (Fintype.card S : k)] [Fintype S] in
theorem invariants_stable : ∀ h, b.invariants ≤ b.invariants.comap (rho h) := by
  intro h u hu
  change ∀ g, b g (rho h u) = rho h u
  intro g
  rw [commutes, hu g]

abbrev invariantRepresentation := rho.subrepresentation b.invariants (invariants_stable rho b commutes)

def project : IntertwiningMap rho (invariantRepresentation rho b commutes) where
  toLinearMap := b.averageMap.codRestrict b.invariants b.averageMap_invariant
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact average_commutes rho b commutes h u

theorem average_vanish : relations rho b commutes ≤ LinearMap.ker b.averageMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,u⟩, rfl⟩
  change b.averageMap (b g u - (1 : k) • u) = 0
  rw [one_smul, map_sub, average_right, sub_self]

def descend : IntertwiningMap
    (SignedRelationQuotient.quotientRepresentation rho (exchange rho b commutes) (fun _ => 1))
    (invariantRepresentation rho b commutes) :=
  RelationQuotient.descend rho (invariantRepresentation rho b commutes)
    (relations rho b commutes) (SignedRelationQuotient.stable rho (exchange rho b commutes) (fun _ => 1))
    ⟨project rho b commutes, by
      intro u hu
      apply Subtype.ext
      exact average_vanish rho b commutes hu⟩

theorem average_sub_mem (u : U) : b.averageMap u - u ∈ relations rho b commutes := by
  have he : b.averageMap u - u =
      ⅟(Fintype.card S : k) • ∑ g : S, (b g u - u) := by
    rw [average_formula, Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]
  rw [he]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro g hg
  exact Submodule.subset_span ⟨(g,u), by simp [SignedRelationQuotient.relation, exchange]⟩

def equiv : Representation.Equiv
    (SignedRelationQuotient.quotientRepresentation rho (exchange rho b commutes) (fun _ => 1))
    (invariantRepresentation rho b commutes) where
  toLinearEquiv :=
    { toLinearMap := (descend rho b commutes).toLinearMap
      invFun := fun u => (relations rho b commutes).mkQ u.val
      left_inv := by
        intro q
        obtain ⟨u, rfl⟩ := (relations rho b commutes).mkQ_surjective q
        change (relations rho b commutes).mkQ (b.averageMap u) = (relations rho b commutes).mkQ u
        apply sub_eq_zero.mp
        rw [← map_sub]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (average_sub_mem rho b commutes u)
      right_inv := by
        intro u
        apply Subtype.ext
        exact b.averageMap_id u.val u.property }
  isIntertwining' := (descend rho b commutes).isIntertwining'

@[simp] theorem equiv_mk (u : U) :
    (equiv rho b commutes ((relations rho b commutes).mkQ u)).val = b.averageMap u := rfl

@[simp] theorem equiv_symm (u : b.invariants) :
    (equiv rho b commutes).symm u = (relations rho b commutes).mkQ u.val := rfl

/-- Twist by an inverse one-dimensional character. Its invariants are the
character-isotypic component of the original statistics action. -/
def twisted (chi : S →* kˣ) : Representation k S U where
  toFun g := ((chi g)⁻¹ : kˣ).val • b g
  map_one' := by simp
  map_mul' g h := by
    ext u
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul, smul_smul]

include commutes in
omit [Invertible (Fintype.card S : k)] [Fintype S] in
theorem twisted_commutes (chi : S →* kˣ) (g : S) (h : H) (u : U) :
    twisted b chi g (rho h u) = rho h (twisted b chi g u) := by
  change ((chi g)⁻¹ : kˣ).val • b g (rho h u) = rho h (((chi g)⁻¹ : kˣ).val • b g u)
  rw [commutes, map_smul]

def characterEquiv (chi : S →* kˣ) :=
  equiv rho (twisted b chi) (twisted_commutes rho b commutes chi)

omit [Invertible (Fintype.card S : k)] [Fintype S] in
theorem mem_twisted (chi : S →* kˣ) (u : U) :
    u ∈ (twisted b chi).invariants ↔ ∀ g, b g u = (chi g).val • u := by
  constructor
  · intro hu g
    have he := hu g
    change ((chi g)⁻¹ : kˣ).val • b g u = u at he
    have hf := congrArg (fun w : U => (chi g).val • w) he
    simpa only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] using hf
  · intro hu g
    change ((chi g)⁻¹ : kˣ).val • b g u = u
    rw [hu, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end
end Math.FiniteStatisticsQuotient

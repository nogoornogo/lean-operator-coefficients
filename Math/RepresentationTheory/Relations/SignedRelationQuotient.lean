import Math.RepresentationTheory.Relations.RelationQuotient

/-! Signed input relations give a universal equivariant-Hom realization of
generator statistics. The generators need not form a group action. -/
namespace Math.SignedRelationQuotient
set_option autoImplicit false
noncomputable section
open Representation
variable {k H U W J : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (rho : Representation k H U) (tau : Representation k H W)
  (exchange : J → IntertwiningMap rho rho) (sign : J → k)

def relation (j : J) (u : U) : U := exchange j u - sign j • u

def relations : Submodule k U :=
  RelationQuotient.relations (fun t : J × U => relation rho exchange sign t.1 t.2)

theorem stable : ∀ g, relations rho exchange sign ≤
    (relations rho exchange sign).comap (rho g) := by
  apply RelationQuotient.relations_stable
  intro g t
  have he := IntertwiningMap.isIntertwining _ _ (exchange t.1) g t.2
  have h : rho g (relation rho exchange sign t.1 t.2) =
      relation rho exchange sign t.1 (rho g t.2) := by
    simp [relation, he]
  rw [h]
  exact Submodule.subset_span ⟨(t.1, rho g t.2), rfl⟩

def quotientRepresentation :=
  rho.quotient (relations rho exchange sign) (stable rho exchange sign)

def action (j : J) : IntertwiningMap rho tau →ₗ[k] IntertwiningMap rho tau where
  toFun f := f.comp (exchange j)
  map_add' f h := by ext u; rfl
  map_smul' z f := by ext u; rfl

theorem admissible (f : IntertwiningMap rho tau) :
    f ∈ StatisticalCompleteness.sector (action rho tau exchange) sign ↔
    f ∈ RelationQuotient.vanishing rho tau (relations rho exchange sign) := by
  unfold relations
  rw [RelationQuotient.vanish_relations_iff]
  change (∀ j, f.comp (exchange j) = sign j • f) ↔
    ∀ t : J × U, f (relation rho exchange sign t.1 t.2) = 0
  simp only [relation, map_sub, map_smul, sub_eq_zero]
  constructor
  · intro h t
    exact congrArg (fun q : IntertwiningMap rho tau => q t.2) (h t.1)
  · intro h j
    ext u
    exact h (j, u)

def equiv : StatisticalCompleteness.sector (action rho tau exchange) sign ≃ₗ[k]
    IntertwiningMap (quotientRepresentation rho exchange sign) tau :=
  (ConstrainedCompleteness.Presentation.mk (LinearEquiv.refl k _)
    (admissible rho tau exchange sign)).equiv.trans
      (RelationQuotient.equiv rho tau (relations rho exchange sign) (stable rho exchange sign))

@[simp] theorem extraction (f : StatisticalCompleteness.sector (action rho tau exchange) sign)
    (u : U) :
    equiv rho tau exchange sign f ((relations rho exchange sign).mkQ u) = f.val u := rfl

@[simp] theorem reconstruction
    (f : IntertwiningMap (quotientRepresentation rho exchange sign) tau) (u : U) :
    ((equiv rho tau exchange sign).symm f).val u =
      f ((relations rho exchange sign).mkQ u) := rfl

theorem empty_relations :
    relations rho (fun j : Empty => nomatch j) (fun j => nomatch j) = ⊥ := by
  apply le_antisymm
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, u⟩, rfl⟩
  exact nomatch j
  exact bot_le

theorem identity_relations :
    relations rho (fun _ : Unit => IntertwiningMap.id rho) (fun _ => (1 : k)) = ⊥ := by
  apply le_antisymm
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, u⟩, rfl⟩
  simp [relation]
  exact bot_le

theorem identity_relations_top (z : k) (hz : z ≠ 1) :
    relations rho (fun _ : Unit => IntertwiningMap.id rho) (fun _ => z) = ⊤ := by
  apply eq_top_iff.mpr
  intro u hu
  have hn : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h : relation rho (fun _ : Unit => IntertwiningMap.id rho) (fun _ => z)
      () ((1 - z)⁻¹ • u) ∈
      relations rho (fun _ : Unit => IntertwiningMap.id rho) (fun _ => z) :=
    Submodule.subset_span ⟨((), (1 - z)⁻¹ • u), rfl⟩
  change (1 - z)⁻¹ • u - z • ((1 - z)⁻¹ • u) ∈ _ at h
  rw [smul_smul, ← sub_smul] at h
  have hc : (1 - z)⁻¹ - z * (1 - z)⁻¹ = 1 := by
    calc
      _ = (1 - z) * (1 - z)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hn
  rwa [hc, one_smul] at h

end
end Math.SignedRelationQuotient

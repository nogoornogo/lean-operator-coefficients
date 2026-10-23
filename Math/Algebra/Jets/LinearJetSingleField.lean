import Math.RepresentationTheory.Jets.LinearJetIBP

/-! Every positive-order single odd-field jet is an ordinary divergence. -/
namespace Math.LinearJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra
open scoped TensorProduct
variable {F B I EF EB : Type*} [AddCommGroup EF] [Module ℂ EF]
  [AddCommGroup EB] [Module ℂ EB]
  (eF : EF →ₗ[ℂ] Jet F I) (eB : EB →ₗ[ℂ] Jet B I)

@[reducible] local instance (d : ℕ) : AddCommGroup (MixedJetAlgebra.grade F B I 1 0 d) := inferInstance
@[reducible] local instance (d : ℕ) : Module ℂ (MixedJetAlgebra.grade F B I 1 0 d) := inferInstance
@[reducible] local instance (d : ℕ) : AddCommGroup (grade eF eB 1 0 d) := inferInstance
@[reducible] local instance (d : ℕ) : Module ℂ (grade eF eB 1 0 d) := inferInstance

private theorem predecessor {a : I →₀ ℕ} {d : ℕ} (ho : order a = d + 1) :
    ∃ i b, b + Finsupp.single i 1 = a ∧ order b = d := by
  classical
  have hn : a ≠ 0 := by intro hz; simp [hz, order] at ho
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hh
    apply hn
    ext i
    simpa using not_exists.mp hh i
  refine ⟨i, a - Finsupp.single i 1, Finsupp.sub_add_single_one_cancel hi, ?_⟩
  have he := congrArg order (Finsupp.sub_add_single_one_cancel hi)
  have he' : order (a - Finsupp.single i 1) + 1 = order a := by
    simpa only [order, map_add, Finsupp.weight_single, one_smul] using he
  omega

private theorem odd_mem_off (s : F) (a : I →₀ ℕ) (d : ℕ) (ho : order a = d + 1) :
    (⟨MixedJetAlgebra.odd (B := B) (s, a), by simpa only [ho] using (MixedJetAlgebra.odd_mem (B := B) (s, a))⟩ :
      MixedJetAlgebra.grade F B I 1 0 (d + 1)) ∈ offRelations 1 0 d := by
  obtain ⟨i, b, hb, hbo⟩ := predecessor ho
  let y : MixedJetAlgebra.grade F B I 1 0 d :=
    ⟨MixedJetAlgebra.odd (s, b), by simpa only [hbo] using (MixedJetAlgebra.odd_mem (B := B) (s, b))⟩
  have he : MixedJetAlgebra.derivative i 1 0 d y =
      ⟨MixedJetAlgebra.odd (s, a), by simpa only [ho] using (MixedJetAlgebra.odd_mem (B := B) (s, a))⟩ := by
    apply Subtype.ext
    change MixedJetAlgebra.totalDerivative i (MixedJetAlgebra.odd (s, b)) = _
    rw [MixedJetAlgebra.totalDerivative_odd]
    simp [ScalarJetAlgebra.shift, hb]
  rw [← he]
  exact GradedJetIBP.derivative_mem (DirectionalJetIBP.mixedDerivatives 1 0) d i y

theorem odd_offRelations_top (d : ℕ) : offRelations (F := F) (B := B) (I := I) 1 0 d = ⊤ := by
  let G := MixedJetAlgebra.grade F B I 1 0 (d + 1)
  let R := offRelations (F := F) (B := B) (I := I) 1 0 d
  have h : G ≤ R.map G.subtype := by
    apply Submodule.span_le.mpr
    rintro p ⟨f, b, hd, rfl⟩
    have hw : MixedJetAlgebra.word f b = MixedJetAlgebra.odd (B := B) (f 0) := by
      simp [MixedJetAlgebra.word, MixedJetAlgebra.odd, ExteriorAlgebra.ιMulti_succ_apply]
    have ho : order (f 0).2 = d + 1 := by
      simpa [MixedJetAlgebra.wordOrder, Fin.sum_univ_succ] using hd
    rw [hw]
    exact ⟨_, odd_mem_off (f 0).1 (f 0).2 d ho, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := h x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

theorem odd_ibpRelations_top (d : ℕ) : ibpRelations eF eB 1 0 d = ⊤ := by
  rw [ibpRelations_map, odd_offRelations_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (gradeProjection_surjective eF eB 1 0 (d + 1))

instance odd_quotient_subsingleton (d : ℕ) :
    Subsingleton (grade eF eB 1 0 (d + 1) ⧸ ibpRelations eF eB 1 0 d) := by
  rw [odd_ibpRelations_top]
  infer_instance

theorem odd_quotient_finrank (d : ℕ) :
    Module.finrank ℂ (grade eF eB 1 0 (d + 1) ⧸ ibpRelations eF eB 1 0 d) = 0 :=
  Module.finrank_zero_of_subsingleton

def odd_quotient_basis (d : ℕ) : Module.Basis (Fin 0) ℂ
    (grade eF eB 1 0 (d + 1) ⧸ ibpRelations eF eB 1 0 d) := Module.Basis.empty _

end
end Math.LinearJetAlgebra

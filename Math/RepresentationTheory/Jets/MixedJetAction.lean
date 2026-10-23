import Math.Algebra.Jets.MixedJetFinite

/-! Arbitrary internal linear actions preserve the actual joint mixed grades. -/
namespace Math.MixedJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra Representation
open scoped TensorProduct

variable {F B I : Type*} {n m : ℕ}

private theorem multilinear_mem_of_basis {K : Type*} [Finite K] {S V : Type*}
    [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (f : MultilinearMap ℂ (fun _ : K => JetLinear.Field S) V)
    (hf : ∀ s : K → S, f (fun i => Finsupp.single (s i) 1) ∈ P) (v : K → JetLinear.Field S) :
    f v ∈ P := by
  have he : P.mkQ.compMultilinearMap f = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => Finsupp.basisSingleOne)
    intro s
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hf s)
  exact (Submodule.Quotient.mk_eq_zero P).mp (MultilinearMap.congr_fun he v)

def wordVectors (α : Fin n → I →₀ ℕ) (β : Fin m → I →₀ ℕ)
    (v : Fin n → JetLinear.Field F) (w : Fin m → JetLinear.Field B) : Algebra F B I :=
  ExteriorAlgebra.ιMulti ℂ n (fun i => atOrder (α i) (v i)) ⊗ₜ[ℂ]
    ∏ j, linearForm (atOrder (β j) (w j))

theorem wordVectors_mem (α : Fin n → I →₀ ℕ) (β : Fin m → I →₀ ℕ)
    (v : Fin n → JetLinear.Field F) (w : Fin m → JetLinear.Field B) :
    wordVectors α β v w ∈ grade F B I n m ((∑ i, order (α i)) + ∑ j, order (β j)) := by
  let P := grade F B I n m ((∑ i, order (α i)) + ∑ j, order (β j))
  have hb (s : Fin n → F) :
      wordVectors α β (fun i => Finsupp.single (s i) 1) w ∈ P := by
    let x := ExteriorAlgebra.ιMulti ℂ n (fun i => atOrder (α i) (Finsupp.single (s i) 1))
    let f := (TensorProduct.mk ℂ (Odd F I) (Even B I) x).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℂ (Fin m) (Even B I)).compLinearMap
        (fun j => linearForm.comp (atOrder (β j))))
    apply multilinear_mem_of_basis P f _ w
    intro t
    simpa [f, x, P, wordVectors, word, wordOrder, linearForm] using
      word_mem (fun i => (s i, α i)) (fun j => (t j, β j))
  let y : Even B I := ∏ j, linearForm (atOrder (β j) (w j))
  let f := ((TensorProduct.mk ℂ (Odd F I) (Even B I)).flip y).compMultilinearMap
    ((ExteriorAlgebra.ιMulti ℂ n).toMultilinearMap.compLinearMap (fun i => atOrder (α i)))
  apply multilinear_mem_of_basis P f _ v
  intro s
  exact hb s

theorem action_word {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (h : H)
    (f : Fin n → Index F I) (b : Fin m → Index B I) :
    action ρF ρB h (word f b) = wordVectors (fun i => (f i).2) (fun j => (b j).2)
      (fun i => ρF h (Finsupp.single (f i).1 1))
      (fun j => ρB h (Finsupp.single (b j).1 1)) := by
  change (ExteriorAlgebra.map (JetLinear.map (ρF h)))
      (ExteriorAlgebra.ιMulti ℂ n (fun i => Finsupp.single (f i) 1)) ⊗ₜ[ℂ]
      polynomialMap (ρB h) (∏ j, MvPolynomial.X (b j)) = _
  rw [ExteriorAlgebra.map_apply_ιMulti, map_prod]
  unfold wordVectors
  congr 1
  · congr 1
    funext i
    rcases hf : f i with ⟨s, α⟩
    simp [hf]
  · apply Finset.prod_congr rfl
    intro j _
    rcases hb : b j with ⟨s, β⟩
    simp [hb]

theorem action_mem {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (h : H) {n m d : ℕ} {p : Algebra F B I}
    (hp : p ∈ grade F B I n m d) : action ρF ρB h p ∈ grade F B I n m d := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, b, hf, rfl⟩ := hp
    rw [action_word]
    have h := wordVectors_mem (fun i => (f i).2) (fun j => (b j).2)
      (fun i => ρF h (Finsupp.single (f i).1 1)) (fun j => ρB h (Finsupp.single (b j).1 1))
    change _ ∈ grade F B I n m (wordOrder f b) at h
    rwa [hf] at h
  | zero => simpa only [map_zero] using (grade F B I n m d).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (grade F B I n m d).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (grade F B I n m d).smul_mem c hp

def gradeAction {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ) :
    Representation ℂ H (grade F B I n m d) where
  toFun h :=
    { toFun p := ⟨action ρF ρB h p.val, action_mem ρF ρB h p.property⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (action (I := I) ρF ρB).map_one p.val
  map_mul' h k := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun ((action (I := I) ρF ρB).map_mul h k) p.val

theorem derivative_covariant {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ) (h : H) (i : I)
    (p : grade F B I n m d) :
    gradeAction ρF ρB n m (d + 1) h (derivative i n m d p) =
      derivative i n m d (gradeAction ρF ρB n m d h p) :=
  Subtype.ext (covariance ρF ρB h i p.val)

section Commuting
variable {G H : Type*} [Group G] [Group H]
  (aF : Representation ℂ G (JetLinear.Field F)) (aB : Representation ℂ G (JetLinear.Field B))
  (ρF : Representation ℂ H (JetLinear.Field F)) (ρB : Representation ℂ H (JetLinear.Field B))
  (commF : ∀ g h v, aF g (ρF h v) = ρF h (aF g v))
  (commB : ∀ g h v, aB g (ρB h v) = ρB h (aB g v))

include commF commB in
theorem actions_commute (g : G) (h : H) (p : Algebra F B I) :
    action aF aB g (action ρF ρB h p) = action ρF ρB h (action aF aB g p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul x y =>
    change ExteriorAlgebra.map (JetLinear.map (aF g))
        (ExteriorAlgebra.map (JetLinear.map (ρF h)) x) ⊗ₜ[ℂ]
        polynomialMap (aB g) (polynomialMap (ρB h) y) =
      ExteriorAlgebra.map (JetLinear.map (ρF h))
        (ExteriorAlgebra.map (JetLinear.map (aF g)) x) ⊗ₜ[ℂ]
        polynomialMap (ρB h) (polynomialMap (aB g) y)
    apply congrArg₂ (fun (x : Odd F I) (y : Even B I) => x ⊗ₜ[ℂ] y)
    · have hf : (aF g).comp (ρF h) = (ρF h).comp (aF g) := LinearMap.ext (commF g h)
      have hj : (JetLinear.map (aF g) (I := I)).comp (JetLinear.map (ρF h)) =
          (JetLinear.map (ρF h)).comp (JetLinear.map (aF g)) := by
        rw [← JetLinear.map_comp, ← JetLinear.map_comp, hf]
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hj,
        ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply]
    · have hb : (aB g).comp (ρB h) = (ρB h).comp (aB g) := LinearMap.ext (commB g h)
      rw [← AlgHom.comp_apply, ← polynomialMap_comp, hb, polynomialMap_comp]
      rfl

include commF commB in
theorem grade_actions_commute (n m d : ℕ) (g : G) (h : H) (p : grade F B I n m d) :
    gradeAction aF aB n m d g (gradeAction ρF ρB n m d h p) =
      gradeAction ρF ρB n m d h (gradeAction aF aB n m d g p) :=
  Subtype.ext (actions_commute aF aB ρF ρB commF commB g h p.val)
end Commuting

end
end Math.MixedJetAlgebra

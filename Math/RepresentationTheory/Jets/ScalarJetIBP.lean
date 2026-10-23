import Math.Algebra.Jets.ScalarJetGrading
import Math.RepresentationTheory.Relations.LocalRelationHom

/-! Actual scalar total divergences, their graded relation quotient, and
inverse coefficient descent. Internal symmetries relabel scalar components;
they fix derivative directions. No averaging or on-shell premise is used. -/
namespace Math.ScalarJetIBP
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra Representation

variable {S T I : Type*}

abbrev Current (S I : Type*) (n d : ℕ) := I →₀ grade (S := S) (I := I) n d

def divergence (n d : ℕ) : Current S I n d →ₗ[ℂ] grade (S := S) (I := I) n (d + 1) :=
  Finsupp.lsum ℂ (fun i => derivative i n d)

@[simp] theorem divergence_single (n d : ℕ) (i : I) (p : grade (S := S) (I := I) n d) :
    divergence n d (Finsupp.single i p) = derivative i n d p :=
  Finsupp.lsum_single ℂ _ i p

def relations (S I : Type*) (n d : ℕ) : Submodule ℂ (grade (S := S) (I := I) n (d + 1)) :=
  LinearMap.range (divergence n d)

theorem derivative_mem_relations (n d : ℕ) (i : I) (p : grade (S := S) (I := I) n d) :
    derivative i n d p ∈ relations S I n d :=
  ⟨Finsupp.single i p, divergence_single n d i p⟩

theorem annihilates_iff {W : Type*} [AddCommGroup W] [Module ℂ W] (n d : ℕ)
    (f : grade (S := S) (I := I) n (d + 1) →ₗ[ℂ] W) :
    relations S I n d ≤ LinearMap.ker f ↔ ∀ i p, f (derivative i n d p) = 0 := by
  constructor
  · intro h i p; exact h (derivative_mem_relations n d i p)
  · intro h u hu
    obtain ⟨c, rfl⟩ := hu
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using (LinearMap.ker f).add_mem ha hb
    | single i p => rw [divergence_single]; exact h i p

def currentRelabel (f : S → T) (n d : ℕ) : Current S I n d →ₗ[ℂ] Current T I n d :=
  Finsupp.mapRange.linearMap (relabelGrade f n d)

theorem divergence_relabel (f : S → T) (n d : ℕ) (c : Current S I n d) :
    relabelGrade f n (d + 1) (divergence n d c) =
      divergence n d (currentRelabel f n d c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single i p =>
    simp only [currentRelabel, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      divergence_single]
    exact (derivative_relabelGrade f i n d p).symm

variable {H : Type*} [Group H] (r : H →* Equiv.Perm S)

def action (n d : ℕ) : Representation ℂ H (grade (S := S) (I := I) n d) where
  toFun h := relabelGrade (r h) n d
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change relabel (r 1) p.val = p.val
    simp [relabel]
    exact MvPolynomial.rename_id_apply p.val
  map_mul' h k := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change relabel (r (h * k)) p.val = relabel (r h) (relabel (r k) p.val)
    simp only [map_mul, relabel, MvPolynomial.rename_rename]
    rfl

theorem relations_stable (n d : ℕ) :
    ∀ h, relations S I n d ≤ (relations S I n d).comap (action r n (d + 1) h) := by
  intro h u hu
  obtain ⟨c, rfl⟩ := hu
  exact ⟨currentRelabel (r h) n d c, (divergence_relabel (r h) n d c).symm⟩

abbrev quotient (n d : ℕ) :=
  (action (I := I) r n (d + 1)).quotient (relations S I n d) (relations_stable r n d)

/-- Coefficients are functionals on the operator source, vanishing on actual divergences. -/
abbrev Coefficient (n d : ℕ) :=
  RelationQuotient.vanishing (action (I := I) r n (d + 1)) (trivial ℂ H ℂ) (relations S I n d)

def coefficientEquiv (n d : ℕ) : Coefficient (I := I) r n d ≃ₗ[ℂ]
    IntertwiningMap (quotient (I := I) r n d) (trivial ℂ H ℂ) :=
  RelationQuotient.equiv _ _ _ (relations_stable r n d)

@[simp] theorem coefficientEquiv_mk (n d : ℕ) (f : Coefficient (I := I) r n d)
    (p : grade (S := S) (I := I) n (d + 1)) :
    coefficientEquiv r n d f ((relations S I n d).mkQ p) = f.val p := rfl

@[simp] theorem coefficientEquiv_symm (n d : ℕ)
    (f : IntertwiningMap (quotient (I := I) r n d) (trivial ℂ H ℂ))
    (p : grade (S := S) (I := I) n (d + 1)) :
    ((coefficientEquiv r n d).symm f).val p = f ((relations S I n d).mkQ p) := rfl

theorem coefficient_mem_iff (n d : ℕ)
    (f : IntertwiningMap (action (I := I) r n (d + 1)) (trivial ℂ H ℂ)) :
    f ∈ Coefficient (I := I) r n d ↔ ∀ i p, f (derivative i n d p) = 0 :=
  annihilates_iff n d f.toLinearMap

theorem integration_by_parts (i : I) {n d m e : ℕ}
    (p : grade (S := S) (I := I) n d) (q : grade (S := S) (I := I) m e)
    (f : Coefficient (I := I) r (n + m) (d + e)) :
    f.val (productLeft i p q) = -f.val (productRight i p q) := by
  have hz := f.property (derivative_mem_relations (n + m) (d + e) i (multiply p q))
  change f.val (derivative i (n + m) (d + e) (multiply p q)) = 0 at hz
  rw [derivative_multiply, map_add] at hz
  exact eq_neg_of_add_eq_zero_left hz

section Local
variable {G : Type*} [Group G] (a : G →* Equiv.Perm S)
  (commutes : ∀ g h s, a g (r h s) = r h (a g s))

include commutes in
theorem actions_commute (n d : ℕ) (g : G) (h : H) (p : grade (S := S) (I := I) n d) :
    action a n d g (action r n d h p) = action r n d h (action a n d g p) := by
  apply Subtype.ext
  change relabel (a g) (relabel (r h) p.val) = relabel (r h) (relabel (a g) p.val)
  simp only [relabel, MvPolynomial.rename_rename]
  apply congrArg (fun f : Index S I → Index S I => MvPolynomial.rename f p.val)
  funext j
  exact Prod.ext (commutes g h j.1) rfl

abbrev LocalCoefficient (n d : ℕ) :=
  LocalRelationHom.Input (action (I := I) a n (d + 1))
    (action r n (d + 1)) (trivial ℂ H ℂ) (relations S I n d)

abbrev residual (n d : ℕ) := LocalRelationHom.residual
  (action (I := I) a n (d + 1)) (action r n (d + 1))
  (actions_commute r a commutes n (d + 1)) (relations S I n d) (relations_stable r n d)

def localEquiv (n d : ℕ) : LocalCoefficient (I := I) r a n d ≃ₗ[ℂ]
    IntertwiningMap (residual (I := I) r a commutes n d) (trivial ℂ H ℂ) :=
  LocalRelationHom.equiv _ _ _ (actions_commute r a commutes n (d + 1)) _ (relations_stable r n d)

theorem localEquiv_mk (n d : ℕ) (f : LocalCoefficient (I := I) r a n d)
    (p : grade (S := S) (I := I) n (d + 1)) :
    localEquiv r a commutes n d f ((LocalRelationHom.image
      (action (I := I) a n (d + 1)) (relations S I n d)).mkQ
        ((LocalCoinvariantHom.relations (action (I := I) a n (d + 1))).mkQ p)) =
      f.val.val p := rfl

theorem local_forbidden_iff (n d : ℕ) :
    (∀ f : LocalCoefficient (I := I) r a n d, f = 0) ↔
      ∀ f : IntertwiningMap (residual (I := I) r a commutes n d) (trivial ℂ H ℂ), f = 0 := by
  constructor
  · intro h f
    exact (localEquiv r a commutes n d).symm.injective
      ((h _).trans (localEquiv r a commutes n d).symm.map_zero.symm)
  · intro h f
    exact (localEquiv r a commutes n d).injective
      ((h _).trans (localEquiv r a commutes n d).map_zero.symm)

theorem local_nonzero_iff (n d : ℕ) :
    (∃ f : LocalCoefficient (I := I) r a n d, f ≠ 0) ↔
      ∃ f : IntertwiningMap (residual (I := I) r a commutes n d) (trivial ℂ H ℂ), f ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (local_forbidden_iff (I := I) r a commutes n d)
end Local

end
end Math.ScalarJetIBP

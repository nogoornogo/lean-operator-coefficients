import Math.RepresentationTheory.Weights.BoundedTorusWeights
import Math.RepresentationTheory.SU2.TwistedSU2ClebschGordan
import Math.RepresentationTheory.Constructions.FiniteConstituentSupport

/-! A bounded source reduces the one-doublet Higgs support to finitely many
full-group Hom tests. The residual action remains in each test. -/
namespace Math.BoundedHiggsSupport
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct
variable {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G X) (j : G →* WeakDoubletScalars.Group) (chi : G →* ℂˣ)
  (k : WeakDoubletScalars.Group →* G)

abbrev constituent (m : ℕ) (delta : ℤ) :=
  charTwist (chi ^ delta) ((doublet.symmetricPower m).comp j)
abbrev Test (m : ℕ) (delta : ℤ) :=
  InvariantCoefficientTransport.Invariants (a.tprod (constituent j chi m delta))
abbrev Space (h d : ℕ) := InvariantCoefficientTransport.Invariants
  (a.tprod (TwistedSU2ClebschGordan.Bosons j chi h d))

variable (hj : ∀ u, j (k u) = u) (hc : ∀ u, chi (k u) = 1)

include hj hc in
theorem constituent_weak (m : ℕ) (delta : ℤ) (u : WeakDoubletScalars.Group)
    (v : Sym[ℂ]^m Doublet) :
    constituent j chi m delta (k u) v = doublet.symmetricPower m u v := by
  change ((chi^delta) (k u) : ℂˣ) • doublet.symmetricPower m (j (k u)) v = _
  simp [hj, hc]

include hj hc in
def weakCurry (m : ℕ) (delta : ℤ) (f : Test a j chi m delta) :
    IntertwiningMap (doublet.symmetricPower m) (Representation.dual (a.comp k)) where
  toLinearMap := TensorProduct.curry
    (f.toLinearMap.comp (TensorProduct.comm ℂ _ _).toLinearMap)
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro x
    change f (x ⊗ₜ[ℂ] doublet.symmetricPower m u v) =
      f (a (k u⁻¹) x ⊗ₜ[ℂ] v)
    have he := f.isIntertwining _ _ (k u) (a (k u⁻¹) x ⊗ₜ[ℂ] v)
    change f (a (k u) (a (k u⁻¹) x) ⊗ₜ[ℂ]
      constituent j chi m delta (k u) v) = f (a (k u⁻¹) x ⊗ₜ[ℂ] v) at he
    rw [constituent_weak j chi k hj hc] at he
    simpa [← Module.End.mul_apply, ← map_mul] using he

include hj hc in
theorem high_zero (N m : ℕ) (delta : ℤ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N)
    (hm : N < m) (f : Test a j chi m delta) : f=0 := by
  have hz := BoundedTorusWeights.high_spin_hom_zero (a.comp k) N m ha hm
    (weakCurry a j chi k hj hc m delta f)
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x v
  exact congrArg (fun phi : Module.Dual ℂ X => phi x) (DFunLike.congr_fun hz v)

theorem charge_eq (h d : ℕ) : TwistedSU2ClebschGordan.charge chi h d = chi ^ ((h : ℤ)-d) := by
  ext g
  simp [TwistedSU2ClebschGordan.charge, zpow_sub, inv_pow]

def summandEquiv (h d : ℕ) (r : SU2ClebschGordan.Index h d) : Representation.Equiv
    (TwistedSU2ClebschGordan.summand j chi h d r)
    (constituent j chi (SU2ClebschGordan.degree h d r) ((h : ℤ)-d)) := by
  unfold TwistedSU2ClebschGordan.summand constituent
  rw [charge_eq]
  exact .refl _

theorem per_degree_allowed (h d : ℕ) : SelectionCriteria.Allowed (Space a j chi h d) ↔
    ∃ r : SU2ClebschGordan.Index h d,
      SelectionCriteria.Allowed (Test a j chi (SU2ClebschGordan.degree h d r) ((h : ℤ)-d)) := by
  rw [SelectionCriteria.allowed_equiv
    (InvariantCoefficientTransport.alongEquiv
      (ExternalInvariantTensor.tensorEquiv (.refl a) (TwistedSU2ClebschGordan.equivalence j chi h d))),
    FiniteConstituentSupport.allowed_iff]
  apply exists_congr
  intro r
  exact SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (.refl a) (summandEquiv j chi h d r)))

def Admissible (h d m : ℕ) : Prop :=
  m ≤ h+d ∧ h ≤ d+m ∧ d ≤ h+m ∧ (h+d-m)%2=0

theorem degree_admissible (h d : ℕ) (r : SU2ClebschGordan.Index h d) :
    Admissible h d (SU2ClebschGordan.degree h d r) := by
  rw [SU2ClebschGordan.degree_eq]
  have hr := r.isLt
  have hh := Nat.min_le_left h d
  have hd := Nat.min_le_right h d
  dsimp [Admissible]
  omega

theorem exists_index (h d m : ℕ) (hm : Admissible h d m) :
    ∃ r : SU2ClebschGordan.Index h d, SU2ClebschGordan.degree h d r = m := by
  rcases hm with ⟨hlo,hh,hd,hpar⟩
  have hr : (h+d-m)/2 < min h d+1 := by omega
  refine ⟨⟨(h+d-m)/2,hr⟩, ?_⟩
  rw [SU2ClebschGordan.degree_eq]
  change h+d-2*((h+d-m)/2) = m
  omega

include hj hc in
theorem finite_allowed_iff (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N) (h d : ℕ) :
    SelectionCriteria.Allowed (Space a j chi h d) ↔
      ∃ m : Fin (N+1), Admissible h d m.val ∧
        SelectionCriteria.Allowed (Test a j chi m.val ((h : ℤ)-d)) := by
  rw [per_degree_allowed]
  constructor
  · rintro ⟨r,f,hf⟩
    have hm : SU2ClebschGordan.degree h d r ≤ N := by
      by_contra hn
      exact hf (high_zero a j chi k hj hc N _ _ ha (by omega) f)
    exact ⟨⟨SU2ClebschGordan.degree h d r,by omega⟩,
      degree_admissible h d r, f,hf⟩
  · rintro ⟨m,hm,ht⟩
    obtain ⟨r,hr⟩ := exists_index h d m.val hm
    refine ⟨r, ?_⟩
    rw [hr]
    exact ht

theorem admissible_pair (h d m : ℕ) (hm : Admissible h d m) :
    Admissible (h+1) (d+1) m := by
  dsimp [Admissible] at *
  omega

theorem admissible_stable (N h d m : ℕ) (hm : m ≤ N) (ht : N ≤ h+d+1) :
    Admissible (h+1) (d+1) m ↔ Admissible h d m := by
  dsimp [Admissible]
  omega

include hj hc in
theorem pair_monotone (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N) (h d : ℕ) :
    SelectionCriteria.Allowed (Space a j chi h d) →
      SelectionCriteria.Allowed (Space a j chi (h+1) (d+1)) := by
  rw [finite_allowed_iff a j chi k hj hc N ha,
    finite_allowed_iff a j chi k hj hc N ha]
  rintro ⟨m,hm,ht⟩
  refine ⟨m,admissible_pair h d m.val hm, ?_⟩
  have he : ((h+1 : ℕ) : ℤ) - ((d+1 : ℕ) : ℤ) = (h : ℤ)-d := by omega
  exact he.symm ▸ ht

include hj hc in
theorem pair_stable (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N)
    (h d : ℕ) (ht : N ≤ h+d+1) :
    SelectionCriteria.Allowed (Space a j chi (h+1) (d+1)) ↔
      SelectionCriteria.Allowed (Space a j chi h d) := by
  rw [finite_allowed_iff a j chi k hj hc N ha,
    finite_allowed_iff a j chi k hj hc N ha]
  have he : ((h+1 : ℕ) : ℤ) - ((d+1 : ℕ) : ℤ) = (h : ℤ)-d := by omega
  change (∃ m : Fin (N+1), Admissible (h+1) (d+1) m.val ∧
    SelectionCriteria.Allowed (Test a j chi m.val (((h+1 : ℕ) : ℤ)-((d+1 : ℕ) : ℤ)))) ↔ _
  rw [he]
  apply exists_congr
  intro m
  rw [admissible_stable N h d m.val (by have := m.isLt; omega) ht]

include hj hc in
theorem finite_table_iff (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N) (h d : ℕ) :
    SelectionCriteria.Allowed (Space a j chi h d) ↔
      ∃ s t : Fin (N+1), s.val+t.val ≤ N ∧
        (h : ℤ)-d = (s.val : ℤ)-t.val ∧ Admissible h d (s.val+t.val) ∧
        SelectionCriteria.Allowed (Test a j chi (s.val+t.val) ((s.val : ℤ)-t.val)) := by
  rw [finite_allowed_iff a j chi k hj hc N ha]
  constructor
  · rintro ⟨m,hm,ht⟩
    obtain ⟨r,hr⟩ := exists_index h d m.val hm
    have hrh : r.val ≤ h := (Nat.le_of_lt_succ r.isLt).trans (Nat.min_le_left h d)
    have hrd : r.val ≤ d := (Nat.le_of_lt_succ r.isLt).trans (Nat.min_le_right h d)
    have hdg : (h-r.val)+(d-r.val) = m.val := by
      simpa only [SU2ClebschGordan.degree] using hr
    have hn := m.isLt
    let s : Fin (N+1) := ⟨h-r.val,by omega⟩
    let t : Fin (N+1) := ⟨d-r.val,by omega⟩
    have hs : s.val+t.val=m.val := hdg
    have he : (h : ℤ)-d = (s.val : ℤ)-t.val := by dsimp [s,t]; omega
    refine ⟨s,t,by omega,he,by simpa only [hs] using hm,?_⟩
    rw [hs, ← he]
    exact ht
  · rintro ⟨s,t,hn,he,hm,ht⟩
    refine ⟨⟨s.val+t.val,by omega⟩,hm,?_⟩
    rw [he]
    exact ht

include hj hc in
theorem imbalance_forbidden (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N)
    (h d : ℕ) (hbad : N < (h-d)+(d-h)) :
    SelectionCriteria.Forbidden (Space a j chi h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, finite_allowed_iff a j chi k hj hc N ha]
  rintro ⟨m,hm,ht⟩
  have hn := m.isLt
  dsimp [Admissible] at hm
  omega

include hj hc in
theorem pair_stable_at_threshold (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N)
    (h d : ℕ) (hdelta : (h-d)+(d-h) ≤ N)
    (ht : (N-((h-d)+(d-h)))/2 ≤ min h d) :
    SelectionCriteria.Allowed (Space a j chi (h+1) (d+1)) ↔
      SelectionCriteria.Allowed (Space a j chi h d) := by
  apply pair_stable a j chi k hj hc N ha h d
  rcases Nat.le_total h d with hh | hh
  · rw [Nat.min_eq_left hh] at ht
    omega
  · rw [Nat.min_eq_right hh] at ht
    omega

def constituentCast {m q : ℕ} (he : m=q) (delta : ℤ) : Representation.Equiv
    (constituent j chi m delta) (constituent j chi q delta) := by
  subst q
  exact .refl _

def representativeEquiv (s t : ℕ) : Representation.Equiv
    (TwistedSU2ClebschGordan.summand j chi s t ⟨0,by omega⟩)
    (constituent j chi (s+t) ((s : ℤ)-t)) :=
  (summandEquiv j chi s t ⟨0,by omega⟩).trans
    (constituentCast j chi (by simp [SU2ClebschGordan.degree]) ((s : ℤ)-t))

include hj hc in
theorem pairs_stable (N : ℕ)
    (ha : BoundedTorusWeights.Bounded (a.comp k) TauCeti.SU2.torusHom N)
    (h d : ℕ) (ht : N ≤ h+d+1) (r : ℕ) :
    SelectionCriteria.Allowed (Space a j chi (h+r) (d+r)) ↔
      SelectionCriteria.Allowed (Space a j chi h d) := by
  induction r with
  | zero => simp only [Nat.add_zero]
  | succ r ih =>
    exact (pair_stable a j chi k hj hc N ha (h+r) (d+r) (by omega)).trans ih

end
end Math.BoundedHiggsSupport

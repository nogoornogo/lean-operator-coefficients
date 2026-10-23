import Math.RepresentationTheory.Invariants.MultilinearInvariantHom
import Mathlib.LinearAlgebra.Alternating.Basic
import TauCeti.RepresentationTheory.ExteriorPower

/-! One occurrence of each distinct species: ordered multilinear coefficients
and alternating coefficients on the field sum. No contraction ansatz is used. -/
namespace Math.DistinctSpeciesAlternation
set_option autoImplicit false
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev Fields (V : ι → Type*) := ∀ i, V i

def ordered (f : MultilinearMap ℂ V W) :
    MultilinearMap ℂ (fun _ : ι => Fields V) W :=
  f.compLinearMap (fun i => LinearMap.proj i)

def assemble (f : MultilinearMap ℂ V W) : Fields V [⋀^ι]→ₗ[ℂ] W :=
  (ordered f).alternatization

def restrict (f : Fields V [⋀^ι]→ₗ[ℂ] W) : MultilinearMap ℂ V W :=
  f.toMultilinearMap.compLinearMap (fun i => LinearMap.single ℂ V i)

theorem restrict_assemble (f : MultilinearMap ℂ V W) : restrict (assemble f) = f := by
  ext v
  change (ordered f).alternatization (fun i => Pi.single i (v i)) = f v
  rw [MultilinearMap.alternatization_apply, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp [ordered, MultilinearMap.domDomCongr_apply]
  · intro p _ hp
    have hex : ∃ i, p i ≠ i := by
      by_contra h
      apply hp
      ext i
      simpa using not_exists.mp h i
    obtain ⟨i, hi⟩ := hex
    have hz : f (fun j => (Pi.single (p j) (v (p j))) j) = 0 := by
      apply f.map_coord_zero i
      simp [Ne.symm hi]
    simpa [MultilinearMap.domDomCongr_apply, ordered] using
      congrArg (fun w : W => Equiv.Perm.sign p • w) hz
  · simp

/-- Intrinsic support: a pure field tuple with a repeated or missing species vanishes. -/
def HasDegree (f : Fields V [⋀^ι]→ₗ[ℂ] W) : Prop :=
  ∀ (s : ι → ι) (v : ι → Fields V), ¬ Function.Bijective s →
    f (fun i => Pi.single (s i) (v i (s i))) = 0

theorem assemble_hasDegree (f : MultilinearMap ℂ V W) : HasDegree (assemble f) := by
  intro s v hs
  have hns : ¬ Function.Surjective s := by
    intro h
    exact hs ⟨(Finite.injective_iff_surjective).mpr h, h⟩
  obtain ⟨j, hj⟩ := not_forall.mp hns
  have hj' : ∀ i, s i ≠ j := by simpa using hj
  rw [assemble, MultilinearMap.alternatization_apply]
  apply Finset.sum_eq_zero
  intro p _
  have hz : f (fun k => (Pi.single (s (p k)) (v (p k) (s (p k)))) k) = 0 := by
    apply f.map_coord_zero j
    simp [Ne.symm (hj' (p j))]
  simpa [MultilinearMap.domDomCongr_apply, ordered] using
    congrArg (fun w : W => Equiv.Perm.sign p • w) hz

theorem support_ext (f g : Fields V [⋀^ι]→ₗ[ℂ] W)
    (hf : HasDegree f) (hg : HasDegree g) (h : restrict f = restrict g) : f = g := by
  have hpure (s : ι → ι) (v : ι → Fields V) :
      f (fun i => Pi.single (s i) (v i (s i))) =
        g (fun i => Pi.single (s i) (v i (s i))) := by
    by_cases hs : Function.Bijective s
    · let p := (Equiv.ofBijective s hs).symm
      have hw : (fun i => Pi.single (s i) (v i (s i))) ∘ p =
          fun i => Pi.single i (v (p i) i) := by
        funext i
        have hi : s (p i) = i := (Equiv.ofBijective s hs).apply_symm_apply i
        change Pi.single (s (p i)) (v (p i) (s (p i))) = Pi.single i (v (p i) i)
        rw [hi]
      calc
        _ = Equiv.Perm.sign p • f ((fun i => Pi.single (s i) (v i (s i))) ∘ p) :=
          f.map_congr_perm _ p
        _ = Equiv.Perm.sign p • g ((fun i => Pi.single (s i) (v i (s i))) ∘ p) := by
          rw [hw]
          exact congrArg (Equiv.Perm.sign p • ·)
            (DFunLike.congr_fun h (fun i => v (p i) i))
        _ = _ := (g.map_congr_perm _ p).symm
    · rw [hf s v hs, hg s v hs]
  ext v
  have hv : v = fun i => ∑ j, Pi.single j (v i j) := by
    funext i
    exact (Finset.univ_sum_single (v i)).symm
  rw [hv]
  calc
    _ = ∑ s : ι → ι, f (fun i => Pi.single (s i) (v i (s i))) :=
      f.toMultilinearMap.map_sum (fun i j => Pi.single j (v i j))
    _ = ∑ s : ι → ι, g (fun i => Pi.single (s i) (v i (s i))) :=
      Finset.sum_congr rfl (fun s _ => hpure s v)
    _ = _ := (g.toMultilinearMap.map_sum (fun i j => Pi.single j (v i j))).symm

def sector : Submodule ℂ (Fields V [⋀^ι]→ₗ[ℂ] W) where
  carrier := {f | HasDegree f}
  zero_mem' := by intro s v h; rfl
  add_mem' := by intro f g hf hg s v h; change f _ + g _ = 0; rw [hf s v h, hg s v h, add_zero]
  smul_mem' := by intro z f hf s v h; change z • f _ = 0; rw [hf s v h, smul_zero]

def equiv : MultilinearMap ℂ V W ≃ₗ[ℂ] sector (V := V) (W := W) where
  toFun f := ⟨assemble f, assemble_hasDegree f⟩
  invFun f := restrict f.val
  left_inv := restrict_assemble
  right_inv f := by
    apply Subtype.ext
    exact support_ext _ _ (assemble_hasDegree _) f.property (restrict_assemble _)
  map_add' f g := by
    apply Subtype.ext
    exact support_ext _ _ (assemble_hasDegree _) ((sector (V := V) (W := W)).add_mem
      (assemble_hasDegree f) (assemble_hasDegree g)) (by
        rw [restrict_assemble]
        change f + g = restrict (assemble f) + restrict (assemble g)
        rw [restrict_assemble, restrict_assemble])
  map_smul' z f := by
    apply Subtype.ext
    exact support_ext _ _ (assemble_hasDegree _) ((sector (V := V) (W := W)).smul_mem z
      (assemble_hasDegree f)) (by
        rw [restrict_assemble]
        change z • f = z • restrict (assemble f)
        rw [restrict_assemble])

section Invariant
variable {G : Type*} [Group G] (r : ∀ i, Representation ℂ G (V i))

omit [Fintype ι] in
theorem action_single (g : G) (i : ι) (v : V i) :
    (fun j => r j g (Pi.single i v j)) = Pi.single i (r i g v) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

def invariantSector : Submodule ℂ (Fields V [⋀^ι]→ₗ[ℂ] W) where
  carrier := {f | HasDegree f ∧ ∀ g v, f (fun i j => r j g (v i j)) = f v}
  zero_mem' := ⟨(sector (V := V) (W := W)).zero_mem, by intro g v; rfl⟩
  add_mem' := by
    rintro f h ⟨hf,hi⟩ ⟨hh,hj⟩
    exact ⟨(sector (V := V) (W := W)).add_mem hf hh,
      fun g v => congrArg₂ (· + ·) (hi g v) (hj g v)⟩
  smul_mem' := by
    rintro z f ⟨hf,hi⟩
    exact ⟨(sector (V := V) (W := W)).smul_mem z hf,
      fun g v => congrArg (z • ·) (hi g v)⟩

def invariantAssemble (f : MultilinearInvariantHom.invariantMaps (W := W) r) :
    invariantSector (W := W) r :=
  ⟨assemble f.val, assemble_hasDegree f.val, by
    intro g v
    simp only [assemble, MultilinearMap.alternatization_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (Equiv.Perm.sign p • ·) (f.property g (fun i => v (p i) i))⟩

def invariantRestrict (f : invariantSector (W := W) r) :
    MultilinearInvariantHom.invariantMaps (W := W) r :=
  ⟨restrict f.val, by
    intro g v
    have h := f.property.2 g (fun i => Pi.single i (v i))
    change f.val (fun i j => r j g (Pi.single i (v i) j)) = _ at h
    have he : (fun i j => r j g (Pi.single i (v i) j)) =
        (fun i => Pi.single i (r i g (v i))) := by
      funext i
      exact action_single r g i (v i)
    rw [he] at h
    exact h⟩

def invariantEquiv : MultilinearInvariantHom.invariantMaps (W := W) r ≃ₗ[ℂ]
    invariantSector (W := W) r where
  toFun := invariantAssemble r
  invFun := invariantRestrict r
  left_inv f := by apply Subtype.ext; exact restrict_assemble f.val
  right_inv f := by
    apply Subtype.ext
    exact support_ext _ _ (assemble_hasDegree _) f.property.1 (restrict_assemble _)
  map_add' f g := by
    apply Subtype.ext
    exact congrArg (fun k : sector (V := V) (W := W) => k.val) (equiv.map_add f.val g.val)
  map_smul' z f := by
    apply Subtype.ext
    exact congrArg (fun k : sector (V := V) (W := W) => k.val) (equiv.map_smul z f.val)

end Invariant

end

section Exterior
noncomputable section
open Representation
variable {n : ℕ} {G : Type*} [Group G]
  {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (r : ∀ i, Representation ℂ G (V i))

def sumRepresentation : Representation ℂ G (Fields V) where
  toFun g := LinearMap.pi (fun i => (r i g).comp (LinearMap.proj i))
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp

abbrev ExteriorCoefficient := IntertwiningMap ((sumRepresentation r).exteriorPower n)
  (Representation.trivial ℂ G ℂ)

def evaluation (f : ExteriorCoefficient r) : Fields V [⋀^Fin n]→ₗ[ℂ] ℂ :=
  f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ n)

def exteriorSector : Submodule ℂ (ExteriorCoefficient r) where
  carrier := {f | HasDegree (evaluation r f)}
  zero_mem' := by intro s v h; rfl
  add_mem' := by
    intro f g hf hg s v h
    change f _ + g _ = 0
    exact add_eq_zero_iff_eq_neg.mpr (by rw [show f _ = 0 from hf s v h,
      show g _ = 0 from hg s v h, neg_zero])
  smul_mem' := by intro z f hf s v h; change z • f _ = 0; rw [show f _ = 0 from hf s v h, smul_zero]

def descend (f : invariantSector (W := ℂ) r) : exteriorSector r :=
  ⟨{ toLinearMap := exteriorPower.alternatingMapLinearEquiv f.val
     isIntertwining' g := by
       apply exteriorPower.linearMap_ext
       apply AlternatingMap.ext
       intro v
       simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
         Representation.exteriorPower_apply_ιMulti,
         exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
       exact f.property.2 g v }, by
    intro s v h
    exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f.val _).trans
      (f.property.1 s v h)⟩

def liftEvaluation (f : exteriorSector r) : invariantSector (W := ℂ) r :=
  ⟨evaluation r f.val, f.property, by
    intro g v
    have h := IntertwiningMap.isIntertwining _ _ f.val g (exteriorPower.ιMulti ℂ n v)
    rw [Representation.exteriorPower_apply_ιMulti] at h
    exact h⟩

def exteriorEquiv : invariantSector (W := ℂ) r ≃ₗ[ℂ] exteriorSector r where
  toFun := descend r
  invFun := liftEvaluation r
  left_inv f := by
    apply Subtype.ext
    ext v
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply exteriorPower.linearMap_ext
    ext v
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  map_add' f g := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact exteriorPower.alternatingMapLinearEquiv.map_add f.val g.val
  map_smul' z f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact exteriorPower.alternatingMapLinearEquiv.map_smul z f.val

/-- Independent one-of-each exterior coefficients are exactly ordered tensor invariants. -/
def exteriorHomEquiv : exteriorSector r ≃ₗ[ℂ]
    IntertwiningMap (MultilinearInvariantHom.tensorRepresentation r)
      (Representation.trivial ℂ G ℂ) :=
  (exteriorEquiv r).symm.trans
    ((invariantEquiv r).symm.trans (MultilinearInvariantHom.equiv r))

end
end Exterior
end Math.DistinctSpeciesAlternation

import Math.RepresentationTheory.BoundedHiggsSupport
import Mathlib.RingTheory.Flat.Basic

/-! Uniform nonzero constituent witnesses from Clebsch--Gordan, without multiplicity numerals. -/
namespace Math.SU2SymmetricSupport
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct

def pullback {G V W : Type*} [Group G] [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] {r : Representation ℂ Group V}
    {s : Representation ℂ Group W} (j : G →* Group) (f : IntertwiningMap r s) :
    IntertwiningMap (r.comp j) (s.comp j) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (j g)

theorem couple (h d m : ℕ) (ha : BoundedHiggsSupport.Admissible h d m) :
    ∃ f : IntertwiningMap (doublet.symmetricPower m)
      ((doublet.symmetricPower h).tprod (doublet.symmetricPower d)), Function.Injective f := by
  obtain ⟨r, hr⟩ := BoundedHiggsSupport.exists_index h d m ha
  subst m
  exact ⟨SU2ClebschGordan.embed h d r, SU2ClebschGordan.embed_injective h d r⟩

theorem pair (k m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 2*k) :
    ∃ f : IntertwiningMap (doublet.symmetricPower m)
      ((doublet.symmetricPower k).tprod (doublet.symmetricPower k)), Function.Injective f :=
  couple k k m (by dsimp [BoundedHiggsSupport.Admissible]; omega)

theorem triple (k m : ℕ) (hk : k % 2 = 0) (hm : m % 2 = 0) (hmax : m ≤ 3*k) :
    ∃ f : IntertwiningMap (doublet.symmetricPower m)
      ((doublet.symmetricPower k).tprod
        ((doublet.symmetricPower k).tprod (doublet.symmetricPower k))), Function.Injective f := by
  let p := if m ≤ 2*k then k else 2*k
  have hp : p % 2 = 0 ∧ p ≤ 2*k := by dsimp [p]; split_ifs <;> omega
  have ha : BoundedHiggsSupport.Admissible p k m := by
    dsimp [p, BoundedHiggsSupport.Admissible]
    split_ifs <;> omega
  obtain ⟨f, hf⟩ := pair k p hp.1 hp.2
  obtain ⟨g, hg⟩ := couple p k m ha
  let t := f.tensor (IntertwiningMap.id (doublet.symmetricPower k))
  let e := Representation.TensorProduct.assoc (doublet.symmetricPower k)
    (doublet.symmetricPower k) (doublet.symmetricPower k)
  have ht : Function.Injective t :=
    TensorProduct.map_injective_of_flat_flat _ _ hf Function.injective_id
  exact ⟨e.toIntertwiningMap.comp (t.comp g), e.injective.comp (ht.comp hg)⟩

end
end Math.SU2SymmetricSupport

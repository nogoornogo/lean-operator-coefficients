import GUT.SU5.Embeddings.PhysicalTorus
import GUT.SU6.Branching.StandardSMCharacterTarget

open Math

/-! Exact comparison with the legacy physical Fourier evaluator. This
adapter may import SU(6); the new SU(5) source and its audit do not. -/

set_option autoImplicit false

namespace GUT.SU6.SU5TorusCompatibility

noncomputable section

open StandardAbelianCharge FiniteAbelianChargeSectors

theorem exponent_eq (w : ReducedWeight) :
    SU5.PhysicalTorus.exponent w = StandardSMCharacterTarget.standardExponent w := rfl

theorem eval_eq {H : Type*} [CommGroup H] (p : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    SU5.TorusCharacter.eval p
        (SU5.PhysicalTorus.toTorus (fun i => AddCircle.toCircle (x i)), h) =
      StandardSMCharacterTarget.eval p x h := by
  unfold SU5.TorusCharacter.eval StandardSMCharacterTarget.eval
  apply Finset.sum_congr rfl
  intro key _
  dsimp only
  rw [SU5.TorusCharacter.keyCharacter_apply, SU5.PhysicalTorus.weightCharacter_fourier,
    exponent_eq, StandardSMCharacterTarget.keyMonoidHom_apply]
  rfl

def circleCoordinates : PhysicalSMTorusTarget.Group →* SU5.PhysicalTorus.Coordinates where
  toFun x i := AddCircle.toCircle (x.toAdd i)
  map_one' := by funext i; exact AddCircle.toCircle_zero
  map_mul' x y := by funext i; exact AddCircle.toCircle_add _ _

theorem circleCoordinates_surjective : Function.Surjective circleCoordinates := by
  intro z
  refine ⟨Multiplicative.ofAdd (fun i => (AddCircle.homeomorphCircle one_ne_zero).symm (z i)), ?_⟩
  funext i
  change AddCircle.toCircle ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (z i)) = z i
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (z i)

def torusCover : PhysicalSMTorusTarget.Group →* SU5.MaximalTorus.Torus :=
  SU5.PhysicalTorus.toTorus.comp circleCoordinates

theorem torusCover_surjective : Function.Surjective torusCover :=
  SU5.PhysicalTorus.toTorus_surjective.comp circleCoordinates_surjective

def cover {H : Type*} [CommGroup H] : StandardSMCharacterTarget.CombinedGroup H →*
    SU5.TorusCharacter.CombinedGroup H := torusCover.prodMap (MonoidHom.id H)

theorem cover_surjective {H : Type*} [CommGroup H] : Function.Surjective (cover (H := H)) := by
  rintro ⟨t, h⟩
  obtain ⟨x, hx⟩ := torusCover_surjective t
  exact ⟨(x, h), Prod.ext hx rfl⟩

theorem key_comp_cover {H : Type*} [CommGroup H] (key : ResolvedKey (ChargeLabel H)) :
    (SU5.TorusCharacter.keyCharacter key).comp cover = StandardSMCharacterTarget.keyMonoidHom key := by
  ext g
  change SU5.TorusCharacter.keyCharacter key
    (SU5.PhysicalTorus.toTorus (fun i => AddCircle.toCircle (g.1.toAdd i)), g.2) = _
  rw [SU5.TorusCharacter.keyCharacter_apply, SU5.PhysicalTorus.weightCharacter_fourier,
    exponent_eq, StandardSMCharacterTarget.keyMonoidHom_apply]

end

end GUT.SU6.SU5TorusCompatibility

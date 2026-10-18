import Math.LinearAlgebra.BinaryExteriorProduct
import Math.RepresentationTheory.TopExteriorCauchy

/-! Independent generation summands give injective exterior multiplication. -/
namespace Math.GenerationExteriorBlocks
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def binary (r : Representation ℂ G V) (s : Representation ℂ G W) (n m : ℕ) :
    IntertwiningMap ((r.exteriorPower n).tprod (s.exteriorPower m))
      ((r.prod s).exteriorPower (n+m)) where
  toLinearMap := BinaryExteriorProduct.map n m
  isIntertwining' g := by
    apply BinaryExteriorProduct.ext
    intro v w
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti, BinaryExteriorProduct.map_pure]
    apply congrArg (exteriorPower.ιMulti ℂ (n+m))
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [Function.comp_def, Representation.prod]

def join : (V × (V × V)) →ₗ[ℂ] V ⊗[ℂ] (Fin 3 → ℂ) :=
  ((TensorProduct.mk ℂ V (Fin 3 → ℂ)).flip (Pi.single 0 1)).comp
      (LinearMap.fst ℂ V (V × V)) +
    ((TensorProduct.mk ℂ V (Fin 3 → ℂ)).flip (Pi.single 1 1)).comp
      ((LinearMap.fst ℂ V V).comp (LinearMap.snd ℂ V (V × V))) +
    ((TensorProduct.mk ℂ V (Fin 3 → ℂ)).flip (Pi.single 2 1)).comp
      ((LinearMap.snd ℂ V V).comp (LinearMap.snd ℂ V (V × V)))

theorem join_injective : Function.Injective (join (V := V)) := by
  intro x y he
  have h (i : Fin 3) := congrArg (TopExteriorCauchy.evaluate (A := V) (LinearMap.proj i)) he
  apply Prod.ext
  · simpa [join] using h 0
  · apply Prod.ext
    · simpa [join] using h 1
    · simpa [join] using h 2

def joinIntertwiner (r : Representation ℂ G V) :
    IntertwiningMap (r.prod (r.prod r))
      (r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))) where
  toLinearMap := join
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    simp [join, Representation.prod, Representation.tprod_apply,
      TensorProduct.map_tmul]

def triple (r : Representation ℂ G V) (n m l : ℕ) :
    IntertwiningMap ((r.exteriorPower n).tprod
      ((r.exteriorPower m).tprod (r.exteriorPower l)))
      ((r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))).exteriorPower (n+(m+l))) :=
  ((joinIntertwiner r).exteriorPower (n+(m+l))).comp
    ((binary r (r.prod r) n (m+l)).comp
      ((IntertwiningMap.id (r.exteriorPower n)).tensor (binary r r m l)))

theorem triple_injective (r : Representation ℂ G V) (n m l : ℕ) :
    Function.Injective (triple r n m l) := by
  exact (exteriorPower.map_injective_field (n := n+(m+l)) join_injective).comp
    ((BinaryExteriorProduct.injective n (m+l)).comp
      (TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
        (BinaryExteriorProduct.injective m l)))

def includeTwo (r : Representation ℂ G V) :
    IntertwiningMap (r.prod r) (r.prod (r.prod r)) where
  toLinearMap := (LinearMap.fst ℂ V V).prod
    ((LinearMap.snd ℂ V V).prod (0 : V × V →ₗ[ℂ] V))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change (r g x.1, (r g x.2, 0)) = (r g x.1, (r g x.2, r g 0))
    rw [map_zero]

theorem includeTwo_injective (r : Representation ℂ G V) :
    Function.Injective (includeTwo r) := by
  intro x y h
  change (x.1,(x.2,0)) = (y.1,(y.2,0)) at h
  exact Prod.ext (congrArg (fun z : V × (V × V) => z.1) h)
    (congrArg (fun z : V × (V × V) => z.2.1) h)

def pair (r : Representation ℂ G V) (n m : ℕ) :
    IntertwiningMap ((r.exteriorPower n).tprod (r.exteriorPower m))
      ((r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))).exteriorPower (n+m)) :=
  (((joinIntertwiner r).comp (includeTwo r)).exteriorPower (n+m)).comp (binary r r n m)

theorem pair_injective (r : Representation ℂ G V) (n m : ℕ) :
    Function.Injective (pair r n m) :=
  (exteriorPower.map_injective_field (n := n+m)
    (join_injective.comp (includeTwo_injective r))).comp (BinaryExteriorProduct.injective n m)

def pairMap {r : Representation ℂ G V} {a : Representation ℂ G W} {k : ℕ}
    (f : IntertwiningMap a (r.exteriorPower k)) :
    IntertwiningMap (a.tprod a)
      ((r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))).exteriorPower (k+k)) :=
  (pair r k k).comp (f.tensor f)

theorem pairMap_injective {r : Representation ℂ G V} {a : Representation ℂ G W} {k : ℕ}
    (f : IntertwiningMap a (r.exteriorPower k)) (hf : Function.Injective f) :
    Function.Injective (pairMap f) :=
  (pair_injective r k k).comp (TensorProduct.map_injective_of_flat_flat _ _ hf hf)

def tripleMap {r : Representation ℂ G V} {a : Representation ℂ G W} {k : ℕ}
    (f : IntertwiningMap a (r.exteriorPower k)) :
    IntertwiningMap (a.tprod (a.tprod a))
      ((r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))).exteriorPower (k+(k+k))) :=
  (triple r k k k).comp (f.tensor (f.tensor f))

theorem tripleMap_injective {r : Representation ℂ G V} {a : Representation ℂ G W} {k : ℕ}
    (f : IntertwiningMap a (r.exteriorPower k)) (hf : Function.Injective f) :
    Function.Injective (tripleMap f) :=
  (triple_injective r k k k).comp (TensorProduct.map_injective_of_flat_flat _ _ hf
    (TensorProduct.map_injective_of_flat_flat _ _ hf hf))

end
end Math.GenerationExteriorBlocks

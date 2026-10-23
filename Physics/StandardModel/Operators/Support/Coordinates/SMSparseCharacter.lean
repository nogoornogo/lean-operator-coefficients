import Physics.StandardModel.Operators.Support.Decomposition.SMComputableSupport
import Math.RepresentationTheory.Weights.SparseWeightPolynomial

/-! Aggregated six-integer keys and actual compact character semantics. -/
namespace Physics.SMSparseCharacter
set_option autoImplicit false
open Math Representation SMCompactTorus ComputableWeightPolynomial

abbrev Key := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ
attribute [local instance] lexOrd
instance keyOrd : Ord Key := inferInstance
instance keyLawfulOrd : Std.LawfulEqOrd Key := inferInstance
instance keyDecidableEq : DecidableEq Key := inferInstance
instance termDecidableEq : DecidableEq (Key × ℤ) := inferInstance
def pack (w : Weight) : Key := (w 0,w 1,w 2,w 3,w 4,w 5)
def unpack (w : Key) : Weight := ![w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2]

theorem unpack_pack (w : Weight) : unpack (pack w) = w := by
  funext i; fin_cases i <;> rfl
theorem pack_unpack (w : Key) : pack (unpack w) = w := by
  rcases w with ⟨a,b,c,d,e,f⟩; rfl
theorem unpack_zero : unpack 0 = 0 := by funext i; fin_cases i <;> rfl
theorem unpack_add (a b : Key) : unpack (a+b) = unpack a + unpack b := by
  funext i; fin_cases i <;> rfl

def weights (s : DeltaLOneSignedInput.Species) : List Key :=
  List.ofFn (fun i => pack (-SMComputableCharacter.slotWeight s i))
def tables : List (List (Terms Key)) :=
  List.ofFn (fun s : DeltaLOneSignedInput.Species => SparseWeightPolynomial.exteriorRows (weights s))
def exteriorTerms (s : DeltaLOneSignedInput.Species) (n : ℕ) : Terms Key :=
  SparseWeightPolynomial.exteriorFast (weights s) n
def sourceTerms (c : DeltaLOneSignedInput.Species → ℕ) : Terms Key :=
  SparseWeightPolynomial.product (List.ofFn (fun s => exteriorTerms s (c s)))
def bosonTerms (m : ℕ) (delta : ℤ) : Terms Key :=
  SparseWeightPolynomial.normalize
    (List.ofFn (fun j => (pack (-SMComputableCharacter.bosonWeight m delta j),1)))
def terms (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : Terms Key :=
  SparseWeightPolynomial.multiplyFast (sourceTerms c) (bosonTerms m delta)
def keyRoots : List Key := roots.map pack
def multiplicity (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : ℤ :=
  CompactWeylExtraction.constantTerm keyRoots (coefficient (terms c m delta))
def cachedTerms (cache : List (List (Terms Key))) (c : DeltaLOneSignedInput.Species → ℕ)
    (m : ℕ) (delta : ℤ) : Terms Key :=
  SparseWeightPolynomial.multiplyFast
    (SparseWeightPolynomial.product (List.ofFn (fun s => (cache.getD s.val []).getD (c s) [])))
    (bosonTerms m delta)
def cachedMultiplicity (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : ℤ :=
  CompactWeylExtraction.constantTerm keyRoots (coefficient (cachedTerms tables c m delta))

noncomputable section
def chi (t : Torus) (w : Key) : ℂ := monomial (unpack w) t
theorem chi_zero (t : Torus) : chi t 0 = 1 := by simp [chi,unpack_zero,SMComputableSlotWeights.monomial_zero]
theorem chi_add (t : Torus) (a b : Key) : chi t (a+b) = chi t a * chi t b := by
  simp only [chi,unpack_add,SMComputableSlotWeights.monomial_add]

theorem terms_evaluation_general {R : Type*} [CommRing R] (f : Weight → R)
    (h0 : f 0 = 1) (hm : ∀ a b, f (a+b) = f a * f b)
    (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    evaluate (fun k => f (unpack k)) (terms c m delta) =
      evaluate f (SMComputableCharacter.terms c m delta) := by
  let g := fun k => f (unpack k)
  have g0 : g 0 = 1 := by simpa only [g,unpack_zero] using h0
  have gm (a b : Key) : g (a+b) = g a * g b := by simp only [g,unpack_add,hm]
  have he (s : DeltaLOneSignedInput.Species) (n : ℕ) :
      evaluate g (exteriorTerms s n) = evaluate f (SMComputableCharacter.exteriorTerms s n) := by
    rw [exteriorTerms,SparseWeightPolynomial.exteriorFast_evaluation _ gm,weights,
      exterior_ofFn_evaluate _ g0 gm,SMComputableCharacter.exteriorTerms,
      exterior_ofFn_evaluate _ h0 hm]
    simp only [g,unpack_pack]
  have hs : evaluate g (sourceTerms c) = evaluate f (SMComputableCharacter.sourceTerms c) := by
    rw [sourceTerms,SparseWeightPolynomial.evaluate_product _ g0 gm,
      SMComputableCharacter.sourceTerms,evaluate_product _ h0 hm,
      List.map_ofFn,List.map_ofFn,List.prod_ofFn,List.prod_ofFn]
    exact Finset.prod_congr rfl (fun s _ => he s (c s))
  have hb : evaluate g (bosonTerms m delta) = evaluate f (SMComputableCharacter.bosonTerms m delta) := by
    rw [bosonTerms,SparseWeightPolynomial.evaluate_normalize]
    simp only [SMComputableCharacter.bosonTerms,evaluate,List.map_ofFn,List.sum_ofFn,
      Function.comp_apply,g,unpack_pack,Int.cast_one,one_mul]
  rw [terms,SparseWeightPolynomial.evaluate_multiplyFast _ gm,hs,hb]
  exact (evaluate_multiply _ hm _ _).symm

theorem terms_evaluation (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (t : Torus) :
    evaluate (chi t) (terms c m delta) =
      evaluate (fun w => monomial w t) (SMComputableCharacter.terms c m delta) :=
  terms_evaluation_general (R := ℂ) (fun w => monomial w t) (SMComputableSlotWeights.monomial_zero t)
    (fun a b => SMComputableSlotWeights.monomial_add a b t) c m delta

theorem coefficient_reference (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Weight) :
    coefficient ((terms c m delta).map (fun x => (unpack x.1,x.2))) w =
      coefficient (SMComputableCharacter.terms c m delta) w := by
  let f : Weight → AddMonoidAlgebra ℤ Weight := fun a => AddMonoidAlgebra.single a 1
  have h0 : f 0 = 1 := rfl
  have hm (a b : Weight) : f (a+b) = f a * f b := by simp [f,AddMonoidAlgebra.single_mul_single]
  have h := terms_evaluation_general f h0 hm c m delta
  have ht : evaluate f ((terms c m delta).map (fun x => (unpack x.1,x.2))) =
      evaluate (fun k => f (unpack k)) (terms c m delta) := by
    simp only [evaluate,List.map_map,Function.comp_def]
  have hc := congrArg (fun p : AddMonoidAlgebra ℤ Weight => p.coeff w) (ht.trans h)
  simpa only [f,SparseWeightPolynomial.formal_coefficient] using hc

theorem tables_lookup (s : DeltaLOneSignedInput.Species) :
    tables.getD s.val [] = SparseWeightPolynomial.exteriorRows (weights s) := by
  simp only [tables,List.getD_eq_getElem?_getD,List.getElem?_ofFn,s.isLt,dite_true,Option.getD_some]

theorem cached_evaluation_general {R : Type*} [CommRing R] (f : Weight → R)
    (h0 : f 0 = 1) (hm : ∀ a b, f (a+b) = f a * f b)
    (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    evaluate (fun k => f (unpack k)) (cachedTerms tables c m delta) =
      evaluate f (SMComputableCharacter.terms c m delta) := by
  let g := fun k => f (unpack k)
  have g0 : g 0 = 1 := by simpa only [g,unpack_zero] using h0
  have gm (a b : Key) : g (a+b) = g a * g b := by simp only [g,unpack_add,hm]
  have he (s : DeltaLOneSignedInput.Species) :
      evaluate g ((tables.getD s.val []).getD (c s) []) =
        evaluate g (exteriorTerms s (c s)) := by
    rw [tables_lookup]
    exact (SparseWeightPolynomial.exterior_evaluation g gm (weights s) (c s)).trans
      (SparseWeightPolynomial.exteriorFast_evaluation g gm (weights s) (c s)).symm
  have hs : evaluate g
      (SparseWeightPolynomial.product (List.ofFn (fun s => (tables.getD s.val []).getD (c s) []))) =
      evaluate g (sourceTerms c) := by
    rw [sourceTerms,SparseWeightPolynomial.evaluate_product _ g0 gm,
      SparseWeightPolynomial.evaluate_product _ g0 gm,
      List.map_ofFn,List.map_ofFn,List.prod_ofFn,List.prod_ofFn]
    exact Finset.prod_congr rfl (fun s _ => he s)
  calc
    _ = evaluate g (terms c m delta) := by
      rw [cachedTerms,SparseWeightPolynomial.evaluate_multiplyFast _ gm,hs]
      exact (SparseWeightPolynomial.evaluate_multiplyFast g gm _ _).symm
    _ = _ := terms_evaluation_general f h0 hm c m delta

theorem cached_coefficient (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Key) :
    coefficient (cachedTerms tables c m delta) w = coefficient (terms c m delta) w := by
  let f : Weight → AddMonoidAlgebra ℤ Key := fun a => AddMonoidAlgebra.single (pack a) 1
  have h0 : f 0 = 1 := rfl
  have hm (a b : Weight) : f (a+b) = f a * f b := by
    change AddMonoidAlgebra.single (pack a + pack b) 1 = _
    simp [f,AddMonoidAlgebra.single_mul_single]
  have h := (cached_evaluation_general f h0 hm c m delta).trans
    (terms_evaluation_general f h0 hm c m delta).symm
  simp only [f,pack_unpack] at h
  simpa only [SparseWeightPolynomial.formal_coefficient] using
    congrArg (fun p : AddMonoidAlgebra ℤ Key => p.coeff w) h

theorem cached_multiplicity (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    cachedMultiplicity c m delta = multiplicity c m delta := by
  unfold cachedMultiplicity multiplicity
  congr 1
  funext w
  exact cached_coefficient c m delta w

def polynomial (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : Weight →₀ ℤ :=
  presentation ((terms c m delta).map (fun x => (unpack x.1,x.2)))

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group :=
  borel SMCombinedCompactAction.Group
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem presents (m : ℕ) (delta : ℤ) : CompactWeylExtraction.Presents
    (SMCompactMultiplicity.model flavor p m delta) inclusion.toMonoidHom monomial
    (polynomial (SMIteratedContent.counts p) m delta) := by
  intro t
  have h := (SMComputableCharacter.terms_evaluation flavor p m delta t).symm.trans
    (terms_evaluation (SMIteratedContent.counts p) m delta t).symm
  have he := presentation_evaluate (fun w => monomial w t)
    ((terms (SMIteratedContent.counts p) m delta).map (fun x => (unpack x.1,x.2)))
  have hm : evaluate (chi t) (terms (SMIteratedContent.counts p) m delta) =
      evaluate (fun w => monomial w t)
        ((terms (SMIteratedContent.counts p) m delta).map (fun x => (unpack x.1,x.2))) := by
    simp only [evaluate,List.map_map,Function.comp_def,chi]
  exact h.trans (hm.trans he.symm)

theorem polynomial_coefficient (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Weight) :
    polynomial c m delta w = coefficient (terms c m delta) (pack w) := by
  rw [polynomial,presentation_apply]
  unfold coefficient
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro x _
  have he : unpack x.1 = w ↔ x.1 = pack w := by
    constructor
    · intro h; simpa only [pack_unpack] using congrArg pack h
    · intro h; rw [h,unpack_pack]
  simp only [he]

theorem extractAt_pack (rs : List Weight) (f : Key → ℤ) (w : Weight) :
    CompactWeylExtraction.extractAt rs (fun v => f (pack v)) w =
      CompactWeylExtraction.extractAt (rs.map pack) f (pack w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
    simp only [CompactWeylExtraction.extractAt,CompactWeylExtraction.difference,List.map_cons,ih]
    rfl

theorem extraction_eq (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    CompactWeylExtraction.constantTerm roots (polynomial c m delta) = multiplicity c m delta := by
  change CompactWeylExtraction.extractAt roots (polynomial c m delta) 0 = _
  have h : polynomial c m delta = fun w => coefficient (terms c m delta) (pack w) :=
    funext (polynomial_coefficient c m delta)
  rw [h,extractAt_pack]
  rfl

theorem polynomial_reference (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    polynomial c m delta = SMComputableCharacter.polynomial c m delta := by
  ext w
  exact (presentation_apply _ w).trans ((coefficient_reference c m delta w).trans
    (SMComputableCharacter.polynomial_coefficient c m delta w).symm)

theorem multiplicity_reference (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    multiplicity c m delta = SMComputableCharacter.multiplicity c m delta := by
  rw [← extraction_eq,polynomial_reference,SMComputableCharacter.extraction_eq]

end
end Physics.SMSparseCharacter

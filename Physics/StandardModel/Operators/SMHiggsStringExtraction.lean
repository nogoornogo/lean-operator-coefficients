import Physics.StandardModel.Operators.SMSparseCharacter
import Math.RepresentationTheory.WeightStringExtraction

/-! Cancel the Higgs weak string before forming the product polynomial. -/
namespace GUT.SMHiggsStringExtraction
set_option autoImplicit false
open Math ComputableWeightPolynomial SMSparseCharacter
open scoped BigOperators

def offset (m : ℕ) (delta : ℤ) : Key := (0,0,-(m : ℤ),0,0,3*delta)
def weak : Key := (0,0,2,0,0,0)
def colorRoots : List Key := [pack SMCompactTorus.alpha,pack SMCompactTorus.beta,
  pack (SMCompactTorus.alpha+SMCompactTorus.beta)]
def spinRoots : List Key := [pack SMCompactTorus.leftRoot,pack SMCompactTorus.rightRoot]
def reducedRoots : List Key := colorRoots ++ spinRoots

def keyMatches (a b : Key) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.1 == b.2.2.1 &&
    a.2.2.2.1 == b.2.2.2.1 && a.2.2.2.2.1 == b.2.2.2.2.1 && a.2.2.2.2.2 == b.2.2.2.2.2

/-- Skip unmatched terms without allocating a list of zero coefficients. -/
def lookup : Terms Key → Key → ℤ
  | [], _ => 0
  | x::p, w => if keyMatches x.1 w then x.2 + lookup p w else lookup p w

def a2Extract (f : Key → ℤ) : ℤ :=
  let g := CompactWeylExtraction.extractAt spinRoots f
  let a := pack SMCompactTorus.alpha
  let b := pack SMCompactTorus.beta
  g 0 - g a - g b + g (a+a+b) + g (a+b+b) - g (a+a+b+b)

def extract (source : Terms Key) (m : ℕ) (delta : ℤ) : ℤ :=
  a2Extract (fun w => lookup source (w+offset m delta) -
    lookup source (w+offset m delta+(m+1) • weak))

def multiplicityWith (cache : List (List (Terms Key)))
    (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : ℤ :=
  extract (cachedTerms cache c 0 0) m delta

def multiplicity (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : ℤ :=
  multiplicityWith tables c m delta

noncomputable section

theorem keyMatches_eq (x y : Key) : keyMatches x y = true ↔ x=y := by
  rcases x with ⟨a,b,c,d,e,f⟩
  rcases y with ⟨g,h,i,j,k,l⟩
  simp [keyMatches,Prod.mk.injEq,and_assoc]

theorem lookup_eq (p : Terms Key) (w : Key) : lookup p w = coefficient p w := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [lookup,coefficient,List.map_cons,List.sum_cons] at *
    by_cases h : x.1=w <;> simp [keyMatches_eq,h,ih]

theorem a2Extract_eq (f : Key → ℤ) :
    a2Extract f = CompactWeylExtraction.constantTerm reducedRoots f := by
  have h := CompactWeylExtraction.a2_formula (pack SMCompactTorus.alpha)
    (pack SMCompactTorus.beta) (CompactWeylExtraction.extractAt spinRoots f)
  have he : pack (SMCompactTorus.alpha+SMCompactTorus.beta) =
      pack SMCompactTorus.alpha + pack SMCompactTorus.beta := rfl
  simpa only [CompactWeylExtraction.constantTerm,reducedRoots,colorRoots,
    he,WeightStringExtraction.extractAt_append,a2Extract] using h.symm

theorem packed_reference (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Key) :
    coefficient (terms c m delta) w =
      coefficient (SMComputableCharacter.terms c m delta) (unpack w) := by
  have h := congrArg (fun P : SMCompactTorus.Weight →₀ ℤ => P (unpack w))
    (polynomial_reference c m delta)
  simpa only [polynomial_coefficient,pack_unpack,SMComputableCharacter.polynomial_coefficient] using h

theorem cached_source (c : DeltaLOneSignedInput.Species → ℕ) (w : Key) :
    coefficient (cachedTerms tables c 0 0) w =
      coefficient (SMComputableCharacter.sourceTerms c) (unpack w) := by
  rw [cached_coefficient,packed_reference,SMComputableCharacter.terms,
    WeightStringExtraction.coefficient_multiply]
  have hb : SMComputableCharacter.bosonTerms 0 0 = [(0,1)] := by decide +kernel
  rw [hb]
  simp

theorem coefficient_string (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Key) :
    coefficient (terms c m delta) w =
      WeightStringExtraction.string
        (fun v => coefficient (cachedTerms tables c 0 0) v) (offset m delta) weak m w := by
  rw [packed_reference,SMComputableCharacter.terms,WeightStringExtraction.coefficient_multiply]
  simp only [SMComputableCharacter.bosonTerms,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,one_mul,sub_neg_eq_add,WeightStringExtraction.string,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [cached_source]
  congr 1
  funext i
  fin_cases i <;> simp [unpack,offset,weak,SMComputableCharacter.bosonWeight,
    TauCeti.SU2.weight]
  ring

theorem multiplicity_eq (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    multiplicity c m delta = SMSparseCharacter.multiplicity c m delta := by
  have hf : coefficient (terms c m delta) =
      WeightStringExtraction.string (fun v => coefficient (cachedTerms tables c 0 0) v)
        (offset m delta) weak m := funext (coefficient_string c m delta)
  have hr : keyRoots = colorRoots ++ weak :: spinRoots := rfl
  rw [SMSparseCharacter.multiplicity,hf,hr,WeightStringExtraction.constantTerm_string]
  simpa only [multiplicity,multiplicityWith,extract,lookup_eq,reducedRoots] using a2Extract_eq
    (fun w => coefficient (cachedTerms tables c 0 0) (w+offset m delta) -
      coefficient (cachedTerms tables c 0 0) (w+offset m delta+(m+1) • weak))

end
end GUT.SMHiggsStringExtraction

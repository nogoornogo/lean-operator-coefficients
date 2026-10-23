import Physics.StandardModel.Operators.Support.Coordinates.SMNeutralSparseRanks
import Math.RepresentationTheory.Exterior.GroupedExteriorPolynomial
import Math.RepresentationTheory.Coefficients.BoundedExteriorCoefficient

/-! Group repeated flavor weights, retaining the original evaluator semantics. -/
namespace Physics.SMGroupedCharacter
set_option autoImplicit false
open Math ComputableWeightPolynomial SMSparseCharacter SMNeutralSparseRanks

def groups : DeltaLOneSignedInput.Species → List Key
  | 0 => [(-1, 0, -1, -1, 0, -1), (-1, 0, -1, 1, 0, -1), (-1, 0, 1, -1, 0, -1), (-1, 0, 1, 1, 0, -1), (0, -1, -1, -1, 0, -1), (0, -1, -1, 1, 0, -1), (0, -1, 1, -1, 0, -1), (0, -1, 1, 1, 0, -1), (1, 1, -1, -1, 0, -1), (1, 1, -1, 1, 0, -1), (1, 1, 1, -1, 0, -1), (1, 1, 1, 1, 0, -1)]
  | 1 => [(-1, 0, 0, 0, -1, -4), (-1, 0, 0, 0, 1, -4), (0, -1, 0, 0, -1, -4), (0, -1, 0, 0, 1, -4), (1, 1, 0, 0, -1, -4), (1, 1, 0, 0, 1, -4)]
  | 2 => [(-1, 0, 0, 0, -1, 2), (-1, 0, 0, 0, 1, 2), (0, -1, 0, 0, -1, 2), (0, -1, 0, 0, 1, 2), (1, 1, 0, 0, -1, 2), (1, 1, 0, 0, 1, 2)]
  | 3 => [(0, 0, -1, -1, 0, 3), (0, 0, -1, 1, 0, 3), (0, 0, 1, -1, 0, 3), (0, 0, 1, 1, 0, 3)]
  | 4 => [(0, 0, 0, 0, -1, 6), (0, 0, 0, 0, 1, 6)]
  | 5 => [(1, 0, 1, 0, -1, 1), (1, 0, 1, 0, 1, 1), (1, 0, -1, 0, -1, 1), (1, 0, -1, 0, 1, 1), (0, 1, 1, 0, -1, 1), (0, 1, 1, 0, 1, 1), (0, 1, -1, 0, -1, 1), (0, 1, -1, 0, 1, 1), (-1, -1, 1, 0, -1, 1), (-1, -1, 1, 0, 1, 1), (-1, -1, -1, 0, -1, 1), (-1, -1, -1, 0, 1, 1)]
  | 6 => [(1, 0, 0, -1, 0, 4), (1, 0, 0, 1, 0, 4), (0, 1, 0, -1, 0, 4), (0, 1, 0, 1, 0, 4), (-1, -1, 0, -1, 0, 4), (-1, -1, 0, 1, 0, 4)]
  | 7 => [(1, 0, 0, -1, 0, -2), (1, 0, 0, 1, 0, -2), (0, 1, 0, -1, 0, -2), (0, 1, 0, 1, 0, -2), (-1, -1, 0, -1, 0, -2), (-1, -1, 0, 1, 0, -2)]
  | 8 => [(0, 0, 1, 0, -1, -3), (0, 0, 1, 0, 1, -3), (0, 0, -1, 0, -1, -3), (0, 0, -1, 0, 1, -3)]
  | 9 => [(0, 0, 0, -1, 0, -6), (0, 0, 0, 1, 0, -6)]

theorem groups_verified (s : DeltaLOneSignedInput.Species) :
    GroupedExteriorPolynomial.slots (groups s) = SMKernelWeightData.data s := by
  fin_cases s <;> decide +kernel

def source (s : DeltaLOneSignedInput.Species) (n : ℕ) : Terms Key :=
  (GroupedExteriorPolynomial.rows n (groups s)).getD n []

def solveGrouped (r : Row) : Result :=
  let v := SMHiggsStringExtraction.extract (source r.species r.fermions) r.m r.delta
  ⟨v,columnsFast r.species r.fermions r.m - v.toNat⟩

theorem source_coefficient (s : DeltaLOneSignedInput.Species) (n : ℕ) (w : Key) :
    coefficient (source s n) w = coefficient
      (SparseWeightPolynomial.exterior (SMKernelWeightData.data s) n) w := by
  let f : Key → AddMonoidAlgebra ℤ Key := fun a => AddMonoidAlgebra.single a 1
  have hm (a b : Key) : f (a+b) = f a * f b := by
    simp [f,AddMonoidAlgebra.single_mul_single]
  have h := GroupedExteriorPolynomial.rows_evaluation f hm n (groups s) n (Nat.le_refl n)
  rw [groups_verified] at h
  have he := h.trans (SparseWeightPolynomial.exterior_evaluation f hm
    (SMKernelWeightData.data s) n).symm
  simpa only [source,f,SparseWeightPolynomial.formal_coefficient] using
    congrArg (fun p : AddMonoidAlgebra ℤ Key => p.coeff w) he

theorem solveGrouped_eq (r : Row) : solveGrouped r = solve r := by
  have hs : rowSource SMKernelWeightData.tables r =
      SparseWeightPolynomial.exterior (SMKernelWeightData.data r.species) r.fermions := by
    simp only [rowSource,SMKernelWeightData.tables,List.getD,List.getElem?_ofFn,
      r.species.isLt,dite_true,Option.getD_some,SparseWeightPolynomial.exterior]
  have he : SMHiggsStringExtraction.lookup (source r.species r.fermions) =
      SMHiggsStringExtraction.lookup (rowSource SMKernelWeightData.tables r) := by
    funext w
    simp only [SMHiggsStringExtraction.lookup_eq,hs,source_coefficient]
  have hv : SMHiggsStringExtraction.extract (source r.species r.fermions) r.m r.delta =
      SMHiggsStringExtraction.extract (rowSource SMKernelWeightData.tables r) r.m r.delta := by
    simp only [SMHiggsStringExtraction.extract,he]
  calc
    solveGrouped r = solveDirectWith SMKernelWeightData.tables r := by
      simp only [solveGrouped,solveDirectWith,hv]
    _ = solve r := solveDirectWith_data r

/-- Linear probes apply to arbitrary contents; their usefulness is algorithmic. -/
def linear (a b c d e f g : ℤ) : BoundedExteriorCoefficient.Test Key where
  toFun x := a*x.1 + b*x.2.1 + c*x.2.2.1 + d*x.2.2.2.1 +
    e*x.2.2.2.2.1 + f*x.2.2.2.2.2.1 + g*x.2.2.2.2.2.2
  map_zero' := by simp
  map_add' := by intros; dsimp; ring

def tests (s : DeltaLOneSignedInput.Species) : List (BoundedExteriorCoefficient.Test Key) :=
  let sign : ℤ := if s.val < 5 then 1 else -1
  [linear 1 (-2*sign) sign 0 0 0 0, linear 1 sign (-2*sign) 0 0 0 0, linear 1 sign sign 0 0 0 0,
    linear 1 0 0 1 0 0 0, linear 1 0 0 (-1) 0 0 0] ++
  (if s=0 ∨ s=3 then
    [linear 1 0 0 0 1 0 0, linear 1 0 0 0 (-1) 0 0, linear 0 0 0 0 0 1 0]
  else
    [linear 1 0 0 0 0 1 0, linear 1 0 0 0 0 (-1) 0, linear 0 0 0 0 1 0 0]) ++
  [linear (DeltaLOneSignedInput.hypercharge s) 0 0 0 0 0 1]

def boundedCoefficient (s : DeltaLOneSignedInput.Species) (n : ℕ) (w : Key) : ℤ :=
  BoundedExteriorCoefficient.compute (tests s) (groups s) n w

def solveBounded (r : Row) : Result :=
  let coeff := boundedCoefficient r.species r.fermions
  let v := SMHiggsStringExtraction.a2Extract (fun w =>
    coeff (w+SMHiggsStringExtraction.offset r.m r.delta) -
    coeff (w+SMHiggsStringExtraction.offset r.m r.delta+(r.m+1) • SMHiggsStringExtraction.weak))
  ⟨v,columnsFast r.species r.fermions r.m - v.toNat⟩

theorem boundedCoefficient_eq (s : DeltaLOneSignedInput.Species) (n : ℕ) (w : Key) :
    boundedCoefficient s n w = SMHiggsStringExtraction.lookup (source s n) w := by
  rw [boundedCoefficient,BoundedExteriorCoefficient.compute_eq,groups_verified,
    SMHiggsStringExtraction.lookup_eq,source_coefficient]
  let f : Key → AddMonoidAlgebra ℤ Key := fun a => AddMonoidAlgebra.single a 1
  have hm (a b : Key) : f (a+b) = f a * f b := by
    simp [f,AddMonoidAlgebra.single_mul_single]
  have he := SparseWeightPolynomial.exterior_evaluation f hm (SMKernelWeightData.data s) n
  have hc := congrArg (fun p : AddMonoidAlgebra ℤ Key => p.coeff w) he
  simpa only [f,SparseWeightPolynomial.formal_coefficient] using hc.symm

theorem solveBounded_eq (r : Row) : solveBounded r = solve r := by
  have he : boundedCoefficient r.species r.fermions =
      SMHiggsStringExtraction.lookup (source r.species r.fermions) :=
    funext (boundedCoefficient_eq r.species r.fermions)
  calc
    solveBounded r = solveGrouped r := by
      simp only [solveBounded,solveGrouped,SMHiggsStringExtraction.extract,he]
    _ = solve r := solveGrouped_eq r

end Physics.SMGroupedCharacter

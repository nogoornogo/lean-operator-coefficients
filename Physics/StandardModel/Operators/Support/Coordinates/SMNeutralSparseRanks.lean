import Physics.StandardModel.Operators.Support.Coordinates.SMSparseSupport
import Physics.StandardModel.Operators.Support.Coordinates.SMHiggsStringExtraction
import Physics.StandardModel.Operators.Support.Coordinates.SMKernelWeightData
import Physics.StandardModel.Operators.Support.Coordinates.SMConstantContentRanks

/-! Bounded neutral inputs and a conditional sound exact evaluator.
The input list records the unresolved rows of the old unconditional CSV. -/
namespace Physics.SMNeutralSparseRanks
set_option autoImplicit false
open Math Representation
structure Row where
  species : Fin 10
  fermions : ℕ
  m : ℕ
  delta : ℤ
  deriving DecidableEq, Repr
structure Result where
  multiplicity : ℤ
  rank : ℕ
  deriving DecidableEq, Repr

def counts (r : Row) (s : DeltaLOneSignedInput.Species) : ℕ :=
  if s=r.species then r.fermions else 0

def solveWith (cache : List (List (ComputableWeightPolynomial.Terms SMSparseCharacter.Key))) (r : Row) : Result :=
  let value := CompactWeylExtraction.constantTerm SMSparseCharacter.keyRoots
    (ComputableWeightPolynomial.coefficient (SMSparseCharacter.cachedTerms cache (counts r) r.m r.delta))
  ⟨value, SMConstantContentRanks.columns r.species r.fermions r.m - value.toNat⟩
def solve (r : Row) : Result := solveWith SMSparseCharacter.tables r

def columnsFast (s : DeltaLOneSignedInput.Species) (n m : ℕ) : ℕ :=
  Nat.fast_choose (SMConstantContentRanks.dimension s) n * (m+1)

theorem columnsFast_eq (s : DeltaLOneSignedInput.Species) (n m : ℕ) :
    columnsFast s n m = SMConstantContentRanks.columns s n m := by
  simp only [columnsFast,SMConstantContentRanks.columns,Nat.choose_eq_fast_choose]

def rowSource (cache : List (List (ComputableWeightPolynomial.Terms SMSparseCharacter.Key)))
    (r : Row) : ComputableWeightPolynomial.Terms SMSparseCharacter.Key :=
  (cache.getD r.species.val []).getD r.fermions []

def solveDirectWith (cache : List (List (ComputableWeightPolynomial.Terms SMSparseCharacter.Key)))
    (r : Row) : Result :=
  let value := SMHiggsStringExtraction.extract (rowSource cache r) r.m r.delta
  ⟨value, columnsFast r.species r.fermions r.m - value.toNat⟩

def inputs : List Row := [
  ⟨0,6,2,-2⟩,
  ⟨0,6,4,-2⟩,
  ⟨0,6,6,-2⟩,
  ⟨0,12,4,-4⟩,
  ⟨0,12,6,-4⟩,
  ⟨0,12,8,-4⟩,
  ⟨0,12,10,-4⟩,
  ⟨0,12,12,-4⟩,
  ⟨0,18,6,-6⟩,
  ⟨0,18,8,-6⟩,
  ⟨0,18,10,-6⟩,
  ⟨0,18,12,-6⟩,
  ⟨0,18,14,-6⟩,
  ⟨0,18,16,-6⟩,
  ⟨0,18,18,-6⟩,
  ⟨0,24,8,-8⟩,
  ⟨0,24,10,-8⟩,
  ⟨0,24,12,-8⟩,
  ⟨0,24,14,-8⟩,
  ⟨0,24,16,-8⟩,
  ⟨0,24,18,-8⟩,
  ⟨0,24,20,-8⟩,
  ⟨0,24,22,-8⟩,
  ⟨0,24,24,-8⟩,
  ⟨0,30,10,-10⟩,
  ⟨0,30,12,-10⟩,
  ⟨0,30,14,-10⟩,
  ⟨0,30,16,-10⟩,
  ⟨0,30,18,-10⟩,
  ⟨0,30,20,-10⟩,
  ⟨0,30,22,-10⟩,
  ⟨0,30,24,-10⟩,
  ⟨0,30,26,-10⟩,
  ⟨0,30,28,-10⟩,
  ⟨0,30,30,-10⟩,
  ⟨0,36,12,-12⟩,
  ⟨0,36,14,-12⟩,
  ⟨0,36,16,-12⟩,
  ⟨0,36,18,-12⟩,
  ⟨0,36,20,-12⟩,
  ⟨0,36,22,-12⟩,
  ⟨0,36,24,-12⟩,
  ⟨0,36,26,-12⟩,
  ⟨0,36,28,-12⟩,
  ⟨0,36,30,-12⟩,
  ⟨0,36,32,-12⟩,
  ⟨0,36,34,-12⟩,
  ⟨0,36,36,-12⟩,
  ⟨3,4,4,4⟩,
  ⟨3,6,6,6⟩,
  ⟨3,8,8,8⟩,
  ⟨3,10,10,10⟩,
  ⟨3,12,12,12⟩,
  ⟨5,6,2,2⟩,
  ⟨5,6,4,2⟩,
  ⟨5,6,6,2⟩,
  ⟨5,12,4,4⟩,
  ⟨5,12,6,4⟩,
  ⟨5,12,8,4⟩,
  ⟨5,12,10,4⟩,
  ⟨5,12,12,4⟩,
  ⟨5,18,6,6⟩,
  ⟨5,18,8,6⟩,
  ⟨5,18,10,6⟩,
  ⟨5,18,12,6⟩,
  ⟨5,18,14,6⟩,
  ⟨5,18,16,6⟩,
  ⟨5,18,18,6⟩,
  ⟨5,24,8,8⟩,
  ⟨5,24,10,8⟩,
  ⟨5,24,12,8⟩,
  ⟨5,24,14,8⟩,
  ⟨5,24,16,8⟩,
  ⟨5,24,18,8⟩,
  ⟨5,24,20,8⟩,
  ⟨5,24,22,8⟩,
  ⟨5,24,24,8⟩,
  ⟨5,30,10,10⟩,
  ⟨5,30,12,10⟩,
  ⟨5,30,14,10⟩,
  ⟨5,30,16,10⟩,
  ⟨5,30,18,10⟩,
  ⟨5,30,20,10⟩,
  ⟨5,30,22,10⟩,
  ⟨5,30,24,10⟩,
  ⟨5,30,26,10⟩,
  ⟨5,30,28,10⟩,
  ⟨5,30,30,10⟩,
  ⟨5,36,12,12⟩,
  ⟨5,36,14,12⟩,
  ⟨5,36,16,12⟩,
  ⟨5,36,18,12⟩,
  ⟨5,36,20,12⟩,
  ⟨5,36,22,12⟩,
  ⟨5,36,24,12⟩,
  ⟨5,36,26,12⟩,
  ⟨5,36,28,12⟩,
  ⟨5,36,30,12⟩,
  ⟨5,36,32,12⟩,
  ⟨5,36,34,12⟩,
  ⟨5,36,36,12⟩,
  ⟨8,2,2,-2⟩,
  ⟨8,4,4,-4⟩,
  ⟨8,6,6,-6⟩,
  ⟨8,8,8,-8⟩,
  ⟨8,10,10,-10⟩,
  ⟨8,12,12,-12⟩ ]
def results : List Result :=
  let cache := SMSparseCharacter.tables
  inputs.map (solveWith cache)

theorem input_count : inputs.length = 107 := by decide +kernel

def enumerateInputs : List Row :=
  (List.finRange 10).flatMap (fun s =>
    (List.range (SMConstantContentRanks.dimension s + 1)).flatMap (fun n =>
      if n=0 then [] else
      (List.range (n * SMWeakWeightBasis.doubletCount s + 1)).flatMap (fun m =>
        (List.range (m+1)).filterMap (fun t =>
          let delta := (m : ℤ)-2*(t : ℤ)
          if (SMConstantContentRanks.evaluate s n m delta).isNone then some ⟨s,n,m,delta⟩ else none))))

theorem inputs_enumerated : inputs = enumerateInputs := by decide +kernel

theorem counts_pattern (r : Row) :
    SMIteratedContent.counts (SMConstantContentRanks.pattern r.species r.fermions) = counts r := by
  funext s
  by_cases h : s=r.species <;> simp [SMIteratedContent.counts,SMConstantContentRanks.pattern,counts,h,eq_comm]

noncomputable section

theorem constant_source_row (r : Row) :
    SMSparseCharacter.cachedTerms SMSparseCharacter.tables (counts r) 0 0 =
      rowSource SMSparseCharacter.tables r := by
  have hz (s : DeltaLOneSignedInput.Species) :
      (SMSparseCharacter.tables.getD s.val []).getD 0 [] = [(0,1)] := by
    rw [SMSparseCharacter.tables_lookup]
    exact SparseWeightPolynomial.rows_zero _
  have hf : List.ofFn (fun s : DeltaLOneSignedInput.Species =>
      (SMSparseCharacter.tables.getD s.val []).getD (counts r s) []) =
      List.ofFn (fun s => if s=r.species then rowSource SMSparseCharacter.tables r else [(0,1)]) := by
    congr 1
    funext s
    by_cases h : s=r.species
    · subst s; simp [counts,rowSource]
    · simp only [counts,ite_eq_right h]
      exact hz s
  have hb : SMSparseCharacter.bosonTerms 0 0 = [(0,1)] := by decide +kernel
  rw [SMSparseCharacter.cachedTerms,hf,hb,SparseWeightPolynomial.multiplyFast_one_right]
  rcases r with ⟨s,n,m,d⟩
  fin_cases s <;> simp [SparseWeightPolynomial.product,List.ofFn_succ]

abbrev Input (r : Row) := SMCompactMultiplicity.Input LLHHKernelRank.flavor
  (SMConstantContentRanks.pattern r.species r.fermions) r.m r.delta

theorem solve_multiplicity (r : Row) :
    (solve r).multiplicity = SMSparseCharacter.multiplicity (counts r) r.m r.delta :=
  SMSparseCharacter.cached_multiplicity _ _ _

theorem solve_eq_of_value (r : Row) (v : ℤ)
    (h : SMHiggsStringExtraction.multiplicity (counts r) r.m r.delta = v) :
    solve r = ⟨v,SMConstantContentRanks.columns r.species r.fermions r.m - v.toNat⟩ := by
  have hm := (solve_multiplicity r).trans
    ((SMHiggsStringExtraction.multiplicity_eq (counts r) r.m r.delta).symm.trans h)
  unfold solve solveWith at hm ⊢
  dsimp only at hm ⊢
  rw [hm]

theorem solveDirect_eq (r : Row) : solveDirectWith SMSparseCharacter.tables r = solve r := by
  have hm : SMHiggsStringExtraction.multiplicity (counts r) r.m r.delta =
      SMHiggsStringExtraction.extract (rowSource SMSparseCharacter.tables r) r.m r.delta :=
    congrArg (fun source => SMHiggsStringExtraction.extract source r.m r.delta) (constant_source_row r)
  let v := SMHiggsStringExtraction.extract (rowSource SMSparseCharacter.tables r) r.m r.delta
  have hc := congrArg (fun cols => Result.mk v (cols-v.toNat))
    (columnsFast_eq r.species r.fermions r.m)
  exact hc.trans (solve_eq_of_value r _ hm).symm

theorem solveDirectWith_data (r : Row) : solveDirectWith SMKernelWeightData.tables r = solve r :=
  (congrArg (fun cache => solveDirectWith cache r) SMKernelWeightData.tables_verified).symm.trans
    (solveDirect_eq r)

theorem kernel_dimension (r : Row) (input : Input r) : Module.finrank ℂ
    (SMFullLocalKernel.Kernel LLHHKernelRank.flavor
      (SMConstantContentRanks.pattern r.species r.fermions) r.m r.delta) = (solve r).multiplicity.toNat := by
  have h := SMSparseSupport.kernel_dimension LLHHKernelRank.flavor _ _ _ input
  have he := (congrArg (fun c => SMSparseCharacter.multiplicity c r.m r.delta) (counts_pattern r)).trans
    (solve_multiplicity r).symm
  exact h.trans (congrArg Int.toNat he)

theorem rank_sound (r : Row) (input : Input r) :
    SMConstantContentRanks.actualRank r.species r.fermions r.m r.delta = (solve r).rank := by
  have h := SMSparseSupport.rank_formula LLHHKernelRank.flavor
    (SMConstantContentRanks.pattern r.species r.fermions) r.m r.delta input
  have hd := (SMIteratedContent.carrier_dimension LLHHKernelRank.flavor
    (SMConstantContentRanks.pattern r.species r.fermions) r.m).symm.trans
    (SMConstantContentRanks.carrier_dimension LLHHKernelRank.flavor r.species r.fermions r.m)
  have hm := (congrArg (fun c => SMSparseCharacter.multiplicity c r.m r.delta) (counts_pattern r)).trans
    (solve_multiplicity r).symm
  exact h.trans (congrArg₂ (fun a b : ℕ => a-b) hd (congrArg Int.toNat hm))

end
end Physics.SMNeutralSparseRanks

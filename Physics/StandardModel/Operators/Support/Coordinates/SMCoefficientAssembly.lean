import Physics.StandardModel.Operators.Support.Coordinates.SMGroupedCharacter

/-! Keep the coefficient function abstract while assembling checked values. -/
namespace Physics.SMCoefficientAssembly
set_option autoImplicit false
open SMNeutralSparseRanks SMSparseCharacter

def evaluate (r : Row) (f : Key → ℤ) : Result :=
  let v := SMHiggsStringExtraction.a2Extract (fun w =>
    f (w+SMHiggsStringExtraction.offset r.m r.delta) -
    f (w+SMHiggsStringExtraction.offset r.m r.delta+(r.m+1) • SMHiggsStringExtraction.weak))
  ⟨v,columnsFast r.species r.fermions r.m - v.toNat⟩

theorem factor (r : Row) : SMGroupedCharacter.solveBounded r =
    evaluate r (SMGroupedCharacter.boundedCoefficient r.species r.fermions) := rfl

end Physics.SMCoefficientAssembly

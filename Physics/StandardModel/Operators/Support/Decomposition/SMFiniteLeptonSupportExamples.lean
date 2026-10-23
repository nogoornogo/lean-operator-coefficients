import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonAssignments

/-! Importing consumers of the uniform theorem, including moduli outside
the retained 572-row domain and a counterexample to unrestricted congruences. -/
namespace Physics.SMFiniteLeptonSupportExamples
open Math SMFiniteLeptonSupport

theorem k101_b1_allowed :
    SMQLPatternRequests.OriginalAllowed (28 : ZMod 101) 1 (fun c => c.1.natAbs=3) := by
  apply (SMFiniteLeptonSupport.b1_allowed_iff _ _).mpr
  exact ⟨17, by decide +kernel, by decide +kernel⟩

theorem k101_b1_forbidden :
    SMQLPatternRequests.OriginalForbidden (10 : ZMod 101) 1 (fun c => c.1.natAbs=3) := by
  apply (SMFiniteLeptonSupport.original_forbidden_iff _ _ 3 (Or.inl rfl)).mpr
  decide +kernel

/-- An odd neutral L exists arithmetically but exceeds exterior capacity. -/
theorem unrestricted_congruence_insufficient :
    (71 : ℤ)%2=1 ∧ (3 : ZMod 101)*10 + (71 : ZMod 101)*1=0 ∧
    SMQLPatternRequests.OriginalForbidden (10 : ZMod 101) 1 (fun c => c.1.natAbs=3) := by
  exact ⟨by decide +kernel, by decide +kernel, k101_b1_forbidden⟩

theorem imported_row_request :
    SMQLPatternRequests.Satisfies (0 : ZMod 2) 1 SMQLPatternRequests.b1ForbiddenB2Allowed := by
  exact (SMFiniteLeptonAssignments.request_iff 0 ⟨2,0,1,true,false⟩
    (by decide +kernel)).mpr ⟨rfl,rfl⟩

end Physics.SMFiniteLeptonSupportExamples

import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityZeroOneThreeLaw
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch
import Omega.GU.Z6CenterQuotient

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-boundary-address-charge-strict-splitting`.
The regular `ZMod 6` boundary address torsor, the CRT splitting
`ZMod 6 ≃ ZMod 2 × ZMod 3`, and the verified three-axis boundary parity package combine into
the strict address/charge splitting statement. -/
theorem paper_conclusion_window6_boundary_address_charge_strict_splitting :
    Omega.Conclusion.boundary_uplift_is_regular_Z6_torsor ∧
      Nonempty (ZMod 2 × ZMod 3 ≃+* ZMod 6) ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      Omega.Conclusion.conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank =
        3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      Omega.Conclusion.paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch.1
  · exact Omega.GU.Z6CenterQuotient.z2_times_z3_ringEquiv_z6
  · simp [Omega.GU.Window6BoundaryParityBlock]
  · rfl

end Omega.Conclusion
